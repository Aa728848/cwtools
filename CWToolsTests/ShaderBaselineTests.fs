module ShaderBaselineTests

open System
open System.Diagnostics
open System.IO
open System.Security.Cryptography
open System.Text
open System.Text.RegularExpressions
open Expecto
open FSharp.Data
open CWTools.Games

/// Vanilla gfx/FX baseline snapshot (plan 阶段 0 / §17.7).
///
/// Runs only when CWTOOLS_STELLARIS_PATH points at a Stellaris install; otherwise the
/// test is skipped. A missing gfx/FX directory is an explicit failure: vanilla read
/// failures must fail the gate, never silently pass. The snapshot JSON is deterministic
/// (ordinal-sorted, relative paths only, no timestamps or machine-specific data). When a
/// baseline already exists the test prints a structured diff but does not fail on drift.

let private contentResource filepath logicalpath filetext : Resource =
    FileWithContentResource(
        filepath,
        { scope = "vanilla"
          filetext = filetext
          filepath = filepath
          logicalpath = logicalpath
          overwrite = Overwrite.No
          validate = true }
    )

let private ordinalSort (values: string array) =
    values |> Array.sortWith (fun left right -> String.CompareOrdinal(left, right))

let private sanitizePaths (vanillaRoot: string) (message: string) =
    let normalizedRoot = vanillaRoot.Replace('\\', '/').TrimEnd('/')
    let pattern = Regex.Escape(normalizedRoot)
    Regex.Replace(message.Replace('\\', '/'), pattern, "<vanilla>", RegexOptions.IgnoreCase)

let private jsonInt (value: int) = JsonValue.Number(decimal value)

let private sha256Hex (bytes: byte[]) =
    Convert.ToHexString(SHA256.HashData bytes).ToLowerInvariant()

type private FileFact =
    { relativePath: string
      fullPath: string
      size: int
      sha256: string
      text: string }

type private DiagnosticFact =
    { code: string
      file: string
      message: string }

let private collectFileFacts (stellarisRoot: string) =
    let fxDir = Path.Combine(stellarisRoot, "gfx", "FX")

    if not (Directory.Exists fxDir) then
        failtestf "Vanilla gfx/FX directory is missing at %s; the baseline gate must fail explicitly" fxDir

    Directory.GetFiles fxDir
    |> Array.map (fun fullPath ->
        let relativePath = Path.GetRelativePath(stellarisRoot, fullPath).Replace('\\', '/')
        let bytes = File.ReadAllBytes fullPath

        { relativePath = relativePath
          fullPath = fullPath
          size = bytes.Length
          sha256 = sha256Hex bytes
          text = File.ReadAllText(fullPath, Encoding.UTF8) })
    |> Array.sortWith (fun left right -> String.CompareOrdinal(left.relativePath, right.relativePath))

let private buildSnapshot (stellarisRoot: string) =
    let sanitize = sanitizePaths stellarisRoot
    let files = collectFileFacts stellarisRoot

    let shaderFiles =
        files |> Array.filter (fun file -> PdxShaderFeatures.isShaderFile file.fullPath)

    let snapshots =
        shaderFiles
        |> Array.map (fun file ->
            PdxShaderProject.createSnapshot PdxShaderProject.Vanilla file.fullPath file.relativePath file.text)
        |> Array.toList

    let resources =
        shaderFiles
        |> Array.map (fun file -> contentResource file.fullPath file.relativePath file.text)

    // --- Parse counts (current PdxShaderFeatures/PdxShaderProject machinery) ---
    let declarations =
        snapshots |> List.collect PdxShaderRuntime.declarationsFromSnapshot

    let countKind kind =
        declarations |> List.filter (fun declaration -> declaration.kind = kind) |> List.length

    let uniqueNames kind =
        declarations
        |> List.filter (fun declaration -> declaration.kind = kind)
        |> List.map _.name
        |> List.distinctBy (fun name -> name.ToLowerInvariant())
        |> List.length

    let uniqueDeclarationNames kind =
        declarations
        |> List.filter (fun declaration -> declaration.kind = kind)
        |> List.map (fun declaration -> declaration.name.ToLowerInvariant())
        |> Set.ofList
        |> Set.count

    let uniqueIncludeFiles =
        snapshots
        |> List.collect PdxShaderProject.extractIncludes
        |> List.map (fun includeReference -> includeReference.target.ToLowerInvariant())
        |> Set.ofList
        |> Set.count

    let includeEntries = snapshots |> List.sumBy (PdxShaderProject.extractIncludes >> List.length)

    // --- Compile-unit stats ---
    let roots =
        snapshots
        |> List.filter (fun snapshot -> snapshot.displayPath.EndsWith(".shader", StringComparison.OrdinalIgnoreCase))

    let compileUnits = roots |> List.map (PdxShaderProject.buildCompileUnit snapshots)
    let allProblems = compileUnits |> List.collect _.problems

    let countProblems predicate =
        allProblems |> List.filter predicate |> List.length

    let missingCount =
        countProblems (function
            | PdxShaderProject.MissingInclude _ -> true
            | _ -> false)

    let ambiguousCount =
        countProblems (function
            | PdxShaderProject.AmbiguousInclude _ -> true
            | _ -> false)

    let cycleCount =
        countProblems (function
            | PdxShaderProject.CyclicInclude _ -> true
            | _ -> false)

    // --- Validation per root: CWFX diagnostics ---
    let resourceSeq = resources :> Resource seq

    let diagnostics =
        roots
        |> List.collect (fun root ->
            PdxShaderFeatures.validateFromResources resourceSeq root.displayPath root.text
            |> List.map (fun error ->
                { code = error.code
                  file = root.logicalPath
                  message = sanitize error.message }))
        |> List.sortWith (fun left right ->
            match String.CompareOrdinal(left.code, right.code) with
            | 0 ->
                match String.CompareOrdinal(left.file, right.file) with
                | 0 -> String.CompareOrdinal(left.message, right.message)
                | other -> other
            | other -> other)

    let diagnosticsByCode =
        diagnostics
        |> List.countBy _.code
        |> List.sortBy fst

    // --- Snapshot JSON ---
    let filesJson =
        files
        |> Array.map (fun file ->
            JsonValue.Record
                [| "path", JsonValue.String file.relativePath
                   "size", jsonInt file.size
                   "sha256", JsonValue.String file.sha256 |])

    let diagnosticsJson =
        diagnostics
        |> List.map (fun diagnostic ->
            JsonValue.Record
                [| "code", JsonValue.String diagnostic.code
                   "file", JsonValue.String diagnostic.file
                   "message", JsonValue.String diagnostic.message |])

    let compatibilitySamplesJson =
        diagnostics
        |> List.filter (fun diagnostic -> diagnostic.code = "CWFX001")
        |> List.map (fun diagnostic ->
            JsonValue.Record
                [| "code", JsonValue.String diagnostic.code
                   "file", JsonValue.String diagnostic.file
                   "message", JsonValue.String diagnostic.message
                   "status", JsonValue.String "pending_classification" |])

    let byCodeJson =
        diagnosticsByCode
        |> List.map (fun (code, count) -> code, jsonInt count)

    let summaryJson =
        JsonValue.Record
            [| "fileCount", jsonInt files.Length
               "shaderFiles", jsonInt (files |> Array.filter (fun f -> f.relativePath.EndsWith(".shader", StringComparison.OrdinalIgnoreCase)) |> Array.length)
               "fxhFiles", jsonInt (files |> Array.filter (fun f -> f.relativePath.EndsWith(".fxh", StringComparison.OrdinalIgnoreCase)) |> Array.length)
               "totalBytes", jsonInt (files |> Array.sumBy _.size)
               "effectDeclarations", jsonInt (countKind PdxShaderRuntime.EffectDeclaration)
               "uniqueEffectNames", jsonInt (uniqueNames PdxShaderRuntime.EffectDeclaration)
               "vertexMainCodeDeclarations", jsonInt (countKind PdxShaderRuntime.VertexMainCodeDeclaration)
               "uniqueVertexMainCodeNames", jsonInt (uniqueNames PdxShaderRuntime.VertexMainCodeDeclaration)
               "pixelMainCodeDeclarations", jsonInt (countKind PdxShaderRuntime.PixelMainCodeDeclaration)
               "uniquePixelMainCodeNames", jsonInt (uniqueNames PdxShaderRuntime.PixelMainCodeDeclaration)
               "constantBufferDeclarations", jsonInt (countKind PdxShaderRuntime.ConstantBufferDeclaration)
               "uniqueConstantBufferNames", jsonInt (uniqueNames PdxShaderRuntime.ConstantBufferDeclaration)
               "blendStateDeclarations", jsonInt (countKind PdxShaderRuntime.BlendStateDeclaration)
               "depthStencilStateDeclarations", jsonInt (countKind PdxShaderRuntime.DepthStencilStateDeclaration)
               "rasterizerStateDeclarations", jsonInt (countKind PdxShaderRuntime.RasterizerStateDeclaration)
               "uniqueBlendStateNames", jsonInt (uniqueDeclarationNames PdxShaderRuntime.BlendStateDeclaration)
               "uniqueDepthStencilStateNames", jsonInt (uniqueDeclarationNames PdxShaderRuntime.DepthStencilStateDeclaration)
               "uniqueRasterizerStateNames", jsonInt (uniqueDeclarationNames PdxShaderRuntime.RasterizerStateDeclaration)
               "uniqueDefines", jsonInt (uniqueDeclarationNames PdxShaderRuntime.MacroDeclaration)
               "includeEntries", jsonInt includeEntries
               "uniqueIncludeFiles", jsonInt uniqueIncludeFiles
               "compileUnitRoots", jsonInt roots.Length
               "missingIncludes", jsonInt missingCount
               "ambiguousIncludes", jsonInt ambiguousCount
               "includeCycles", jsonInt cycleCount
               "diagnosticCount", jsonInt diagnostics.Length |]

    let snapshotJson =
        JsonValue.Record
            [| "schemaVersion", jsonInt 1
               "game", JsonValue.String "stellaris"
               "gameVersion", JsonValue.String "4.4.6"
               "sourceDirectory", JsonValue.String "gfx/FX"
               "summary", summaryJson
               "files", JsonValue.Array filesJson
               "diagnosticsByCode", JsonValue.Record(Array.ofList byCodeJson)
               "diagnostics", JsonValue.Array(Array.ofList diagnosticsJson)
               "knownCompatibilitySamples", JsonValue.Array(Array.ofList compatibilitySamplesJson) |]

    let summaryLines =
        [ sprintf "files: %d (%d .shader, %d .fxh, %d bytes)"
              files.Length
              (files |> Array.filter (fun f -> f.relativePath.EndsWith(".shader", StringComparison.OrdinalIgnoreCase)) |> Array.length)
              (files |> Array.filter (fun f -> f.relativePath.EndsWith(".fxh", StringComparison.OrdinalIgnoreCase)) |> Array.length)
              (files |> Array.sumBy _.size)
          sprintf "effects: %d declarations, %d unique names"
              (countKind PdxShaderRuntime.EffectDeclaration)
              (uniqueNames PdxShaderRuntime.EffectDeclaration)
          sprintf "maincodes: %d vertex (%d unique), %d pixel (%d unique)"
              (countKind PdxShaderRuntime.VertexMainCodeDeclaration)
              (uniqueNames PdxShaderRuntime.VertexMainCodeDeclaration)
              (countKind PdxShaderRuntime.PixelMainCodeDeclaration)
              (uniqueNames PdxShaderRuntime.PixelMainCodeDeclaration)
          sprintf "constant buffers: %d (%d unique); states: %d blend (%d unique), %d depth-stencil (%d unique), %d rasterizer (%d unique)"
              (countKind PdxShaderRuntime.ConstantBufferDeclaration)
              (uniqueNames PdxShaderRuntime.ConstantBufferDeclaration)
              (countKind PdxShaderRuntime.BlendStateDeclaration)
              (uniqueDeclarationNames PdxShaderRuntime.BlendStateDeclaration)
              (countKind PdxShaderRuntime.DepthStencilStateDeclaration)
              (uniqueDeclarationNames PdxShaderRuntime.DepthStencilStateDeclaration)
              (countKind PdxShaderRuntime.RasterizerStateDeclaration)
              (uniqueDeclarationNames PdxShaderRuntime.RasterizerStateDeclaration)
          sprintf "defines: %d unique; includes: %d entries, %d unique files"
              (uniqueDeclarationNames PdxShaderRuntime.MacroDeclaration)
              includeEntries
              uniqueIncludeFiles
          sprintf "compile units: %d roots, %d missing, %d ambiguous, %d cycles"
              roots.Length
              missingCount
              ambiguousCount
              cycleCount
          sprintf "diagnostics: %d total (%s)"
              diagnostics.Length
              (diagnosticsByCode |> List.map (fun (code, count) -> sprintf "%s=%d" code count) |> String.concat ", ") ]

    snapshotJson, files, diagnostics, summaryLines

let private diffBaseline (baselinePath: string) (snapshotJson: JsonValue) (files: FileFact[]) (diagnostics: DiagnosticFact list) =
    try
        let old = JsonValue.Parse(File.ReadAllText baselinePath)
        let mutable drift = false

        // File set diff.
        let oldFiles =
            match old.TryGetProperty "files" with
            | Some filesValue ->
                filesValue.AsArray()
                |> Array.choose (fun entry ->
                    match entry.TryGetProperty "path", entry.TryGetProperty "size", entry.TryGetProperty "sha256" with
                    | Some path, Some size, Some sha -> Some(path.AsString(), (int (size.AsInteger64()), sha.AsString()))
                    | _ -> None)
                |> Map.ofArray
            | None -> Map.empty

        let newFiles = files |> Array.map (fun file -> file.relativePath, (file.size, file.sha256)) |> Map.ofArray

        let added = newFiles |> Seq.filter (fun pair -> not (oldFiles.ContainsKey pair.Key)) |> Seq.map _.Key |> Seq.toArray |> ordinalSort
        let removed = oldFiles |> Seq.filter (fun pair -> not (newFiles.ContainsKey pair.Key)) |> Seq.map _.Key |> Seq.toArray |> ordinalSort

        let changed =
            newFiles
            |> Seq.choose (fun pair ->
                match oldFiles.TryFind pair.Key with
                | Some oldFact when oldFact <> pair.Value -> Some pair.Key
                | _ -> None)
            |> Seq.toArray
            |> ordinalSort

        if added.Length > 0 || removed.Length > 0 || changed.Length > 0 then
            drift <- true
            if added.Length > 0 then printfn "  added files: %s" (String.concat ", " added)
            if removed.Length > 0 then printfn "  removed files: %s" (String.concat ", " removed)
            if changed.Length > 0 then printfn "  changed files: %s" (String.concat ", " changed)

        // Summary count diff.
        match old.TryGetProperty "summary", snapshotJson.TryGetProperty "summary" with
        | Some oldSummary, Some newSummary ->
            for property in newSummary.Properties() do
                let name, newValue = property

                match oldSummary.TryGetProperty name with
                | Some oldValue when oldValue <> newValue ->
                    drift <- true
                    printfn "  summary %s: %s -> %s" name (oldValue.ToString()) (newValue.ToString())
                | _ -> ()
        | _ -> ()

        // Diagnostics diff.
        let diagnosticKey (code: string) (file: string) (message: string) = sprintf "%s|%s|%s" code file message

        let oldDiagnostics =
            match old.TryGetProperty "diagnostics" with
            | Some diagnosticsValue ->
                diagnosticsValue.AsArray()
                |> Array.choose (fun entry ->
                    match entry.TryGetProperty "code", entry.TryGetProperty "file", entry.TryGetProperty "message" with
                    | Some code, Some file, Some message -> Some(diagnosticKey (code.AsString()) (file.AsString()) (message.AsString()))
                    | _ -> None)
                |> Set.ofArray
            | None -> Set.empty

        let newDiagnostics =
            diagnostics
            |> List.map (fun diagnostic -> diagnosticKey diagnostic.code diagnostic.file diagnostic.message)
            |> Set.ofList

        let addedDiagnostics = Set.difference newDiagnostics oldDiagnostics
        let removedDiagnostics = Set.difference oldDiagnostics newDiagnostics

        if not addedDiagnostics.IsEmpty || not removedDiagnostics.IsEmpty then
            drift <- true
            for diagnostic in addedDiagnostics do
                printfn "  added diagnostic: %s" diagnostic
            for diagnostic in removedDiagnostics do
                printfn "  removed diagnostic: %s" diagnostic

        if not drift then
            printfn "baseline diff: no drift detected"
    with ex ->
        printfn "baseline diff: failed to compare with existing baseline (%s); keeping new snapshot" ex.Message

[<Tests>]
let vanillaShaderBaselineTests =
    testList "vanilla 4.4.6 shader baselines"
      [ testCase "gfx/FX shader baseline snapshot" (fun () ->
          let stellarisPath = Environment.GetEnvironmentVariable("CWTOOLS_STELLARIS_PATH")

          if String.IsNullOrWhiteSpace stellarisPath then
              Tests.skiptest "CWTOOLS_STELLARIS_PATH is not set; skipping vanilla shader baseline"

          let stopwatch = Stopwatch.StartNew()
          let snapshotJson, files, diagnostics, summaryLines =
              buildSnapshot stellarisPath
          stopwatch.Stop()

          let baselineDir = Path.Combine(__SOURCE_DIRECTORY__, "ShaderBaseline")
          Directory.CreateDirectory baselineDir |> ignore
          let baselinePath = Path.Combine(baselineDir, "vanilla-4.4.6.json")

          printfn "vanilla shader baseline (%s):" (stopwatch.Elapsed.ToString())
          for line in summaryLines do
              printfn "  %s" line

          if File.Exists baselinePath then
              diffBaseline baselinePath snapshotJson files diagnostics

          let jsonText = snapshotJson.ToString(JsonSaveOptions.None) + "\n"
          File.WriteAllText(baselinePath, jsonText, Encoding.UTF8)
          printfn "baseline snapshot written to %s" baselinePath)

        testCase "interface sprite shader graph smoke" (fun () ->
          let stellarisPath = Environment.GetEnvironmentVariable("CWTOOLS_STELLARIS_PATH")

          if String.IsNullOrWhiteSpace stellarisPath then
              Tests.skiptest "CWTOOLS_STELLARIS_PATH is not set; skipping vanilla interface shader graph"

          let interfaceDir = Path.Combine(stellarisPath, "interface")
          if not (Directory.Exists interfaceDir) then
              failtestf "Vanilla interface directory is missing at %s" interfaceDir

          let interfaceResources =
              Directory.GetFiles(interfaceDir, "*.*", SearchOption.AllDirectories)
              |> Array.filter (fun filepath ->
                  filepath.EndsWith(".gfx", StringComparison.OrdinalIgnoreCase)
                  || filepath.EndsWith(".gui", StringComparison.OrdinalIgnoreCase))
              |> Array.map (fun filepath ->
                  let logicalPath = Path.GetRelativePath(stellarisPath, filepath).Replace('\\', '/')
                  contentResource filepath logicalPath (File.ReadAllText(filepath, Encoding.UTF8)))

          let shaderResources =
              collectFileFacts stellarisPath
              |> Array.filter (fun file -> PdxShaderFeatures.isShaderFile file.fullPath)
              |> Array.map (fun file -> contentResource file.fullPath file.relativePath file.text)

          let model =
              Seq.append shaderResources interfaceResources
              |> fun resources -> PdxShaderRuntime.buildModel (Some "4.4.6") resources []

          Expect.isGreaterThan model.interfaceSprites.Length 1000 "Vanilla interface effectFile sprites must be modeled"
          Expect.isGreaterThan model.guiSpriteUses.Length 1000 "Vanilla static GUI sprite uses must be modeled"
          Expect.isTrue
              (model.interfaceSprites |> List.forall (fun invocation -> invocation.rendererSubtype <> ""))
              "every modeled interface invocation has a renderer subtype"
          Expect.isTrue
              (model.guiSpriteUses |> List.forall (fun guiUse -> guiUse.spriteName.StartsWith("GFX_", StringComparison.OrdinalIgnoreCase)))
              "dynamic GUI expressions are not fabricated as concrete sprite uses") ]
