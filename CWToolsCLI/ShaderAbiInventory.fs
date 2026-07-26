namespace CWToolsCLI

open System
open System.IO
open System.Security.Cryptography
open System.Text
open System.Text.Json
open System.Text.RegularExpressions
open CWTools.Games

/// Authoritative, deterministic Stellaris Shader ABI candidate inventory.
/// Parsing is delegated to PdxShaderRuntime; this command never promotes ABI entries.
module ShaderAbiInventory =
    type private FileFact =
        { relativePath: string
          fullPath: string
          size: int64
          sha256: string
          text: string }

    type private EffectFact =
        { logicalPath: string
          name: string
          startLine: int
          startColumn: int }

    let private sha256Hex (bytes: byte[]) =
        Convert.ToHexString(SHA256.HashData bytes).ToLowerInvariant()

    let private sha256Text (value: string) =
        value |> Encoding.UTF8.GetBytes |> sha256Hex

    let private normalizePath (value: string) = value.Replace('\\', '/').TrimStart('/')

    let private launcherVersion (gamePath: string) =
        let launcherPath = Path.Combine(gamePath, "launcher-settings.json")

        if not (File.Exists launcherPath) then
            None
        else
            let text = File.ReadAllText(launcherPath, Encoding.UTF8)
            let matched = Regex.Match(text, "\"rawVersion\"\\s*:\\s*\"v?([^\"]+)\"", RegexOptions.IgnoreCase)
            if matched.Success then Some matched.Groups[1].Value else None

    let private collectFiles (gamePath: string) =
        let fxPath = Path.Combine(gamePath, "gfx", "FX")

        if not (Directory.Exists fxPath) then
            invalidArg "directory" (sprintf "Stellaris gfx/FX directory does not exist: %s" fxPath)

        Directory.EnumerateFiles(fxPath, "*", SearchOption.AllDirectories)
        |> Seq.filter PdxShaderFeatures.isShaderFile
        |> Seq.map (fun fullPath ->
            let bytes = File.ReadAllBytes fullPath
            { relativePath = Path.GetRelativePath(gamePath, fullPath) |> normalizePath
              fullPath = fullPath
              size = int64 bytes.Length
              sha256 = sha256Hex bytes
              text = Encoding.UTF8.GetString bytes })
        |> Seq.sortWith (fun left right -> String.CompareOrdinal(left.relativePath, right.relativePath))
        |> Seq.toArray

    let private collectEffects (files: FileFact array) =
        files
        |> Array.collect (fun file ->
            let snapshot =
                PdxShaderProject.createSnapshot
                    PdxShaderProject.Vanilla
                    file.fullPath
                    file.relativePath
                    file.text

            PdxShaderRuntime.declarationsFromSnapshot snapshot
            |> List.filter (fun declaration -> declaration.kind = PdxShaderRuntime.EffectDeclaration)
            |> List.map (fun declaration ->
                { logicalPath = normalizePath declaration.logicalPath
                  name = declaration.name
                  startLine = int declaration.selectionRange.StartLine
                  startColumn = int declaration.selectionRange.StartColumn })
            |> List.toArray)
        |> Array.sortWith (fun left right ->
            let pathOrder = String.CompareOrdinal(left.logicalPath, right.logicalPath)
            if pathOrder <> 0 then pathOrder
            else
                let lineOrder = compare left.startLine right.startLine
                if lineOrder <> 0 then lineOrder
                else
                    let columnOrder = compare left.startColumn right.startColumn
                    if columnOrder <> 0 then columnOrder else String.CompareOrdinal(left.name, right.name))

    let private uniqueEffectNames (effects: EffectFact array) =
        let seen = Collections.Generic.HashSet<string>(StringComparer.OrdinalIgnoreCase)

        effects
        |> Array.choose (fun effect -> if seen.Add effect.name then Some effect.name else None)
        |> Array.sortWith (fun left right -> String.CompareOrdinal(left, right))

    let private containsBytes (haystack: byte[]) (needle: byte[]) =
        needle.Length > 0 && haystack.AsSpan().IndexOf(needle.AsSpan()) >= 0

    let private executableHits (executableBytes: byte[]) (effectNames: string array) =
        let ascii =
            effectNames
            |> Array.filter (fun name -> name |> Seq.forall (fun character -> int character <= 0x7f))
            |> Array.filter (fun name -> containsBytes executableBytes (Encoding.ASCII.GetBytes name))

        let utf16 =
            effectNames
            |> Array.filter (fun name -> containsBytes executableBytes (Encoding.Unicode.GetBytes name))

        ascii, utf16

    let private writeStringArray (writer: Utf8JsonWriter) (name: string) (values: string array) =
        writer.WriteStartArray name
        for value in values do writer.WriteStringValue value
        writer.WriteEndArray()

    let private writeOutput
        (outputPath: string)
        (gameVersion: string)
        (files: FileFact array)
        (effects: EffectFact array)
        (inventoryHash: string)
        (declarationHash: string)
        (launcherRawVersion: string)
        (launcherHash: string)
        (executableSize: int64)
        (executableHash: string)
        (asciiHits: string array)
        (utf16Hits: string array)
        =
        let directory = Path.GetDirectoryName outputPath
        if not (String.IsNullOrWhiteSpace directory) then Directory.CreateDirectory directory |> ignore

        use stream = File.Create outputPath
        use writer = new Utf8JsonWriter(stream, JsonWriterOptions(Indented = true))
        writer.WriteStartObject()
        writer.WriteString("_schema", "cwtools/shader-abi-inventory/v1")
        writer.WriteString("game", "stellaris")
        writer.WriteString("game_version", gameVersion)
        writer.WriteString("source_directory", "gfx/FX")

        writer.WriteStartObject("candidate_universe")
        writer.WriteNumber("source_files", files.Length)
        writer.WriteNumber("shader_files", files |> Array.filter (fun file -> file.relativePath.EndsWith(".shader", StringComparison.OrdinalIgnoreCase)) |> Array.length)
        writer.WriteNumber("fxh_files", files |> Array.filter (fun file -> file.relativePath.EndsWith(".fxh", StringComparison.OrdinalIgnoreCase)) |> Array.length)
        writer.WriteNumber("effect_declarations", effects.Length)
        writer.WriteNumber("unique_effect_names", uniqueEffectNames effects |> Array.length)
        writer.WriteString("inventory_sha256", inventoryHash)
        writer.WriteString("inventory_hash_algorithm", "sha256 of UTF-8 ordinal path|size|file_sha256 rows joined by LF without a trailing LF")
        writer.WriteString("declaration_inventory_sha256", declarationHash)
        writer.WriteString("declaration_hash_algorithm", "sha256 of UTF-8 ordinal lowercase_logical_path|effect_name|selection_start_line|selection_start_column rows joined by LF without a trailing LF")
        writer.WriteEndObject()

        writer.WriteStartObject("game_identity")
        writer.WriteString("launcher_raw_version", launcherRawVersion)
        writer.WriteString("launcher_settings_sha256", launcherHash)
        writer.WriteString("executable", "stellaris.exe")
        writer.WriteNumber("executable_size", executableSize)
        writer.WriteString("executable_sha256", executableHash)
        writer.WriteEndObject()

        writer.WriteStartObject("executable_string_scan")
        writer.WriteString("policy", "String presence is candidate evidence only and never proves a call path.")
        writer.WriteNumber("ascii_hits", asciiHits.Length)
        writeStringArray writer "ascii_effect_names" asciiHits
        writer.WriteNumber("utf16le_hits", utf16Hits.Length)
        writeStringArray writer "utf16le_effect_names" utf16Hits
        writer.WriteEndObject()

        writer.WriteStartArray("files")
        for file in files do
            writer.WriteStartObject()
            writer.WriteString("path", file.relativePath)
            writer.WriteNumber("size", file.size)
            writer.WriteString("sha256", file.sha256)
            writer.WriteEndObject()
        writer.WriteEndArray()

        writer.WriteStartArray("effects")
        for effect in effects do
            writer.WriteStartObject()
            writer.WriteString("shader_file", effect.logicalPath)
            writer.WriteString("name", effect.name)
            writer.WriteNumber("selection_start_line", effect.startLine)
            writer.WriteNumber("selection_start_column", effect.startColumn)
            writer.WriteEndObject()
        writer.WriteEndArray()

        writer.WriteEndObject()
        writer.Flush()

    let run (gamePath: string) (suppliedVersion: string option) (outputPath: string) =
        let gamePath = Path.GetFullPath gamePath
        let outputPath = Path.GetFullPath outputPath

        if not (Directory.Exists gamePath) then
            invalidArg "directory" (sprintf "Stellaris directory does not exist: %s" gamePath)

        let detectedVersion = launcherVersion gamePath
        let gameVersion =
            match suppliedVersion, detectedVersion with
            | Some supplied, _ when not (String.IsNullOrWhiteSpace supplied) && supplied <> "local" -> supplied.TrimStart([| 'v'; 'V' |])
            | _, Some detected -> detected.TrimStart([| 'v'; 'V' |])
            | _ -> invalidArg "game-version" "No game version was supplied and launcher-settings.json has no rawVersion."

        let launcherPath = Path.Combine(gamePath, "launcher-settings.json")
        if not (File.Exists launcherPath) then invalidArg "directory" (sprintf "Missing launcher-settings.json: %s" launcherPath)

        let executablePath = Path.Combine(gamePath, "stellaris.exe")
        if not (File.Exists executablePath) then invalidArg "directory" (sprintf "Missing stellaris.exe: %s" executablePath)

        let files = collectFiles gamePath
        let effects = collectEffects files
        let effectNames = uniqueEffectNames effects
        let executableBytes = File.ReadAllBytes executablePath
        let asciiHits, utf16Hits = executableHits executableBytes effectNames

        let inventoryRows =
            files |> Array.map (fun file -> sprintf "%s|%d|%s" file.relativePath file.size file.sha256)

        let declarationRows =
            effects
            |> Array.map (fun effect ->
                sprintf
                    "%s|%s|%d|%d"
                    (effect.logicalPath.ToLowerInvariant())
                    effect.name
                    effect.startLine
                    effect.startColumn)

        let launcherBytes = File.ReadAllBytes launcherPath
        let launcherRawVersion = detectedVersion |> Option.map (fun value -> "v" + value.TrimStart([| 'v'; 'V' |])) |> Option.defaultValue ("v" + gameVersion)

        writeOutput
            outputPath
            gameVersion
            files
            effects
            (inventoryRows |> String.concat "\n" |> sha256Text)
            (declarationRows |> String.concat "\n" |> sha256Text)
            launcherRawVersion
            (sha256Hex launcherBytes)
            (int64 executableBytes.Length)
            (sha256Hex executableBytes)
            asciiHits
            utf16Hits

        printfn "Shader ABI inventory: %s" outputPath
        printfn "Stellaris %s: %d files, %d Effect declarations, %d unique Effect names" gameVersion files.Length effects.Length effectNames.Length
        printfn "EXE candidate strings: %d ASCII, %d UTF-16LE" asciiHits.Length utf16Hits.Length
