namespace CWTools.Games

open System
open System.IO
open CWTools.Common
open CWTools.Utilities.Position

/// Language-service façade for the Paradox FX shader DSL and embedded/raw HLSL.
/// Every V2 feature below consumes PdxShaderProject.semanticSnapshot so diagnostics,
/// navigation, tokens, formatting and signature help share one lossless frontend.
module PdxShaderFeatures =
    type ShaderSource =
        { filepath: string
          logicalpath: string
          filetext: string }

    type ShaderDocumentSymbolKind =
        | IncludesSymbol
        | IncludeFileSymbol
        | VertexStructSymbol
        | ConstantBufferSymbol
        | ShaderBlockSymbol
        | MainCodeSymbol
        | CodeBlockSymbol
        | EffectSymbol
        | BlendStateSymbol
        | DepthStencilStateSymbol
        | RasterizerStateSymbol
        | SamplersSymbol
        | SamplerSymbol

    type ShaderDocumentSymbol =
        { name: string
          detail: string
          kind: ShaderDocumentSymbolKind
          range: range
          selectionRange: range
          children: ShaderDocumentSymbol list }

    type ShaderDocumentLink =
        { range: range
          targetFilepath: string }

    let isShaderFile = PdxShaderProject.isShaderFile

    /// Lazily-loaded FX sources from the vanilla game installation.
    /// Populated once via `loadVanillaFxSources` when the game starts up.
    let mutable private vanillaFxSources: ShaderSource list = []

    /// Scan a vanilla game directory for .shader/.fxh files and cache their
    /// contents.  Scans gfx/FX first, then the entire gfx tree.
    let loadVanillaFxSources (vanillaPath: string) =
        try
            let candidates =
                [| Path.Combine(vanillaPath, "gfx", "FX")
                   Path.Combine(vanillaPath, "gfx") |]
            let scanDir dir =
                if Directory.Exists dir then
                    Directory.GetFiles(dir, "*", SearchOption.AllDirectories)
                    |> Array.filter isShaderFile
                else
                    [||]
            let allFiles =
                candidates
                |> Array.collect scanDir
                |> Array.distinct
            let mutable failures = 0
            vanillaFxSources <-
                allFiles
                |> Array.choose (fun fp ->
                    try
                        Some
                            { filepath = fp
                              logicalpath = fp
                              filetext = File.ReadAllText fp }
                    with _ ->
                        failures <- failures + 1
                        None)
                |> Array.toList
            vanillaFxSources
            |> List.map (fun (source: ShaderSource) ->
                PdxShaderRuntime.createScriptSource source.filepath source.logicalpath "vanilla" source.filetext)
            |> PdxShaderRuntime.setVanillaShaderSources
            if failures > 0 then
                CWTools.Utilities.Utils.logWarning (
                    sprintf "PdxShaderFeatures: failed to read %d of %d vanilla FX files under %s" failures allFiles.Length vanillaPath
                )
        with ex ->
            CWTools.Utilities.Utils.logWarning (
                sprintf "PdxShaderFeatures: failed to scan vanilla FX files under %s: %s" vanillaPath ex.Message
            )

    /// Read-only view of the cached vanilla FX sources, used by PdxShaderRuntime
    /// so the reachability model sees the same vanilla shaders as validation.
    let vanillaShaderSources () = vanillaFxSources

    let private fileName (path: string) =
        let normalized = path.Replace('\\', '/')
        let lastSlash = normalized.LastIndexOf('/')
        if lastSlash >= 0 then normalized.Substring(lastSlash + 1) else normalized

    /// Bounded (last-write-time, length) -> text cache for FileResource shader files.
    /// Unchanged files skip the disk read and the downstream content hash entirely;
    /// this is the per-request cost the semantic LRU cannot avoid. Cleared wholesale
    /// above the limit instead of maintaining an eviction order.
    let private fileTextCache =
        System.Collections.Concurrent.ConcurrentDictionary<string, struct (System.DateTime * int64 * string)>()

    let private fileTextCacheLimit = 2048

    let private readShaderFileText (filepath: string) =
        let info = System.IO.FileInfo(filepath)

        if not info.Exists then
            fileTextCache.TryRemove filepath |> ignore
            None
        else
            match fileTextCache.TryGetValue filepath with
            | true, struct (lastWrite, length, text) when lastWrite = info.LastWriteTimeUtc && length = info.Length ->
                Some text
            | _ ->
                if fileTextCache.Count > fileTextCacheLimit then
                    fileTextCache.Clear()

                let text = File.ReadAllText filepath
                fileTextCache[filepath] <- struct (info.LastWriteTimeUtc, info.Length, text)
                Some text

    /// Unified snapshot collection for every language-service feature. A content-bearing
    /// resource always wins over a FileResource
    /// disk read of the same file; a failed read is logged and skipped. Returns all
    /// snapshots (resources in enumeration order, then the current document, then
    /// vanilla) plus the current-document snapshot.
    let private collectSnapshots (resources: Resource seq) filepath filetext =
        let materialized = Seq.toList resources
        let currentCanonical = PdxShaderProject.canonicalizePath filepath

        let contentSnapshots, currentLogicalPath =
            (([], None), materialized)
            ||> List.fold (fun (snapshots, currentLogical) resource ->
                match resource with
                | FileWithContentResource(_, resource) when
                    resource.overwrite <> Overwrite.Overwritten
                    && isShaderFile resource.filepath
                    ->
                    let canonical = PdxShaderProject.canonicalizePath resource.filepath

                    if canonical = currentCanonical then
                        // The unsaved document replaces the on-disk copy.
                        snapshots, Some resource.logicalpath
                    else
                        PdxShaderProject.createSnapshot
                            (PdxShaderProject.originForResource resource.scope resource.filepath)
                            resource.filepath
                            resource.logicalpath
                            resource.filetext
                        :: snapshots,
                        currentLogical
                | _ -> snapshots, currentLogical)

        let contentPaths =
            System.Collections.Generic.HashSet<string>(
                seq {
                    yield currentCanonical

                    for snapshot in contentSnapshots do
                        yield snapshot.canonicalPath
                },
                StringComparer.Ordinal)

        let fileSnapshots =
            materialized
            |> List.choose (function
                | FileResource(_, resource) when isShaderFile resource.filepath ->
                    let canonical = PdxShaderProject.canonicalizePath resource.filepath

                    if contentPaths.Contains canonical then
                        None
                    elif File.Exists resource.filepath then
                        try
                            match readShaderFileText resource.filepath with
                            | Some filetext ->
                                Some(
                                    PdxShaderProject.createSnapshot
                                        (PdxShaderProject.originForResource resource.scope resource.filepath)
                                        resource.filepath
                                        resource.logicalpath
                                        filetext
                                )
                            | None -> None
                        with ex ->
                            CWTools.Utilities.Utils.logWarning (
                                sprintf "PdxShaderFeatures: failed to read shader file %s: %s" resource.filepath ex.Message
                            )

                            None
                    else
                        None
                | _ -> None)

        let vanillaSnapshots =
            vanillaFxSources
            |> List.choose (fun source ->
                if PdxShaderProject.canonicalizePath source.filepath = currentCanonical then
                    None
                else
                    Some(PdxShaderProject.createSnapshot PdxShaderProject.Vanilla source.filepath source.logicalpath source.filetext))

        let current =
            PdxShaderProject.createSnapshot
                PdxShaderProject.CurrentDocument
                filepath
                (defaultArg currentLogicalPath filepath)
                filetext

        (List.rev contentSnapshots) @ fileSnapshots @ [ current ] @ vanillaSnapshots, current

    let private snapshotIncludeNames (snapshots: PdxShaderProject.ShaderSnapshot list) =
        snapshots |> List.map (fun snapshot -> fileName snapshot.displayPath) |> Set.ofList

    let private rangeBetweenOffsets filepath (text: string) startOffset endOffset =
        mkRange filepath (PdxShaderProject.posFromOffset text startOffset) (PdxShaderProject.posFromOffset text endOffset)

    let private rangeFromOffset filepath (text: string) offset length =
        rangeBetweenOffsets filepath text offset (offset + max 1 length)

    let documentSymbols (filepath: string) (filetext: string) =
        let tree = PdxShaderSyntax.parse filepath filetext

        let rec convert (node: PdxShaderSyntax.ShaderSyntaxNode) =
            let mapped =
                match node.kind with
                | PdxShaderSyntax.ShaderNodeKind.Includes -> Some(IncludesSymbol, "Includes", "Include files")
                | PdxShaderSyntax.ShaderNodeKind.IncludeFile -> Some(IncludeFileSymbol, defaultArg node.name "include", "FX include")
                | PdxShaderSyntax.ShaderNodeKind.VertexStruct -> Some(VertexStructSymbol, defaultArg node.name "VertexStruct", "Vertex struct")
                | PdxShaderSyntax.ShaderNodeKind.ConstantBuffer -> Some(ConstantBufferSymbol, defaultArg node.name "ConstantBuffer", "ConstantBuffer")
                | PdxShaderSyntax.ShaderNodeKind.VertexShader -> Some(ShaderBlockSymbol, "VertexShader", "Vertex shader block")
                | PdxShaderSyntax.ShaderNodeKind.PixelShader -> Some(ShaderBlockSymbol, "PixelShader", "Pixel shader block")
                | PdxShaderSyntax.ShaderNodeKind.GeometryShader -> Some(ShaderBlockSymbol, "GeometryShader", "Geometry shader block")
                | PdxShaderSyntax.ShaderNodeKind.MainCode -> Some(MainCodeSymbol, defaultArg node.name "MainCode", "Shader entry point")
                | PdxShaderSyntax.ShaderNodeKind.HlslRegion -> Some(CodeBlockSymbol, "Code", "Embedded HLSL/Cg")
                | PdxShaderSyntax.ShaderNodeKind.Effect -> Some(EffectSymbol, defaultArg node.name "Effect", "Effect")
                | PdxShaderSyntax.ShaderNodeKind.BlendState -> Some(BlendStateSymbol, defaultArg node.name "BlendState", "BlendState")
                | PdxShaderSyntax.ShaderNodeKind.DepthStencilState -> Some(DepthStencilStateSymbol, defaultArg node.name "DepthStencilState", "DepthStencilState")
                | PdxShaderSyntax.ShaderNodeKind.RasterizerState -> Some(RasterizerStateSymbol, defaultArg node.name "RasterizerState", "RasterizerState")
                | PdxShaderSyntax.ShaderNodeKind.Samplers -> Some(SamplersSymbol, "Samplers", "Sampler list")
                | PdxShaderSyntax.ShaderNodeKind.Sampler -> Some(SamplerSymbol, defaultArg node.name "Sampler", "Sampler")
                | _ -> None

            match mapped with
            | None -> None
            | Some(kind, name, detail) ->
                let selection = node.nameSpan |> Option.defaultValue node.span
                let children = node.children |> List.choose convert

                Some
                    { name = name
                      detail = detail
                      kind = kind
                      range = rangeBetweenOffsets filepath filetext node.span.startOffset node.span.endOffset
                      selectionRange = rangeBetweenOffsets filepath filetext selection.startOffset selection.endOffset
                      children = children }

        tree.root.children
        |> List.choose convert
        |> List.sortBy (fun item -> item.range.StartLine, item.range.StartColumn)

    /// Resolve only unambiguous Includes from the current compile-unit snapshot.
    /// Missing or ambiguous includes intentionally produce no fabricated link.
    let documentLinks (resources: Resource seq) (filepath: string) (filetext: string) =
        let snapshots, current = collectSnapshots resources filepath filetext

        PdxShaderProject.extractIncludes current
        |> List.choose (fun includeEntry ->
            match PdxShaderProject.resolveInclude snapshots current includeEntry.target with
            | PdxShaderProject.Resolved(best :: _) ->
                Some
                    { range = rangeFromOffset filepath filetext includeEntry.start includeEntry.length
                      targetFilepath = best.displayPath }
            | _ -> None)


    let private includeProblemError filepath filetext message start length =
        { code = "CWFX004"
          severity = Severity.Warning
          range = rangeFromOffset filepath filetext start length
          keyLength = max 1 length
          message = message
          data = None
          relatedErrors = None }

    let private frontendErrors (snapshot: PdxShaderProject.ShaderSnapshot) =
        let parsed = PdxShaderProject.semanticSnapshot snapshot

        let syntaxErrors =
            parsed.syntax.diagnostics
            |> List.map (fun diagnostic ->
                { code =
                    match diagnostic.kind with
                    | PdxShaderSyntax.UnterminatedString -> "CWFX101"
                    | PdxShaderSyntax.UnterminatedComment -> "CWFX102"
                    | PdxShaderSyntax.UnterminatedBlock
                    | PdxShaderSyntax.UnterminatedHlslRegion -> "CWFX103"
                    | PdxShaderSyntax.UnexpectedClosingDelimiter
                    | PdxShaderSyntax.MissingName -> "CWFX104"
                  severity = Severity.Error
                  range = rangeFromOffset snapshot.displayPath snapshot.text diagnostic.span.startOffset (max 1 diagnostic.span.Length)
                  keyLength = max 1 diagnostic.span.Length
                  message = diagnostic.message
                  data = None
                  relatedErrors = None })

        let preprocessorErrors =
            parsed.preprocessor.diagnostics
            |> List.map (fun diagnostic ->
                { code = diagnostic.code
                  severity = Severity.Error
                  range = rangeFromOffset snapshot.displayPath snapshot.text diagnostic.span.startOffset (max 1 diagnostic.span.Length)
                  keyLength = max 1 diagnostic.span.Length
                  message = diagnostic.message
                  data = None
                  relatedErrors = None })

        let hlslErrors =
            parsed.hlsl.diagnostics
            |> List.map (fun diagnostic ->
                { code = diagnostic.code
                  severity = Severity.Warning
                  range = rangeFromOffset snapshot.displayPath snapshot.text diagnostic.span.startOffset (max 1 diagnostic.span.Length)
                  keyLength = max 1 diagnostic.span.Length
                  message = diagnostic.message
                  data = None
                  relatedErrors = None })

        syntaxErrors @ preprocessorErrors @ hlslErrors

    /// V2 validation: symbols come only from the current document's compile unit
    /// (current document plus transitive Includes, effective origin per logical path).
    /// Include references are checked against the include graph: missing and ambiguous
    /// includes and cycles report CWFX004.
    let private validateFromResourcesV2 (resources: Resource seq) filepath filetext =
        let snapshots, current = collectSnapshots resources filepath filetext
        let unit = PdxShaderProject.buildCompileUnit snapshots current

        let referenceErrors =
            let declarations = unit.effective |> List.collect PdxShaderRuntime.declarationsFromSnapshot
            let references = unit.effective |> List.collect PdxShaderRuntime.semanticReferencesFromSnapshot
            PdxShaderRuntime.resolveSemanticReferences unit.effective declarations references
            |> List.filter (fun reference -> PdxShaderProject.sameFilePath reference.file filepath)
            |> List.filter (fun reference -> reference.targetIds.IsEmpty)
            |> List.choose (fun reference ->
                let diagnostic =
                    match reference.kind with
                    | PdxShaderRuntime.EffectUsesVertexMainCode ->
                        Some("CWFX001", sprintf "Effect references undefined Vertex MainCode \"%s\"" reference.targetName)
                    | PdxShaderRuntime.EffectUsesPixelMainCode ->
                        Some("CWFX001", sprintf "Effect references undefined Pixel MainCode \"%s\"" reference.targetName)
                    | PdxShaderRuntime.EffectUsesGeometryMainCode ->
                        Some("CWFX001", sprintf "Effect references undefined Geometry MainCode \"%s\"" reference.targetName)
                    | PdxShaderRuntime.EffectUsesRenderState ->
                        Some("CWFX003", sprintf "Effect references undefined render state \"%s\"" reference.targetName)
                    | PdxShaderRuntime.MainCodeUsesConstantBuffer ->
                        Some("CWFX002", sprintf "MainCode references undefined ConstantBuffer \"%s\"" reference.targetName)
                    | _ -> None
                diagnostic
                |> Option.map (fun (code, message) ->
                    { code = code
                      severity = Severity.Warning
                      range = reference.span
                      keyLength = max 1 (int reference.span.EndColumn - int reference.span.StartColumn)
                      message = message
                      data = None
                      relatedErrors = None }))

        let isCurrentFile path = PdxShaderProject.sameFilePath path filepath

        let directIncludeErrors =
            unit.problems
            |> List.choose (fun problem ->
                match problem with
                | PdxShaderProject.MissingInclude(includingPath, target, start, length) when isCurrentFile includingPath ->
                    Some(includeProblemError filepath filetext (sprintf "Include file \"%s\" is not loaded" target) start length)
                | PdxShaderProject.AmbiguousInclude(includingPath, target, start, length, candidates) when isCurrentFile includingPath ->
                    Some(
                        includeProblemError
                            filepath
                            filetext
                            (sprintf "Include file \"%s\" is ambiguous (%d candidates: %s)" target candidates.Length (String.concat ", " candidates))
                            start
                            length
                    )
                | PdxShaderProject.CyclicInclude(includingPath, _, start, length, cyclePath) when isCurrentFile includingPath ->
                    Some(
                        includeProblemError
                            filepath
                            filetext
                            (sprintf "Include cycle detected: %s" (String.concat " -> " cyclePath))
                            start
                            length
                    )
                | PdxShaderProject.IncludeBudgetExceeded(includingPath, target, start, length, budget, limit) when isCurrentFile includingPath ->
                    Some(
                        includeProblemError
                            filepath
                            filetext
                            (sprintf "Include %s budget exceeded while resolving \"%s\" (limit %d)" budget target limit)
                            start
                            length
                    )
                | _ -> None)

        // A cycle whose edge starts in another file still involves the current document;
        // report it once on the current file's first include reference.
        let participatingCycleErrors =
            let cycles =
                unit.problems
                |> List.choose (function
                    | PdxShaderProject.CyclicInclude(includingPath, _, _, _, cyclePath) when
                        not (isCurrentFile includingPath)
                        && (cyclePath |> List.exists isCurrentFile)
                        ->
                        Some cyclePath
                    | _ -> None)
                |> List.distinct

            match cycles, PdxShaderProject.extractIncludes current |> List.tryHead with
            | [], _ | _, None -> []
            | _, Some anchor ->
                cycles
                |> List.map (fun cyclePath ->
                    includeProblemError
                        filepath
                        filetext
                        (sprintf "Include cycle detected: %s" (String.concat " -> " cyclePath))
                        anchor.start
                        anchor.length)

        frontendErrors current @ referenceErrors @ directIncludeErrors @ participatingCycleErrors

    /// Compile-unit validation exposed for tests with fabricated resources.
    /// The retired global symbol-pool path is intentionally no longer available.
    let validateFromResources (resources: Resource seq) filepath filetext =
        validateFromResourcesV2 resources filepath filetext

    let validate (resources: IResourceAPI<_>) filepath filetext =
        validateFromResourcesV2 (resources.GetResources()) filepath filetext

    let private offsetAt (text: string) (pos: pos) =
        let mutable line = 1
        let mutable offset = 0

        while offset < text.Length && line < int pos.Line do
            if text[offset] = '\n' then line <- line + 1
            offset <- offset + 1

        min text.Length (offset + max 0 (int pos.Column))

    let private containsOffset startOffset length offset =
        offset >= startOffset && offset <= startOffset + max 1 length


    let private semanticDefinitionFromResources (resources: Resource seq) pos filepath filetext =
        let snapshots, current = collectSnapshots resources filepath filetext
        let unit = PdxShaderProject.buildCompileUnit snapshots current
        let effective = unit.effective
        let currentSemantic = PdxShaderProject.semanticSnapshot current
        let offset = offsetAt filetext pos
        let declarations = effective |> List.collect PdxShaderRuntime.declarationsFromSnapshot
        let references =
            effective
            |> List.collect PdxShaderRuntime.semanticReferencesFromSnapshot
            |> PdxShaderRuntime.resolveSemanticReferences effective declarations
        let positionInRange (target: range) =
            let afterStart = int pos.Line > int target.StartLine || (pos.Line = target.StartLine && pos.Column >= target.StartColumn)
            let beforeEnd = int pos.Line < int target.EndLine || (pos.Line = target.EndLine && pos.Column <= target.EndColumn)
            afterStart && beforeEnd
        let hlslTarget =
            currentSemantic.hlsl.references
            |> List.tryFind (fun reference -> containsOffset reference.span.startOffset reference.span.Length offset)
            |> Option.map (fun reference -> reference.name, Set.ofList reference.candidateIds)
        let runtimeTarget =
            references
            |> List.tryFind (fun reference -> PdxShaderProject.sameFilePath reference.file filepath && positionInRange reference.span)
            |> Option.map (fun reference -> reference.targetName, Set.ofList reference.targetIds)
        match hlslTarget |> Option.orElse runtimeTarget with
        | Some(name, ids) ->
            declarations
            |> List.filter (fun declaration -> ids.Contains declaration.stableId || (ids.IsEmpty && declaration.name.Equals(name, StringComparison.OrdinalIgnoreCase)))
            |> List.sortBy (fun declaration -> PdxShaderProject.originRank declaration.origin, declaration.file, declaration.selectionRange.StartLine, declaration.selectionRange.StartColumn)
            |> List.tryHead
            |> Option.map _.selectionRange
        | None ->
            declarations
            |> List.tryFind (fun declaration -> PdxShaderProject.sameFilePath declaration.file filepath && positionInRange declaration.selectionRange)
            |> Option.map _.selectionRange

    let goToDefinitionFromResources (resources: Resource seq) pos filepath filetext =
        semanticDefinitionFromResources resources pos filepath filetext

    let goToDefinition (resources: IResourceAPI<_>) pos filepath filetext =
        semanticDefinitionFromResources (resources.GetResources()) pos filepath filetext


    let infoAtPos (resources: IResourceAPI<_>) pos filepath filetext =
        let allResources = resources.GetResources()
        let snapshots, current = collectSnapshots allResources filepath filetext
        let unit = PdxShaderProject.buildCompileUnit snapshots current
        let declarations = unit.effective |> List.collect PdxShaderRuntime.declarationsFromSnapshot
        semanticDefinitionFromResources allResources pos filepath filetext
        |> Option.bind (fun target ->
            declarations
            |> List.tryFind (fun declaration ->
                PdxShaderProject.sameFilePath declaration.file target.FileName
                && declaration.selectionRange.StartLine = target.StartLine
                && declaration.selectionRange.StartColumn = target.StartColumn))
        |> Option.map (fun declaration ->
            let origin =
                match declaration.origin with
                | PdxShaderProject.CurrentDocument -> "current document"
                | PdxShaderProject.Workspace -> "workspace"
                | PdxShaderProject.Dependency order -> sprintf "dependency %d" order
                | PdxShaderProject.Vanilla -> "vanilla"
            let risk =
                if declaration.kind = PdxShaderRuntime.EffectDeclaration then
                    " Effect names are runtime entry points; absent data references do not prove they are unused or safe to rename."
                else ""
            { typename = "pdx_shader"
              name = declaration.name
              localisation = []
              ruleDescription =
                Some(sprintf "**%A** `%s`\n\nDefined in `%s` (%s), condition `%s`.%s" declaration.kind declaration.name declaration.logicalPath origin declaration.presenceCondition risk)
              ruleRequiredScopes = [] })


    let private completionItem label detail category =
        CompletionResponse.Detailed(label, Some detail, None, category)

    let private quotedValueCompletion label detail =
        CompletionResponse.CreateSnippet(label, sprintf "\"%s\"" label, Some detail)

    let private referenceCompletion requiresQuotes name detail =
        if requiresQuotes then
            quotedValueCompletion name detail
        else
            completionItem name detail CompletionCategory.Link

    let private valueCompletion label detail =
        completionItem label detail CompletionCategory.Value

    let private snippets =
        [ CompletionResponse.CreateSnippet(
              "MainCode",
              "MainCode ${1:ShaderName}\n\tConstantBuffers = { ${2:CommonAlternative} }\n[[\n\t$0\n]]",
              Some "Define a MainCode block with HLSL brackets body"
          )
          CompletionResponse.CreateSnippet(
              "Includes",
              "Includes = {\n\t\"${1:file.fxh}\"\n}",
              Some "Include FX shader files"
          )
          CompletionResponse.CreateSnippet(
              "VertexStruct",
              "VertexStruct ${1:VS_INPUT}\n{\n\t$0\n};",
              Some "Define a vertex struct"
          )
          CompletionResponse.CreateSnippet(
              "ConstantBuffer",
              "ConstantBuffer( ${1:Common}, ${2:0}, ${3:0} )\n{\n\t$0\n}",
              Some "Define a constant buffer"
          )
          CompletionResponse.CreateSnippet(
              "VertexShader",
              "VertexShader =\n{\n\tMainCode ${1:VertexShader}\n\t\tConstantBuffers = { ${2:Common} }\n\t[[\n\t\t$0\n\t]]\n}",
              Some "Define vertex shader code"
          )
          CompletionResponse.CreateSnippet(
              "PixelShader",
              "PixelShader =\n{\n\tMainCode ${1:PixelShader}\n\t[[\n\t\t$0\n\t]]\n}",
              Some "Define pixel shader code"
          )
          CompletionResponse.CreateSnippet(
              "Effect",
              "Effect ${1:EffectName}\n{\n\tVertexShader = \"${2:VertexShader}\"\n\tPixelShader = \"${3:PixelShader}\"\n\t$0\n}",
              Some "Bind shader code and render state"
          )
          CompletionResponse.CreateSnippet(
              "BlendState",
              "BlendState ${1:BlendState}\n{\n\tBlendEnable = ${2:yes}\n\t$0\n}",
              Some "Define a blend state"
          )
          CompletionResponse.CreateSnippet(
              "DepthStencilState",
              "DepthStencilState ${1:DepthStencilState}\n{\n\tDepthEnable = ${2:yes}\n\t$0\n}",
              Some "Define a depth stencil state"
          )
          CompletionResponse.CreateSnippet(
              "RasterizerState",
              "RasterizerState ${1:RasterizerState}\n{\n\tCullMode = \"${2:none}\"\n\t$0\n}",
              Some "Define a rasterizer state"
          )
          CompletionResponse.CreateSnippet("Code", "Code\n[[\n\t$0\n]]", Some "Shared HLSL block") ]

    let private samplerProperties =
        [ "Index"
          "MagFilter"
          "MinFilter"
          "MipFilter"
          "AddressU"
          "AddressV"
          "Type"
          "MaxAnisotropy"
          "MipMapLodBias" ]

    let private effectProperties =
        [ "VertexShader"
          "PixelShader"
          "BlendState"
          "DepthStencilState"
          "RasterizerState"
          "Defines" ]

    let private blendProperties =
        [ "BlendEnable"
          "AlphaTest"
          "SourceBlend"
          "DestBlend"
          "SourceAlpha"
          "DestAlpha"
          "BlendOp"
          "BlendOpAlpha"
          "WriteMask" ]

    let private depthStencilProperties =
        [ "DepthEnable"
          "DepthWriteEnable"
          "DepthWriteMask"
          "DepthFunction"
          "StencilEnable"
          "FrontStencilFunc"
          "FrontStencilPassOp"
          "FrontStencilFailOp"
          "FrontStencilDepthFailOp" ]

    let private rasterizerProperties = [ "CullMode"; "FillMode"; "FrontCCW" ]

    let private shaderFieldTypes =
        [ "bool"
          "bool2"
          "bool3"
          "bool4"
          "float"
          "float2"
          "float3"
          "float4"
          "float2x2"
          "float3x3"
          "float4x4"
          "half"
          "half2"
          "half3"
          "half4"
          "int"
          "int2"
          "int3"
          "int4"
          "uint"
          "uint2"
          "uint3"
          "uint4" ]

    let private vertexSemantics =
        [ "POSITION"
          "PDX_POSITION"
          "NORMAL"
          "TANGENT"
          "BINORMAL"
          "COLOR"
          "COLOR0"
          "COLOR1"
          "TEXCOORD0"
          "TEXCOORD1"
          "TEXCOORD2"
          "TEXCOORD3"
          "TEXCOORD4"
          "TEXCOORD5" ]

    let private hlslTypes =
        [ "float"; "float2"; "float3"; "float4"
          "float2x2"; "float3x3"; "float4x4"
          "half"; "half2"; "half3"; "half4"
          "int"; "int2"; "int3"; "int4"
          "uint"; "uint2"; "uint3"; "uint4"
          "bool"; "void"; "static"; "const"; "inout"; "in"; "out"
          "struct"; "Texture2D"; "Texture2DArray"; "TextureCube"
          "sampler2D"; "sampler2DShadow"; "samplerCUBE"
          "SamplerState"; "SamplerComparisonState" ]

    let private hlslControlFlow =
        [ "if"; "else"; "for"; "while"; "do"; "break"; "continue"; "return"; "discard" ]

    let hlslBuiltinSnippets =
        [ // Math
          CompletionResponse.CreateSnippet("mul", "mul(${1:matrix}, ${2:vector})", Some "Multiply matrices/vectors")
          CompletionResponse.CreateSnippet("dot", "dot(${1:a}, ${2:b})", Some "Dot product")
          CompletionResponse.CreateSnippet("cross", "cross(${1:a}, ${2:b})", Some "Cross product of two 3D vectors")
          CompletionResponse.CreateSnippet("normalize", "normalize(${1:vector})", Some "Normalize a vector")
          CompletionResponse.CreateSnippet("length", "length(${1:vector})", Some "Length of a vector")
          CompletionResponse.CreateSnippet("distance", "distance(${1:a}, ${2:b})", Some "Distance between two points")
          CompletionResponse.CreateSnippet("lerp", "lerp(${1:a}, ${2:b}, ${3:t})", Some "Linear interpolation")
          CompletionResponse.CreateSnippet("smoothstep", "smoothstep(${1:min}, ${2:max}, ${3:x})", Some "Hermite interpolation")
          CompletionResponse.CreateSnippet("step", "step(${1:edge}, ${2:x})", Some "Step function (0 or 1)")
          CompletionResponse.CreateSnippet("clamp", "clamp(${1:value}, ${2:min}, ${3:max})", Some "Clamp value to range")
          CompletionResponse.CreateSnippet("saturate", "saturate(${1:value})", Some "Clamp value to [0.0, 1.0]")
          CompletionResponse.CreateSnippet("abs", "abs(${1:value})", Some "Absolute value")
          CompletionResponse.CreateSnippet("sign", "sign(${1:value})", Some "Sign of value (-1, 0, or 1)")
          CompletionResponse.CreateSnippet("max", "max(${1:a}, ${2:b})", Some "Maximum")
          CompletionResponse.CreateSnippet("min", "min(${1:a}, ${2:b})", Some "Minimum")
          CompletionResponse.CreateSnippet("floor", "floor(${1:value})", Some "Floor")
          CompletionResponse.CreateSnippet("ceil", "ceil(${1:value})", Some "Ceiling")
          CompletionResponse.CreateSnippet("round", "round(${1:value})", Some "Round to nearest integer")
          CompletionResponse.CreateSnippet("trunc", "trunc(${1:value})", Some "Truncate to integer part")
          CompletionResponse.CreateSnippet("frac", "frac(${1:value})", Some "Fractional part")
          CompletionResponse.CreateSnippet("pow", "pow(${1:base}, ${2:exp})", Some "Power")
          CompletionResponse.CreateSnippet("sqrt", "sqrt(${1:value})", Some "Square root")
          CompletionResponse.CreateSnippet("exp", "exp(${1:value})", Some "e raised to power")
          CompletionResponse.CreateSnippet("exp2", "exp2(${1:value})", Some "2 raised to power")
          CompletionResponse.CreateSnippet("log", "log(${1:value})", Some "Natural logarithm")
          CompletionResponse.CreateSnippet("log2", "log2(${1:value})", Some "Base-2 logarithm")
          // Trigonometry
          CompletionResponse.CreateSnippet("sin", "sin(${1:value})", Some "Sine")
          CompletionResponse.CreateSnippet("cos", "cos(${1:value})", Some "Cosine")
          CompletionResponse.CreateSnippet("tan", "tan(${1:value})", Some "Tangent")
          CompletionResponse.CreateSnippet("asin", "asin(${1:value})", Some "Arcsine")
          CompletionResponse.CreateSnippet("acos", "acos(${1:value})", Some "Arccosine")
          CompletionResponse.CreateSnippet("atan2", "atan2(${1:y}, ${2:x})", Some "Two-argument arctangent")
          // Vector / geometric
          CompletionResponse.CreateSnippet("reflect", "reflect(${1:incident}, ${2:normal})", Some "Reflect vector around normal")
          CompletionResponse.CreateSnippet("refract", "refract(${1:incident}, ${2:normal}, ${3:eta})", Some "Refract vector")
          // Derivative
          CompletionResponse.CreateSnippet("ddx", "ddx(${1:value})", Some "Partial derivative in x")
          CompletionResponse.CreateSnippet("ddy", "ddy(${1:value})", Some "Partial derivative in y")
          // Clip / test
          CompletionResponse.CreateSnippet("clip", "clip(${1:value})", Some "Discard pixel if value < 0")
          CompletionResponse.CreateSnippet("any", "any(${1:value})", Some "True if any component is non-zero")
          CompletionResponse.CreateSnippet("all", "all(${1:value})", Some "True if all components are non-zero")
          // Texture sampling (legacy DX9 / PDX compat)
          CompletionResponse.CreateSnippet("tex2D", "tex2D(${1:sampler}, ${2:uv})", Some "2D texture lookup")
          CompletionResponse.CreateSnippet("tex2Dlod", "tex2Dlod(${1:sampler}, ${2:float4(uv, 0, lod)})", Some "2D texture lookup with LOD")
          CompletionResponse.CreateSnippet("tex2Dgrad", "tex2Dgrad(${1:sampler}, ${2:uv}, ${3:ddx}, ${4:ddy})", Some "2D texture lookup with gradients")
          CompletionResponse.CreateSnippet("tex2Dproj", "tex2Dproj(${1:sampler}, ${2:uvProj})", Some "2D projective texture lookup")
          CompletionResponse.CreateSnippet("tex2Dbias", "tex2Dbias(${1:sampler}, ${2:float4(uv, 0, bias)})", Some "2D texture lookup with bias")
          CompletionResponse.CreateSnippet("texCUBE", "texCUBE(${1:sampler}, ${2:dir})", Some "Cube texture lookup")
          CompletionResponse.CreateSnippet("texCUBElod", "texCUBElod(${1:sampler}, ${2:float4(dir, lod)})", Some "Cube texture lookup with LOD")
          CompletionResponse.CreateSnippet("texCUBEbias", "texCUBEbias(${1:sampler}, ${2:float4(dir, bias)})", Some "Cube texture lookup with bias")
          // DX11+ style
          CompletionResponse.CreateSnippet("Sample", "Sample(${1:sampler}, ${2:uv})", Some "Texture.Sample(sampler, uv)")
          CompletionResponse.CreateSnippet("SampleLevel", "SampleLevel(${1:sampler}, ${2:uv}, ${3:lod})", Some "Texture.SampleLevel")
          // Paradox PBR Lighting & Special VFX Helpers
          CompletionResponse.CreateSnippet("ApplyPlanetDissolve", "ApplyPlanetDissolve(${1:vPrimaryColor}, ${2:vColor}, ${3:vNormal}, ${4:vUV}, ${5:vDissolve})", Some "float3: Applies planetary explosion/dissolve glowing edge effect")
          CompletionResponse.CreateSnippet("ApplyDissolve", "ApplyDissolve(${1:vPrimaryColor}, ${2:vProgress}, ${3:vColor}, ${4:vAddColor}, ${5:vUV})", Some "float3: Applies model dissolve/materialization holographic transition effect")
          CompletionResponse.CreateSnippet("FastHueShift", "FastHueShift(${1:vColor}, ${2:vShift})", Some "float3: Shifts color hue efficiently in HSV color space")
          CompletionResponse.CreateSnippet("VoronoiNoise2D", "VoronoiNoise2D(${1:vPosition}, ${2:vScale}, ${3:vSpeed})", Some "float2: Generates 2D cellular Voronoi noise for hologram scanlines")
          CompletionResponse.CreateSnippet("GreyOutDotLerp", "GreyOutDotLerp(${1:vColor}, ${2:vAmount})", Some "float3: Desaturates color to grey scale based on amount")
          CompletionResponse.CreateSnippet("AreEqual", "AreEqual(${1:a}, ${2:b}, ${3:precision})", Some "bool: High-precision comparison between two float vectors")
          CompletionResponse.CreateSnippet("UnpackRRxGNormal", "UnpackRRxGNormal(${1:vNormalMap})", Some "float3: Unpacks and reconstructs tangent space normal vector from compressed texture map")
          CompletionResponse.CreateSnippet("GetEnvmapMipLevel", "GetEnvmapMipLevel(${1:glossiness})", Some "float: Calculates optimal environmental cubemap mipmap level based on glossiness")
          CompletionResponse.CreateSnippet("FresnelGlossy", "FresnelGlossy(${1:specularColor}, ${2:eyeDir}, ${3:normal}, ${4:glossiness})", Some "float3: Computes specular fresnel reflection coefficient with glossiness correction")
          CompletionResponse.CreateSnippet("MetalnessToDiffuse", "MetalnessToDiffuse(${1:metalness}, ${2:color})", Some "float3: Re-maps base diffuse color vector based on PBR metalness")
          CompletionResponse.CreateSnippet("MetalnessToSpec", "MetalnessToSpec(${1:metalness}, ${2:color}, ${3:specular})", Some "float3: Re-maps base specular highlight color vector based on PBR metalness")
          CompletionResponse.CreateSnippet("ToGamma", "ToGamma(${1:linearColor})", Some "float3: Converts linear space color to gamma space color")
          CompletionResponse.CreateSnippet("ToLinear", "ToLinear(${1:gammaColor})", Some "float3: Converts gamma space color to linear space color")
          CompletionResponse.CreateSnippet("ComposeLight", "ComposeLight(${1:lightingProperties}, ${2:shadowTerm}, ${3:diffuseLight}, ${4:specularLight})", Some "float3: Combines diffuse and specular lighting components into final pixel color")
          CompletionResponse.CreateSnippet("CalculateSystemPointLight", "CalculateSystemPointLight(${1:lightingProperties}, ${2:intensity}, ${3:diffuse}, ${4:specular})", Some "void: Computes global system point light illumination contribution")
          CompletionResponse.CreateSnippet("CalculatePointLights", "CalculatePointLights(${1:lightingProperties}, ${2:lightDataMap}, ${3:lightIndexMap}, ${4:diffuse}, ${5:specular})", Some "void: Computes multiple dynamic tiled point lights illumination contribution")
          // Additional PDX helper functions
          CompletionResponse.CreateSnippet("GetPointLight", "GetPointLight(${1:posRadius}, ${2:colorFalloff})", Some "PointLight: Constructs a PointLight struct from packed float4 parameters")
          CompletionResponse.CreateSnippet("GetNonLinearGlossiness", "GetNonLinearGlossiness(${1:glossiness})", Some "float: Remaps linear glossiness to non-linear perceptual glossiness")
          CompletionResponse.CreateSnippet("CreateScaleMatrix", "CreateScaleMatrix(${1:scale})", Some "float4x4: Creates a 4x4 uniform or non-uniform scale matrix")
          CompletionResponse.CreateSnippet("tex2Dlod0", "tex2Dlod0(${1:sampler}, ${2:uv})", Some "float4: 2D texture lookup at mipmap LOD level 0 (vertex shader safe)") ]

    /// PDX platform semantics and common conditional macros from vanilla shaders
    let private hlslPdxDirectives =
        [ // Platform semantics (defines_hlsl.fxh)
          "PDX_POSITION"; "PDX_COLOR"
          "PDX_DIRECTX_9"; "PDX_DIRECTX_11"; "PDX_OPENGL"; "PDX_ORBIS"
          // Mesh features
          "PDX_MESH_UV1"; "PDX_FOUR_SPLITS"
          // Lighting model selection
          "PDX_LEGACY_BLINN_PHONG"; "PDX_IMPROVED_BLINN_PHONG"
          // Debug toggles
          "PDX_DEBUG_NORMAL"; "PDX_DEBUG_DIFFUSE"; "PDX_DEBUG_SPEC"
          "PDX_DEBUG_GLOSSINESS"; "PDX_DEBUG_SHADOW"
          "PDX_DEBUG_SUN_LIGHT"; "PDX_DEBUG_SUN_LIGHT_WITH_SHADOW"
          "PDX_DEBUG_SYSTEM_LIGHT"; "PDX_DEBUG_AMBIENT"; "PDX_DEBUG_CAMERA_LIGHTS"
          // PDX compat helpers (defines_hlsl.fxh)
          "vec2"; "vec3"; "vec4"
          "CastTo3x3"; "Create3x3"; "GetMatrixData"
          "uintIfSupported"; "tex2Dlod0"
          // Common feature flags (used in Defines = { })
          "PIXEL_SHADER"; "VERTEX_SHADER"
          "IS_SHADOW"; "IS_PLANET"; "IS_STAR"; "IS_RING"; "IS_CLOUDS"
          "IS_NEBULA"; "IS_HOLOGRAM"; "IS_NEUTRON_STAR_SHELL"
          "IS_BORDER"; "IS_CHARACTER"; "IS_CITY"; "IS_ENVIRONMENT"; "IS_ROOM"; "IS_TRAIL"
          "EMISSIVE"; "EMISSIVE_FLOW"; "EMISSIVE_NOISE"; "GLOSSY_EMISSIVE"
          "DISSOLVE"; "DISSOLVE_USE_EROSION"
          "ALPHA_TEST"; "ALPHA_OVERRIDE"
          "ANIMATE_UV"; "ANIMATE_UV_ALPHA"; "ANIMATE_UV_UP"; "ANIMATED"
          "ADD_COLOR"; "COLORED"; "BLOOM"; "HDR"; "CLOAKED"
          "USE_EMPIRE_COLOR"; "USE_EMPIRE_COLOR_MASK_FOR_EMISSIVE"
          "USE_FLOWMAP"; "USE_HUE_SHIFT_MASK"; "USE_NORMALMAP_AS_ALPHA"
          "GUI_ICON"; "CUSTOM_DIFFUSE"; "HAIR"; "CLOTHES"
          "MASKING"; "HUE_SHIFT"; "RIM_LIGHT"
          "NO_BILLBOARD"; "NO_PLANET_EMISSIVE"; "NO_ALPHA_MULTIPLIED_EMISSIVE"
          "SHADOW_PCF"; "SHADOW_MULTI_TAP"
          "HEALTH_BAR"; "PROGRESS_BAR"; "BUTTON_STATES"; "DISABLED"
          "UNIFORM_WIDTH"; "RIPPLE_UV"; "FLOWMAP"
          "BLEND_TO_DIFFUSE_ALPHA"; "APPLY_EMISSIVE_TO_ALPHA"
          "COLOR_LUT"; "PLANET_LIGHTS_EMISSIVE"; "YCOCG" ]

    /// Paradox system-injected global variables (matrices, lighting, camera variables)
    let hlslPdxGlobals =
        [ // System transformation matrices
          CompletionResponse.CreateSnippet("WorldMatrix", "WorldMatrix", Some "4x4 Matrix: Transforms local coordinates to world coordinates")
          CompletionResponse.CreateSnippet("ViewMatrix", "ViewMatrix", Some "4x4 Matrix: Transforms world coordinates to view coordinates")
          CompletionResponse.CreateSnippet("ProjectionMatrix", "ProjectionMatrix", Some "4x4 Matrix: Transforms view coordinates to clip coordinates")
          CompletionResponse.CreateSnippet("ViewProjectionMatrix", "ViewProjectionMatrix", Some "4x4 Matrix: Combined View and Projection matrix")
          CompletionResponse.CreateSnippet("InvViewMatrix", "InvViewMatrix", Some "4x4 Matrix: Inverse View matrix (Camera world position matrix)")
          CompletionResponse.CreateSnippet("ShadowProjectionMatrix", "ShadowProjectionMatrix", Some "4x4 Matrix: Projection matrix for shadow mapping")
          CompletionResponse.CreateSnippet("ShadowMatrix", "ShadowMatrix", Some "4x4 Matrix: Combined World View Projection for light space")
          // Camera & Environment
          CompletionResponse.CreateSnippet("CameraPosition", "CameraPosition", Some "float3: World position of the camera/view point")
          CompletionResponse.CreateSnippet("CameraDirection", "CameraDirection", Some "float3: Forward viewing direction of the camera")
          CompletionResponse.CreateSnippet("HdrRange_Time_ClipHeight", "HdrRange_Time_ClipHeight", Some "float4: System params (x: HDR range, y: Game Time in seconds, z: Clip height)")
          // Lighting
          CompletionResponse.CreateSnippet("LightPosition", "LightPosition", Some "float3: Position of the primary light source")
          CompletionResponse.CreateSnippet("LightDirection", "LightDirection", Some "float3: Direction vector of the primary light source")
          CompletionResponse.CreateSnippet("SunColor", "SunColor", Some "float3: Color and intensity of the sun/primary light source")
          CompletionResponse.CreateSnippet("AmbientColor", "AmbientColor", Some "float3: Global ambient color of the scene")
          // Geometry & Vertex Attributes
          CompletionResponse.CreateSnippet("vPosition", "vPosition", Some "float4: Vertex local position in object space")
          CompletionResponse.CreateSnippet("vPos", "vPos", Some "float3/float4: Interpolated vertex position in world space or screen-space pixel position")
          CompletionResponse.CreateSnippet("vNormal", "vNormal", Some "float3: Vertex normal vector for basic lighting calculation")
          CompletionResponse.CreateSnippet("vTangent", "vTangent", Some "float4: Vertex tangent vector for TBN rotation matrix and normal mapping")
          CompletionResponse.CreateSnippet("vBitangent", "vBitangent", Some "float3: Vertex bitangent vector for TBN rotation matrix and normal mapping")
          CompletionResponse.CreateSnippet("vSphere", "vSphere", Some "float4: Spherical projection/mapping vector for shield hit ripple and planet glow")
          CompletionResponse.CreateSnippet("vUV0", "vUV0", Some "float2: First texture UV coordinates (Diffuse, Normal mapping)")
          CompletionResponse.CreateSnippet("vUV1", "vUV1", Some "float2: Second texture UV coordinates (Empire paint mask, scrolling特效)")
          CompletionResponse.CreateSnippet("vObjectNormal", "vObjectNormal", Some "float3: Original object-space vertex normal")
          CompletionResponse.CreateSnippet("vBoneWeight", "vBoneWeight", Some "float4: Bone weights for skeletal animation skinning")
          CompletionResponse.CreateSnippet("vBoneIndex", "vBoneIndex", Some "float4: Bone indices for skeletal animation skinning (indices into matBones)")
          CompletionResponse.CreateSnippet("vSkinnedPosition", "vSkinnedPosition", Some "float4: Blended skinned vertex position from skeletal animation")
          CompletionResponse.CreateSnippet("vSkinnedNormal", "vSkinnedNormal", Some "float3: Blended skinned vertex normal from skeletal animation")
          CompletionResponse.CreateSnippet("vSkinnedTangent", "vSkinnedTangent", Some "float3: Blended skinned vertex tangent from skeletal animation")
          CompletionResponse.CreateSnippet("vSkinnedBitangent", "vSkinnedBitangent", Some "float3: Blended skinned vertex bitangent from skeletal animation")
          CompletionResponse.CreateSnippet("vOffset", "vOffset", Some "float: Offset parameter for normal debugging")
          // Material constants & Special parameters
          CompletionResponse.CreateSnippet("scrollingSpeed", "scrollingSpeed", Some "float2: Speed/direction vector for scrolling UV textures (Shield, energy flow)")
          CompletionResponse.CreateSnippet("scrollingUV", "scrollingUV", Some "float2: Calculated dynamic scrolling UV texture coordinates")
          CompletionResponse.CreateSnippet("matBones", "matBones", Some "float4x4[50]: Array of transformation matrices for skeletal bone animation")
          CompletionResponse.CreateSnippet("vUVAnimationDir", "vUVAnimationDir", Some "float2: Material property: Direction vector for UV animation scrolling")
          CompletionResponse.CreateSnippet("vUVAnimationTime", "vUVAnimationTime", Some "float: Material property: Running time factor for UV animation scrolling")
          CompletionResponse.CreateSnippet("vBloomFactor", "vBloomFactor", Some "float: Material property: Bloom/emissive intensity adjustment multiplier")
          CompletionResponse.CreateSnippet("vDamage", "vDamage", Some "float: Material property: Damage/scratch intensity factor (controls burns/cracks)")
          CompletionResponse.CreateSnippet("PrimaryColor", "PrimaryColor", Some "float4: Material property: Primary color vector of the mesh or effect")
          CompletionResponse.CreateSnippet("AtmosphereColor", "AtmosphereColor", Some "float4: Material property: Glowing color vector for planet atmosphere")
          CompletionResponse.CreateSnippet("AtmosphereIntensity", "AtmosphereIntensity", Some "float: Material property: Glowing intensity multiplier for planet atmosphere")
          CompletionResponse.CreateSnippet("AtmosphereWidth", "AtmosphereWidth", Some "float: Material property: Width/thickness boundary for planet atmosphere")
          CompletionResponse.CreateSnippet("vPlanetDissolveTime", "vPlanetDissolveTime", Some "float: Runtime progression factor for planet dissolve/explosion effect")
          CompletionResponse.CreateSnippet("vPlanetDissolveColorMult", "vPlanetDissolveColorMult", Some "float3: Glowing edge lava color multiplier for planet dissolve effect")
          CompletionResponse.CreateSnippet("vProgressBarValue", "vProgressBarValue", Some "float: Progress fill percentage factor for progress bars")
          CompletionResponse.CreateSnippet("vHPBarPadding", "vHPBarPadding", Some "float: Horizontal layout padding adjustment parameter for HP bars")
          CompletionResponse.CreateSnippet("vHealth", "vHealth", Some "float: Current entity health ratio (0.0 to 1.0)")
          CompletionResponse.CreateSnippet("vAlphaOverrideMult", "vAlphaOverrideMult", Some "float: Material alpha override opacity multiplier")
          CompletionResponse.CreateSnippet("vConstructionProgress", "vConstructionProgress", Some "float: Progress factor for mesh construction laser sweep effect")
          CompletionResponse.CreateSnippet("vAuraColor", "vAuraColor", Some "float4: Glowing light emission color vector of the entity's aura")
          CompletionResponse.CreateSnippet("vAuraRadius", "vAuraRadius", Some "float: Physical radius boundary parameter of the entity's glowing aura")
          CompletionResponse.CreateSnippet("LavaBrightColor", "LavaBrightColor", Some "float3: Star material: Color vector of the high-intensity lava eruption layer")
          CompletionResponse.CreateSnippet("LavaHotStoneColor", "LavaHotStoneColor", Some "float3: Star material: Color vector of the warm stone/magma cooled crust layer")
          CompletionResponse.CreateSnippet("LavaColdStoneColor", "LavaColdStoneColor", Some "float3: Star material: Color vector of the low-intensity cooled dark stone layer")
          CompletionResponse.CreateSnippet("StarAtmosphereIntensity", "StarAtmosphereIntensity", Some "float: Star material: Glowing intensity for the star atmosphere/corona")
          CompletionResponse.CreateSnippet("StarAtmosphereWidth", "StarAtmosphereWidth", Some "float: Star material: Thickness/width boundary for the star atmosphere/corona")
          CompletionResponse.CreateSnippet("StarAtmosphereColor", "StarAtmosphereColor", Some "float4: Star material: Glowing color vector for the star atmosphere/corona")
          // Mined from Kuat Ancient Empire meshes & WPO/UI custom shader constants
          CompletionResponse.CreateSnippet("WPODirection", "WPODirection", Some "float2: Direction vector for World Position Offset (WPO) vertex animation")
          CompletionResponse.CreateSnippet("WPOSpeed", "WPOSpeed", Some "float: Animation speed factor for World Position Offset (WPO) waves")
          CompletionResponse.CreateSnippet("OffsetStrength", "OffsetStrength", Some "float: Overall physical offset strength multiplier for vertex displacement")
          CompletionResponse.CreateSnippet("WPOScale", "WPOScale", Some "float: High-frequency noise scale parameter for WPO vertex shader")
          CompletionResponse.CreateSnippet("WPOBigScale", "WPOBigScale", Some "float: Low-frequency macro noise scale parameter for WPO vertex shader")
          CompletionResponse.CreateSnippet("WPOTime", "WPOTime", Some "float: Accumulated game runtime factor for WPO vertex wave progression")
          CompletionResponse.CreateSnippet("vEmissiveRecolorCrunch", "vEmissiveRecolorCrunch", Some "float: Contrast/crunch multiplier for emissive map color recoloring on ships")
          CompletionResponse.CreateSnippet("Glossiness_", "Glossiness_", Some "float: Global override parameter for glossiness/smoothness multiplier")
          CompletionResponse.CreateSnippet("Specular_", "Specular_", Some "float: Global override parameter for specular reflectivity multiplier")
          CompletionResponse.CreateSnippet("Metalness_", "Metalness_", Some "float: Global override parameter for metalness multiplier")
          CompletionResponse.CreateSnippet("Sensor", "Sensor", Some "float: Planet active sensor scan overlay sweep progression factor")
          CompletionResponse.CreateSnippet("Colonized", "Colonized", Some "float: Planet colony growth factor, controls building lights distribution on darkside")
          CompletionResponse.CreateSnippet("vEmissiveRecolorCrunch_Construction", "vEmissiveRecolorCrunch_Construction", Some "float: Recolor crunch contrast control for ship construction glow")
          CompletionResponse.CreateSnippet("ConstructionColor", "ConstructionColor", Some "float4: Emissive color vector of the laser scanning boundary during construction")
          CompletionResponse.CreateSnippet("PrimaryColor_Construction", "PrimaryColor_Construction", Some "float4: Base primary hull color vector applied during mesh construction")
          CompletionResponse.CreateSnippet("PortraitScale", "PortraitScale", Some "float3: 3D scale adjustment vector for character portraits rendering")
          CompletionResponse.CreateSnippet("PortraitMipLevel", "PortraitMipLevel", Some "float: Texture mipmap level limit factor for character portraits rendering")
          CompletionResponse.CreateSnippet("CustomDiffuseTexture", "CustomDiffuseTexture", Some "float: Toggle parameter for custom diffuse texture override on mesh")
          CompletionResponse.CreateSnippet("FlowMapIntensity", "FlowMapIntensity", Some "float: Dynamic scrolling flowmap deformation intensity multiplier")
          CompletionResponse.CreateSnippet("HueShift", "HueShift", Some "float: Color hue shift progression factor for spectrum cycling effects")
          CompletionResponse.CreateSnippet("UVStep", "UVStep", Some "float2: UV step/tiling spacing factor for texture coordinate repeat offsets")
          CompletionResponse.CreateSnippet("vOverValue", "vOverValue", Some "float: UI element hover state emission/transparency intensity value")
          CompletionResponse.CreateSnippet("vDownValue", "vDownValue", Some "float: UI element pressed state emission/transparency intensity value")
          CompletionResponse.CreateSnippet("vSelectedValue", "vSelectedValue", Some "float: UI element selected/active state emission/transparency intensity value")
          CompletionResponse.CreateSnippet("vIntelValue", "vIntelValue", Some "float: UI element espionage/intel state transparency intensity value")
          CompletionResponse.CreateSnippet("ObjectPos", "ObjectPos", Some "float3: Origin world position coordinates of the shield collision ellipsoid")
          CompletionResponse.CreateSnippet("ObjectDir", "ObjectDir", Some "float3: Direction vector of the incoming laser impact on shield ellipsoid")
          CompletionResponse.CreateSnippet("ObjectScale", "ObjectScale", Some "float3: Ellipsoid-to-sphere boundary scaling factor for shield hit animation")
          CompletionResponse.CreateSnippet("vNumLoops", "vNumLoops", Some "float: Repetitive animation loop limit parameter for effects")
          CompletionResponse.CreateSnippet("vTimePerLoop", "vTimePerLoop", Some "float: Time duration threshold allocated for each animation cycle loop")
          CompletionResponse.CreateSnippet("vObjectTime", "vObjectTime", Some "float: Running local time tracker for shield collision animation")
          // Mined planetary textures, volumetric maps and light sources
          CompletionResponse.CreateSnippet("Time", "Time", Some "float: Running game time factor for star fluid wave animations")
          CompletionResponse.CreateSnippet("SystemLightPosRadius", "SystemLightPosRadius", Some "float4: Global system primary light source coordinates (xyz) and lighting range (w)")
          CompletionResponse.CreateSnippet("SystemLightColorFalloff", "SystemLightColorFalloff", Some "float4: Global system primary light source color (rgb) and falloff attenuation (w)")
          CompletionResponse.CreateSnippet("LavaNoise", "LavaNoise", Some "TextureCube: 3D cubemap noise texture for animated star magma")
          CompletionResponse.CreateSnippet("LavaDiffuse", "LavaDiffuse", Some "Texture2D: Diffuse color map for flowing star lava")
          CompletionResponse.CreateSnippet("StoneDiffuse", "StoneDiffuse", Some "Texture2D: Diffuse color map for cooled star crust/stone")
          CompletionResponse.CreateSnippet("NormalMap", "NormalMap", Some "Texture2D: Global tangent space normal map for planetary surface details")
          CompletionResponse.CreateSnippet("SpecularMap", "SpecularMap", Some "Texture2D: Global PBR parameters map (specular, glossiness, metalness, empire mask)")
          // Camera state vectors
          CompletionResponse.CreateSnippet("vCamPos", "vCamPos", Some "float3: Camera world space position coordinates")
          CompletionResponse.CreateSnippet("vCamLookAtDir", "vCamLookAtDir", Some "float3: Camera forward look-at direction vector")
          CompletionResponse.CreateSnippet("vCamRightDir", "vCamRightDir", Some "float3: Camera right-side direction vector for billboarding")
          CompletionResponse.CreateSnippet("vCamUpDir", "vCamUpDir", Some "float3: Camera up direction vector for billboarding")
          // Erosion & dissolve control
          CompletionResponse.CreateSnippet("Erosion", "Erosion", Some "float4: Dissolve/erosion control vector for mesh fade effects")
          // Progress bar & map icon colors
          CompletionResponse.CreateSnippet("BARPrimaryColor", "BARPrimaryColor", Some "float4: Primary color vector for health/progress bar rendering")
          CompletionResponse.CreateSnippet("ProgressBarPrimaryColor", "ProgressBarPrimaryColor", Some "float4: Primary color vector for map icon progress indicators")
          // Cubemap & ship state
          CompletionResponse.CreateSnippet("CubemapIntensity", "CubemapIntensity", Some "float: Environmental cubemap reflection intensity multiplier")
          CompletionResponse.CreateSnippet("ShipVars", "ShipVars", Some "float4: Packed ship state variables (dissolve progress, cloaking, etc.)")
          // Core texture samplers
          CompletionResponse.CreateSnippet("DiffuseMap", "DiffuseMap", Some "Texture2D: Primary diffuse/albedo color texture sampler")
          CompletionResponse.CreateSnippet("CustomTexture", "CustomTexture", Some "Texture2D: Custom auxiliary texture sampler (city lights, noise, etc.)")
          CompletionResponse.CreateSnippet("CustomTexture2", "CustomTexture2", Some "Texture2D: Secondary custom auxiliary texture sampler")
          CompletionResponse.CreateSnippet("LightDataMap", "LightDataMap", Some "Texture2D: Tiled point light data texture for deferred lighting")
          CompletionResponse.CreateSnippet("LightIndexMap", "LightIndexMap", Some "Texture2D: Tiled point light index lookup texture")
          CompletionResponse.CreateSnippet("WPOTexture", "WPOTexture", Some "Texture2D: World Position Offset noise texture sampler")
          CompletionResponse.CreateSnippet("EnvironmentMap", "EnvironmentMap", Some "TextureCube: Global skybox cubemap for environmental reflections")
          // Portrait texture samplers
          CompletionResponse.CreateSnippet("PortraitClothes", "PortraitClothes", Some "Texture2D: Portrait clothing layer texture sampler")
          CompletionResponse.CreateSnippet("PortraitHair", "PortraitHair", Some "Texture2D: Portrait hair layer texture sampler")
          CompletionResponse.CreateSnippet("PortraitCharacter", "PortraitCharacter", Some "Texture2D: Portrait base character body texture sampler")
          CompletionResponse.CreateSnippet("PortraitEvolutionDecal", "PortraitEvolutionDecal", Some "Texture2D: Portrait evolution decal overlay texture sampler")
          // Transform matrices
          CompletionResponse.CreateSnippet("Transform", "Transform", Some "float4x4: Local-to-world transform matrix for simple vertex shaders")
          CompletionResponse.CreateSnippet("ViewProjectionMatrix_Duplicate", "ViewProjectionMatrix_Duplicate", Some "float4x4: Duplicate View-Projection matrix for alternative constant buffers")
          // Generic UV
          CompletionResponse.CreateSnippet("vUV", "vUV", Some "float2: Generic UV texture coordinate variable") ]

    let private propertyValues =
        Map.ofList
            [ "MagFilter", [ "Linear"; "Point"; "Anisotropic" ]
              "MinFilter", [ "Linear"; "Point"; "Anisotropic" ]
              "MipFilter", [ "Linear"; "Point"; "None" ]
              "AddressU", [ "Wrap"; "Clamp"; "Mirror"; "Border" ]
              "AddressV", [ "Wrap"; "Clamp"; "Mirror"; "Border" ]
              "Type", [ "Cube"; "2D"; "3D" ]
              "MaxAnisotropy", [ "1"; "2"; "4"; "8"; "16" ]
              "MipMapLodBias", [ "-1"; "0"; "1" ]
              "BlendEnable", [ "yes"; "no" ]
              "AlphaTest", [ "yes"; "no" ]
              "SourceBlend",
              [ "SRC_ALPHA"; "INV_SRC_ALPHA"; "ONE"; "ZERO"; "SRC_COLOR"; "INV_SRC_COLOR"; "DEST_ALPHA"; "INV_DEST_ALPHA"; "DEST_COLOR"; "INV_DEST_COLOR"
                "\"SRC_ALPHA\""; "\"INV_SRC_ALPHA\""; "\"ONE\""; "\"ZERO\""; "\"SRC_COLOR\""; "\"INV_SRC_COLOR\""; "\"DEST_ALPHA\""; "\"INV_DEST_ALPHA\""; "\"DEST_COLOR\""; "\"INV_DEST_COLOR\"" ]
              "DestBlend",
              [ "SRC_ALPHA"; "INV_SRC_ALPHA"; "ONE"; "ZERO"; "SRC_COLOR"; "INV_SRC_COLOR"; "DEST_ALPHA"; "INV_DEST_ALPHA"; "DEST_COLOR"; "INV_DEST_COLOR"
                "\"SRC_ALPHA\""; "\"INV_SRC_ALPHA\""; "\"ONE\""; "\"ZERO\""; "\"SRC_COLOR\""; "\"INV_SRC_COLOR\""; "\"DEST_ALPHA\""; "\"INV_DEST_ALPHA\""; "\"DEST_COLOR\""; "\"INV_DEST_COLOR\"" ]
              "SourceAlpha", [ "SRC_ALPHA"; "INV_SRC_ALPHA"; "ONE"; "ZERO"; "\"SRC_ALPHA\""; "\"INV_SRC_ALPHA\""; "\"ONE\""; "\"ZERO\"" ]
              "DestAlpha", [ "SRC_ALPHA"; "INV_SRC_ALPHA"; "ONE"; "ZERO"; "\"SRC_ALPHA\""; "\"INV_SRC_ALPHA\""; "\"ONE\""; "\"ZERO\"" ]
              "BlendOp", [ "ADD"; "SUBTRACT"; "REV_SUBTRACT"; "MIN"; "MAX" ]
              "BlendOpAlpha", [ "ADD"; "SUBTRACT"; "REV_SUBTRACT"; "MIN"; "MAX" ]
              "WriteMask", [ "RED"; "GREEN"; "BLUE"; "ALPHA"; "RED|GREEN|BLUE"; "RED|GREEN|BLUE|ALPHA"; "\"RED|GREEN|BLUE\""; "\"RED|GREEN|BLUE|ALPHA\""; "0x0F"; "0x0E"; "0x0C"; "0x08"; "0x00"; "\"0x0F\""; "\"0x0E\""; "\"0x0C\""; "\"0x08\""; "\"0x00\"" ]
              "CullMode", [ "none"; "cw"; "ccw"; "CULL_NONE"; "CULL_BACK"; "CULL_FRONT"; "\"CULL_NONE\""; "\"CULL_BACK\""; "\"CULL_FRONT\"" ]
              "FillMode", [ "solid"; "wireframe"; "FILL_SOLID"; "FILL_WIREFRAME"; "\"FILL_SOLID\""; "\"FILL_WIREFRAME\"" ]
              "FrontCCW", [ "yes"; "no" ]
              "DepthEnable", [ "yes"; "no" ]
              "DepthWriteEnable", [ "yes"; "no" ]
              "DepthWriteMask", [ "DEPTH_WRITE_ALL"; "DEPTH_WRITE_ZERO"; "\"DEPTH_WRITE_ALL\""; "\"DEPTH_WRITE_ZERO\"" ]
              "DepthFunction", [ "LESS"; "LESS_EQUAL"; "EQUAL"; "GREATER"; "GREATER_EQUAL"; "ALWAYS"; "NEVER" ]
              "StencilEnable", [ "yes"; "no" ]
              "FrontStencilFunc",
              [ "ALWAYS"; "NEVER"; "LESS"; "LESS_EQUAL"; "EQUAL"; "GREATER"; "GREATER_EQUAL"; "NOT_EQUAL" ]
              "FrontStencilPassOp", [ "KEEP"; "ZERO"; "REPLACE"; "INCR"; "DECR"; "INVERT"; "INCR_SAT"; "DECR_SAT" ]
              "FrontStencilFailOp", [ "KEEP"; "ZERO"; "REPLACE"; "INCR"; "DECR"; "INVERT"; "INCR_SAT"; "DECR_SAT" ]
              "FrontStencilDepthFailOp",
              [ "KEEP"; "ZERO"; "REPLACE"; "INCR"; "DECR"; "INVERT"; "INCR_SAT"; "DECR_SAT" ] ]

    let completeFromResources (resources: Resource seq) pos filepath filetext =
        let snapshots, current = collectSnapshots resources filepath filetext
        let includeNames = snapshotIncludeNames snapshots
        let unit = PdxShaderProject.buildCompileUnit snapshots current
        let views = unit.effective |> List.map (fun snapshot -> snapshot, PdxShaderProject.semanticSnapshot snapshot)
        let currentSemantic = PdxShaderProject.semanticSnapshot current
        let offset = offsetAt filetext pos
        let spanContains (span: PdxShaderSyntax.TextSpan) = offset >= span.startOffset && offset <= span.endOffset
        let rec nodePath (node: PdxShaderSyntax.ShaderSyntaxNode) =
            if not (spanContains node.span) then []
            else
                node
                :: (node.children
                    |> List.tryPick (fun child ->
                        let nested = nodePath child
                        if nested.IsEmpty then None else Some nested)
                    |> Option.defaultValue [])
        let path = nodePath currentSemantic.syntax.root
        let enclosingKind =
            path
            |> List.rev
            |> List.tryPick (fun node ->
                match node.kind with
                | PdxShaderSyntax.ShaderNodeKind.VertexStruct
                | PdxShaderSyntax.ShaderNodeKind.ConstantBuffer
                | PdxShaderSyntax.ShaderNodeKind.Effect
                | PdxShaderSyntax.ShaderNodeKind.Sampler
                | PdxShaderSyntax.ShaderNodeKind.Samplers
                | PdxShaderSyntax.ShaderNodeKind.BlendState
                | PdxShaderSyntax.ShaderNodeKind.DepthStencilState
                | PdxShaderSyntax.ShaderNodeKind.RasterizerState
                | PdxShaderSyntax.ShaderNodeKind.Includes as kind -> Some kind
                | _ -> None)
        let isFxh = filepath.EndsWith(".fxh", StringComparison.OrdinalIgnoreCase)
        let insideHlsl = isFxh || path |> List.exists (fun node -> node.kind = PdxShaderSyntax.ShaderNodeKind.HlslRegion)
        let significantTokens =
            currentSemantic.syntax.tokens
            |> Array.filter (fun token ->
                token.span.endOffset <= offset
                && token.kind <> PdxShaderSyntax.ShaderTokenKind.Whitespace
                && token.kind <> PdxShaderSyntax.ShaderTokenKind.NewLine
                && token.kind <> PdxShaderSyntax.ShaderTokenKind.LineComment
                && token.kind <> PdxShaderSyntax.ShaderTokenKind.BlockComment)
        let previousToken = significantTokens |> Array.tryLast
        let insideString =
            currentSemantic.syntax.tokens
            |> Array.exists (fun token ->
                token.kind = PdxShaderSyntax.ShaderTokenKind.StringLiteral
                && offset >= token.span.startOffset
                && offset <= token.span.endOffset)
        let declarations = unit.effective |> List.collect PdxShaderRuntime.declarationsFromSnapshot
        let declarationNames kind =
            declarations
            |> List.filter (fun declaration -> declaration.kind = kind)
            |> List.map _.name
            |> List.distinctBy _.ToLowerInvariant()
            |> List.sort
        let conditionNames =
            views
            |> List.collect (fun (_, semantic) ->
                semantic.preprocessor.regions
                |> List.collect (fun region -> PdxShaderPreprocessor.symbols region.condition |> Set.toList))
            |> List.distinctBy _.ToLowerInvariant()
            |> List.sort
        let responseForSymbol (symbol: PdxShaderHlsl.HlslSymbol) =
            match symbol.kind with
            | PdxShaderHlsl.FunctionSymbol ->
                let placeholders =
                    symbol.parameters
                    |> List.mapi (fun index parameter -> sprintf "${%d:%s}" (index + 1) parameter.name)
                    |> String.concat ", "
                CompletionResponse.CreateSnippet(symbol.name, sprintf "%s(%s)" symbol.name placeholders, Some(sprintf "%A" symbol.symbolType))
            | PdxShaderHlsl.TypeSymbol
            | PdxShaderHlsl.StructSymbol -> valueCompletion symbol.name "HLSL type"
            | PdxShaderHlsl.MacroSymbol -> completionItem symbol.name "HLSL macro" CompletionCategory.Global
            | _ -> completionItem symbol.name (sprintf "HLSL %A" symbol.symbolType) CompletionCategory.Value
        let deduplicate responses =
            responses
            |> List.distinctBy (function
                | CompletionResponse.Snippet(label, _, _, _, _)
                | CompletionResponse.Simple(label, _, _)
                | CompletionResponse.Detailed(label, _, _, _) -> label.ToLowerInvariant())
        if insideHlsl then
            let currentScopeIds =
                let containing =
                    currentSemantic.hlsl.scopes
                    |> List.filter (fun scope -> spanContains scope.span)
                    |> List.sortBy (fun scope -> scope.span.Length)
                    |> List.tryHead
                let rec ancestors acc scopeId =
                    if Set.contains scopeId acc then acc
                    else
                        let next = Set.add scopeId acc
                        currentSemantic.hlsl.scopes
                        |> List.tryFind (fun scope -> scope.id = scopeId)
                        |> Option.bind _.parentId
                        |> Option.map (ancestors next)
                        |> Option.defaultValue next
                containing |> Option.map (fun scope -> ancestors Set.empty scope.id) |> Option.defaultValue Set.empty
            let semanticSymbols =
                views
                |> List.collect (fun (snapshot, semantic) ->
                    semantic.hlsl.symbols
                    |> List.filter (fun symbol ->
                        not (PdxShaderProject.sameFilePath snapshot.displayPath filepath)
                        || Set.contains symbol.scopeId currentScopeIds
                        || symbol.kind = PdxShaderHlsl.FunctionSymbol
                        || symbol.kind = PdxShaderHlsl.TypeSymbol
                        || symbol.kind = PdxShaderHlsl.StructSymbol
                        || symbol.kind = PdxShaderHlsl.GlobalVariableSymbol
                        || symbol.kind = PdxShaderHlsl.ResourceSymbol
                        || symbol.kind = PdxShaderHlsl.SamplerSymbol
                        || symbol.kind = PdxShaderHlsl.MacroSymbol)
                    |> List.map responseForSymbol)
            (semanticSymbols
             @ (hlslTypes |> List.map (fun name -> valueCompletion name "HLSL type"))
             @ (hlslControlFlow |> List.map (fun name -> completionItem name "HLSL keyword" CompletionCategory.Value))
             @ hlslBuiltinSnippets
             @ hlslPdxGlobals)
            |> deduplicate
        else
            let referenceValues detail values =
                values |> List.map (fun value -> referenceCompletion (not insideString) value detail)
            let contextualCompletions () =
                match enclosingKind, previousToken |> Option.map _.kind with
                | Some PdxShaderSyntax.ShaderNodeKind.VertexStruct, Some PdxShaderSyntax.ShaderTokenKind.Colon ->
                    vertexSemantics |> List.map (fun value -> valueCompletion value "Vertex semantic")
                | Some PdxShaderSyntax.ShaderNodeKind.VertexStruct, _
                | Some PdxShaderSyntax.ShaderNodeKind.ConstantBuffer, _ ->
                    shaderFieldTypes |> List.map (fun value -> valueCompletion value "FX field type")
                | Some PdxShaderSyntax.ShaderNodeKind.Effect, _ ->
                    effectProperties |> List.map (fun value -> completionItem value "Effect property" CompletionCategory.Value)
                | Some PdxShaderSyntax.ShaderNodeKind.Sampler, _
                | Some PdxShaderSyntax.ShaderNodeKind.Samplers, _ ->
                    samplerProperties |> List.map (fun value -> completionItem value "Sampler property" CompletionCategory.Value)
                | Some PdxShaderSyntax.ShaderNodeKind.BlendState, _ ->
                    blendProperties |> List.map (fun value -> completionItem value "BlendState property" CompletionCategory.Value)
                | Some PdxShaderSyntax.ShaderNodeKind.DepthStencilState, _ ->
                    depthStencilProperties |> List.map (fun value -> completionItem value "DepthStencilState property" CompletionCategory.Value)
                | Some PdxShaderSyntax.ShaderNodeKind.RasterizerState, _ ->
                    rasterizerProperties |> List.map (fun value -> completionItem value "RasterizerState property" CompletionCategory.Value)
                | Some PdxShaderSyntax.ShaderNodeKind.Includes, _ ->
                    includeNames |> Set.toList |> List.sort |> referenceValues "FX include"
                | _ -> snippets
            let propertyName =
                path
                |> List.rev
                |> List.tryPick (fun node -> if node.kind = PdxShaderSyntax.ShaderNodeKind.Property then node.name else None)
            match propertyName with
            | Some name when name.Equals("VertexShader", StringComparison.OrdinalIgnoreCase) ->
                declarationNames PdxShaderRuntime.VertexMainCodeDeclaration |> referenceValues "Vertex MainCode"
            | Some name when name.Equals("PixelShader", StringComparison.OrdinalIgnoreCase) ->
                declarationNames PdxShaderRuntime.PixelMainCodeDeclaration |> referenceValues "Pixel MainCode"
            | Some name when name.Equals("GeometryShader", StringComparison.OrdinalIgnoreCase) ->
                declarationNames PdxShaderRuntime.GeometryMainCodeDeclaration |> referenceValues "Geometry MainCode"
            | Some name when name.Equals("BlendState", StringComparison.OrdinalIgnoreCase) ->
                declarationNames PdxShaderRuntime.BlendStateDeclaration |> referenceValues "BlendState"
            | Some name when name.Equals("DepthStencilState", StringComparison.OrdinalIgnoreCase) ->
                declarationNames PdxShaderRuntime.DepthStencilStateDeclaration |> referenceValues "DepthStencilState"
            | Some name when name.Equals("RasterizerState", StringComparison.OrdinalIgnoreCase) ->
                declarationNames PdxShaderRuntime.RasterizerStateDeclaration |> referenceValues "RasterizerState"
            | Some name when name.Equals("ConstantBuffers", StringComparison.OrdinalIgnoreCase) ->
                declarationNames PdxShaderRuntime.ConstantBufferDeclaration |> referenceValues "ConstantBuffer"
            | Some name when name.Equals("Includes", StringComparison.OrdinalIgnoreCase) ->
                includeNames |> Set.toList |> List.sort |> referenceValues "FX include"
            | Some name when name.Equals("Defines", StringComparison.OrdinalIgnoreCase) ->
                conditionNames |> referenceValues "FX preprocessor define"
            | Some name ->
                propertyValues
                |> Map.tryPick (fun property values ->
                    if property.Equals(name, StringComparison.OrdinalIgnoreCase) then Some values else None)
                |> Option.map (List.map (fun value -> valueCompletion value (sprintf "%s value" name)))
                |> Option.defaultWith contextualCompletions
            | None -> contextualCompletions ()

    let completion (resourceManager: ResourceManager<_>) pos filepath filetext =
        completeFromResources (resourceManager.Api.GetResources()) pos filepath filetext

    // ------------------------------------------------------------------
    // Unified V2 LSP feature façade
    // ------------------------------------------------------------------

    type ShaderSignatureParameter =
        { label: string
          documentation: string option }

    type ShaderSignature =
        { label: string
          documentation: string option
          parameters: ShaderSignatureParameter list }

    type ShaderSignatureHelp =
        { signatures: ShaderSignature list
          activeSignature: int
          activeParameter: int }

    type ShaderSemanticToken =
        { span: PdxShaderSyntax.TextSpan
          tokenType: string
          declaration: bool
          readonly: bool
          inactive: bool }

    type ShaderInlayHint =
        { offset: int
          label: string }

    type ShaderRenameTarget =
        { name: string
          kind: string
          range: range
          edits: range list }

    let private snapshotView (resources: Resource seq) filepath filetext =
        let snapshots, current = collectSnapshots resources filepath filetext
        let unit = PdxShaderProject.buildCompileUnit snapshots current
        current, unit.effective |> List.map (fun snapshot -> snapshot, PdxShaderProject.semanticSnapshot snapshot)

    let rec private hlslTypeName =
        function
        | PdxShaderHlsl.VoidType -> "void"
        | PdxShaderHlsl.ScalarType kind -> sprintf "%A" kind |> fun value -> value.ToLowerInvariant()
        | PdxShaderHlsl.VectorType(kind, width) -> sprintf "%A%d" kind width |> fun value -> value.ToLowerInvariant()
        | PdxShaderHlsl.MatrixType(kind, rows, columns) -> sprintf "%A%dx%d" kind rows columns |> fun value -> value.ToLowerInvariant()
        | PdxShaderHlsl.ArrayType(item, length) -> sprintf "%s[%s]" (hlslTypeName item) (length |> Option.map string |> Option.defaultValue "")
        | PdxShaderHlsl.StructType name
        | PdxShaderHlsl.TextureType name
        | PdxShaderHlsl.SamplerType name
        | PdxShaderHlsl.UnknownType name -> name
        | PdxShaderHlsl.BufferType(name, item) ->
            item |> Option.map (fun value -> sprintf "%s<%s>" name (hlslTypeName value)) |> Option.defaultValue name
        | PdxShaderHlsl.ErrorType -> "<error>"

    let private spanContainsOffset (span: PdxShaderSyntax.TextSpan) offset =
        offset >= span.startOffset && offset <= span.endOffset

    let private hlslSymbolKindName =
        function
        | PdxShaderHlsl.TypeSymbol
        | PdxShaderHlsl.StructSymbol -> "type"
        | PdxShaderHlsl.FunctionSymbol -> "function"
        | PdxShaderHlsl.ParameterSymbol -> "parameter"
        | PdxShaderHlsl.FieldSymbol -> "property"
        | PdxShaderHlsl.MacroSymbol -> "macro"
        | _ -> "variable"

    let private hlslLocationsForTarget
        (views: (PdxShaderProject.ShaderSnapshot * PdxShaderProject.ShaderSemanticSnapshot) list)
        (targetName: string)
        (targetIds: Set<string>)
        =
        [ for snapshot, semantic in views do
              for symbol in semantic.hlsl.symbols do
                  if targetIds.Contains symbol.id || (targetIds.IsEmpty && symbol.name.Equals(targetName, StringComparison.OrdinalIgnoreCase)) then
                      yield rangeBetweenOffsets snapshot.displayPath snapshot.text symbol.selectionSpan.startOffset symbol.selectionSpan.endOffset

              for reference in semantic.hlsl.references do
                  if
                      (reference.candidateIds |> List.exists targetIds.Contains)
                      || (targetIds.IsEmpty && reference.name.Equals(targetName, StringComparison.OrdinalIgnoreCase))
                  then
                      yield rangeBetweenOffsets snapshot.displayPath snapshot.text reference.span.startOffset reference.span.endOffset ]

    let private outerDefinitions (snapshot: PdxShaderProject.ShaderSnapshot) =
        let semantic = PdxShaderProject.semanticSnapshot snapshot

        let kindName stage (node: PdxShaderSyntax.ShaderSyntaxNode) =
            match node.kind with
            | PdxShaderSyntax.ShaderNodeKind.Effect -> Some "effect"
            | PdxShaderSyntax.ShaderNodeKind.MainCode -> stage
            | PdxShaderSyntax.ShaderNodeKind.VertexStruct -> Some "struct"
            | PdxShaderSyntax.ShaderNodeKind.ConstantBuffer -> Some "constant_buffer"
            | PdxShaderSyntax.ShaderNodeKind.BlendState -> Some "blend_state"
            | PdxShaderSyntax.ShaderNodeKind.DepthStencilState -> Some "depth_stencil_state"
            | PdxShaderSyntax.ShaderNodeKind.RasterizerState -> Some "rasterizer_state"
            | PdxShaderSyntax.ShaderNodeKind.Sampler -> Some "sampler"
            | _ -> None

        let rec collect
            (stage: string option)
            (node: PdxShaderSyntax.ShaderSyntaxNode)
            : (string * string * PdxShaderSyntax.TextSpan) list =
            let nextStage =
                match node.kind with
                | PdxShaderSyntax.ShaderNodeKind.VertexShader -> Some "vertex_maincode"
                | PdxShaderSyntax.ShaderNodeKind.PixelShader -> Some "pixel_maincode"
                | PdxShaderSyntax.ShaderNodeKind.GeometryShader -> Some "geometry_maincode"
                | _ -> stage

            [ match node.name, node.nameSpan, kindName nextStage node with
              | Some name, Some nameSpan, Some kind -> yield kind, name, nameSpan
              | _ -> ()
              for child in node.children do
                  yield! collect nextStage child ]

        collect None semantic.syntax.root

    let referencesAt (resources: Resource seq) (pos: pos) filepath filetext : range list =
        let current, views = snapshotView resources filepath filetext
        let offset = offsetAt filetext pos
        let currentSemantic = PdxShaderProject.semanticSnapshot current
        let declarations = views |> List.collect (fun (snapshot, _) -> PdxShaderRuntime.declarationsFromSnapshot snapshot)
        let effectiveSnapshots = views |> List.map fst
        let semanticReferences =
            views
            |> List.collect (fun (snapshot, _) -> PdxShaderRuntime.semanticReferencesFromSnapshot snapshot)
            |> PdxShaderRuntime.resolveSemanticReferences effectiveSnapshots declarations
        let positionInRange (target: range) =
            let afterStart = int pos.Line > int target.StartLine || (pos.Line = target.StartLine && pos.Column >= target.StartColumn)
            let beforeEnd = int pos.Line < int target.EndLine || (pos.Line = target.EndLine && pos.Column <= target.EndColumn)
            afterStart && beforeEnd
        let hlslTarget =
            currentSemantic.hlsl.symbols
            |> List.tryFind (fun symbol -> spanContainsOffset symbol.selectionSpan offset)
            |> Option.map (fun symbol -> symbol.name, Set.singleton symbol.id)
            |> Option.orElseWith (fun () ->
                currentSemantic.hlsl.references
                |> List.tryFind (fun reference -> spanContainsOffset reference.span offset)
                |> Option.map (fun reference -> reference.name, Set.ofList reference.candidateIds))
        let declarationTarget =
            declarations
            |> List.tryFind (fun declaration -> PdxShaderProject.sameFilePath declaration.file filepath && positionInRange declaration.selectionRange)
            |> Option.map (fun declaration -> declaration.name, Set.singleton declaration.stableId)
        let semanticTarget =
            semanticReferences
            |> List.tryFind (fun reference -> PdxShaderProject.sameFilePath reference.file filepath && positionInRange reference.span)
            |> Option.map (fun reference -> reference.targetName, Set.ofList reference.targetIds)
        let target = hlslTarget |> Option.orElse declarationTarget |> Option.orElse semanticTarget
        let results =
            match target with
            | None -> []
            | Some(name, ids) ->
                let declarationRanges =
                    declarations
                    |> List.filter (fun declaration -> ids.Contains declaration.stableId || (ids.IsEmpty && declaration.name.Equals(name, StringComparison.OrdinalIgnoreCase)))
                    |> List.map _.selectionRange
                let referenceRanges =
                    semanticReferences
                    |> List.filter (fun reference ->
                        (reference.targetIds |> List.exists ids.Contains)
                        || (ids.IsEmpty && reference.targetName.Equals(name, StringComparison.OrdinalIgnoreCase)))
                    |> List.map _.span
                let runtimeRanges =
                    let effectIds =
                        declarations
                        |> List.filter (fun declaration -> declaration.kind = PdxShaderRuntime.EffectDeclaration && ids.Contains declaration.stableId)
                    if effectIds.IsEmpty then []
                    else
                        let model = PdxShaderRuntime.buildModel None resources [ filepath, filetext ]
                        PdxShaderRuntime.callersOf model name |> List.map _.span
                declarationRanges @ referenceRanges @ runtimeRanges

        results
        |> List.distinctBy (fun item -> PdxShaderProject.canonicalizePath item.FileName, item.StartLine, item.StartColumn, item.EndLine, item.EndColumn)
        |> List.sortBy (fun item -> PdxShaderProject.canonicalizePath item.FileName, item.StartLine, item.StartColumn)

    let private builtInSignatures (name: string) =
        let signature (result: string) (parameters: string list) (documentation: string) : ShaderSignature =
            { label = sprintf "%s %s(%s)" result name (String.concat ", " parameters)
              documentation = Some documentation
              parameters = parameters |> List.map (fun label -> { label = label; documentation = None }) }
        let scalar = "float"
        let vector (result: string) =
            let width =
                if result.EndsWith("4", StringComparison.Ordinal) then 4
                elif result.EndsWith("3", StringComparison.Ordinal) then 3
                elif result.EndsWith("2", StringComparison.Ordinal) then 2
                else 1
            let components = [ "x"; "y"; "z"; "w" ] |> List.take width |> List.map (sprintf "%s %s" scalar)
            [ signature result components "HLSL vector constructor"
              signature result [ sprintf "%s scalar" scalar ] "HLSL scalar-splat constructor" ]
        if hlslTypes |> List.exists (fun candidate -> candidate.Equals(name, StringComparison.OrdinalIgnoreCase)) then
            vector name
        else
            match name.ToLowerInvariant() with
            | "mul" ->
                [ signature "T" [ "T left"; "T right" ] "HLSL matrix/vector multiply"
                  signature "vector" [ "matrix left"; "vector right" ] "HLSL matrix-vector multiply" ]
            | "lerp" -> [ signature "T" [ "T x"; "T y"; "T amount" ] "Linear interpolation" ]
            | "saturate" -> [ signature "T" [ "T value" ] "Clamp to the inclusive 0..1 range" ]
            | "dot" -> [ signature scalar [ "vector left"; "vector right" ] "Vector dot product" ]
            | "cross" -> [ signature "float3" [ "float3 left"; "float3 right" ] "Vector cross product" ]
            | "normalize" -> [ signature "T" [ "T value" ] "Return a normalized vector" ]
            | "length" -> [ signature scalar [ "T value" ] "Return vector length" ]
            | "clamp" -> [ signature "T" [ "T value"; "T minimum"; "T maximum" ] "Clamp a value" ]
            | "min"
            | "max"
            | "pow" -> [ signature "T" [ "T left"; "T right" ] "HLSL intrinsic" ]
            | "tex2d" -> [ signature "float4" [ "sampler2D sampler"; "float2 uv" ] "Sample a 2D texture" ]
            | "tex2dlod" -> [ signature "float4" [ "sampler2D sampler"; "float4 uvLod" ] "Sample a 2D texture at an explicit LOD" ]
            | _ -> []

    let signatureHelpAt (resources: Resource seq) (pos: pos) filepath filetext : ShaderSignatureHelp option =
        let _, views = snapshotView resources filepath filetext
        let offset = offsetAt filetext pos
        let current = views |> List.tryFind (fun (snapshot, _) -> PdxShaderProject.sameFilePath snapshot.displayPath filepath)

        current
        |> Option.bind (fun (_, semantic) ->
            let calls =
                semantic.hlsl.references
                |> List.filter (fun reference ->
                    reference.kind = PdxShaderHlsl.CallReference
                    && reference.span.endOffset <= offset
                    && offset - reference.span.endOffset <= 512)
                |> List.sortByDescending (fun reference -> reference.span.endOffset)

            calls
            |> List.tryPick (fun call ->
                let tokens = semantic.syntax.tokens
                let openParen =
                    tokens
                    |> Array.tryFindIndex (fun token ->
                        token.span.startOffset >= call.span.endOffset
                        && token.span.startOffset <= offset
                        && token.kind = PdxShaderSyntax.ShaderTokenKind.OpenParen)

                openParen
                |> Option.bind (fun openIndex ->
                    let mutable depth = 0
                    let mutable activeParameter = 0
                    let mutable closed = false
                    let mutable index = openIndex

                    while index < tokens.Length && tokens[index].span.startOffset <= offset && not closed do
                        match tokens[index].kind with
                        | PdxShaderSyntax.ShaderTokenKind.OpenParen -> depth <- depth + 1
                        | PdxShaderSyntax.ShaderTokenKind.CloseParen ->
                            depth <- depth - 1
                            if depth <= 0 && tokens[index].span.startOffset < offset then closed <- true
                        | PdxShaderSyntax.ShaderTokenKind.Comma when depth = 1 -> activeParameter <- activeParameter + 1
                        | _ -> ()
                        index <- index + 1

                    if closed then None
                    else
                        let functions =
                            views
                            |> List.collect (fun (_, view) -> view.hlsl.symbols)
                            |> List.filter (fun symbol ->
                                symbol.kind = PdxShaderHlsl.FunctionSymbol
                                && ((call.candidateIds |> List.contains symbol.id)
                                    || (call.candidateIds.IsEmpty && symbol.name.Equals(call.name, StringComparison.OrdinalIgnoreCase))))
                            |> List.distinctBy _.id

                        let signatures =
                            if functions.IsEmpty then
                                builtInSignatures call.name
                            else
                                functions
                                |> List.map (fun symbol ->
                                    let parameters =
                                        symbol.parameters
                                        |> List.map (fun parameter ->
                                            { label = sprintf "%s %s" (hlslTypeName parameter.parameterType) parameter.name
                                              documentation = parameter.semantic |> Option.map (sprintf "Semantic: %s") })
                                    { label = sprintf "%s %s(%s)" (hlslTypeName symbol.symbolType) symbol.name (parameters |> List.map _.label |> String.concat ", ")
                                      documentation = Some(sprintf "Stage: %A; condition: %A" symbol.stage symbol.condition)
                                      parameters = parameters })

                        if signatures.IsEmpty then None
                        else
                            Some
                                { signatures = signatures
                                  activeSignature = 0
                                  activeParameter = min activeParameter (max 0 (signatures.Head.parameters.Length - 1)) })))

    let semanticTokens filepath filetext : ShaderSemanticToken list =
        let snapshot = PdxShaderProject.createSnapshot PdxShaderProject.CurrentDocument filepath filepath filetext
        let semantic = PdxShaderProject.semanticSnapshot snapshot
        let symbolBySpan = System.Collections.Generic.Dictionary<struct (int * int), _>()
        for symbol in semantic.hlsl.symbols do
            let span = symbol.selectionSpan
            let key = struct (span.startOffset, span.Length)
            if not (symbolBySpan.ContainsKey key) then
                symbolBySpan[key] <- symbol
        let directX = PdxShaderPreprocessor.defaultPlatformVariants |> List.find (fun variant -> variant.name = "directx11")

        semantic.syntax.tokens
        |> Array.choose (fun token ->
            if token.span.Length <= 0 then None
            else
                let symbol =
                    match symbolBySpan.TryGetValue(struct (token.span.startOffset, token.span.Length)) with
                    | true, symbol -> Some symbol
                    | _ -> None
                let tokenType, declaration, readonly =
                    match symbol with
                    | Some value -> hlslSymbolKindName value.kind, true, value.kind = PdxShaderHlsl.MacroSymbol
                    | None ->
                        match token.kind with
                        | PdxShaderSyntax.ShaderTokenKind.LineComment
                        | PdxShaderSyntax.ShaderTokenKind.BlockComment -> "comment", false, false
                        | PdxShaderSyntax.ShaderTokenKind.StringLiteral -> "string", false, false
                        | PdxShaderSyntax.ShaderTokenKind.NumberLiteral -> "number", false, false
                        | PdxShaderSyntax.ShaderTokenKind.DirectiveLine -> "macro", false, true
                        | PdxShaderSyntax.ShaderTokenKind.Identifier ->
                            if token.text.Equals("Effect", StringComparison.OrdinalIgnoreCase)
                               || token.text.EndsWith("Shader", StringComparison.OrdinalIgnoreCase)
                               || token.text.Equals("MainCode", StringComparison.OrdinalIgnoreCase)
                            then "keyword", false, false
                            else "variable", false, false
                        | PdxShaderSyntax.ShaderTokenKind.Equals
                        | PdxShaderSyntax.ShaderTokenKind.Colon
                        | PdxShaderSyntax.ShaderTokenKind.Comma
                        | PdxShaderSyntax.ShaderTokenKind.Semicolon -> "operator", false, false
                        | _ -> "", false, false

                if String.IsNullOrEmpty tokenType then None
                else
                    let condition = PdxShaderPreprocessor.conditionAt token.span.startOffset semantic.preprocessor
                    let inactive = (PdxShaderPreprocessor.evaluate directX.environment condition) = PdxShaderPreprocessor.ConditionFalse
                    Some
                        { span = token.span
                          tokenType = tokenType
                          declaration = declaration
                          readonly = readonly
                          inactive = inactive })
        |> Array.toList

    let inlayHints filepath filetext : ShaderInlayHint list =
        let snapshot = PdxShaderProject.createSnapshot PdxShaderProject.CurrentDocument filepath filepath filetext
        let semantic = PdxShaderProject.semanticSnapshot snapshot

        semantic.hlsl.symbols
        |> List.choose (fun symbol ->
            match symbol.kind, symbol.symbolType with
            | (PdxShaderHlsl.LocalVariableSymbol | PdxShaderHlsl.GlobalVariableSymbol | PdxShaderHlsl.ParameterSymbol), PdxShaderHlsl.UnknownType _ -> None
            | (PdxShaderHlsl.LocalVariableSymbol | PdxShaderHlsl.GlobalVariableSymbol | PdxShaderHlsl.ParameterSymbol), symbolType ->
                Some { offset = symbol.selectionSpan.endOffset; label = sprintf ": %s" (hlslTypeName symbolType) }
            | _ -> None)

    let foldingRanges filepath filetext : range list =
        let snapshot = PdxShaderProject.createSnapshot PdxShaderProject.CurrentDocument filepath filepath filetext
        let semantic = PdxShaderProject.semanticSnapshot snapshot
        let rec collect (node: PdxShaderSyntax.ShaderSyntaxNode) : range list =
            [ let nodeRange = rangeBetweenOffsets filepath filetext node.span.startOffset node.span.endOffset
              if nodeRange.EndLine > nodeRange.StartLine then yield nodeRange
              for child in node.children do yield! collect child ]
        collect semantic.syntax.root

    let selectionRangesAt (pos: pos) filepath filetext : range list =
        let snapshot = PdxShaderProject.createSnapshot PdxShaderProject.CurrentDocument filepath filepath filetext
        let semantic = PdxShaderProject.semanticSnapshot snapshot
        let offset = offsetAt filetext pos
        let rec containing (node: PdxShaderSyntax.ShaderSyntaxNode) : range list =
            if not (spanContainsOffset node.span offset) then []
            else
                let child = node.children |> List.tryPick (fun item -> let nested = containing item in if nested.IsEmpty then None else Some nested)
                (child |> Option.defaultValue []) @ [ rangeBetweenOffsets filepath filetext node.span.startOffset node.span.endOffset ]
        containing semantic.syntax.root

    let formatDocument insertSpaces tabSize filepath filetext =
        let snapshot = PdxShaderProject.createSnapshot PdxShaderProject.CurrentDocument filepath filepath filetext
        let semantic = PdxShaderProject.semanticSnapshot snapshot
        let hlslSpans =
            let rec collect (node: PdxShaderSyntax.ShaderSyntaxNode) : PdxShaderSyntax.TextSpan list =
                [ if node.kind = PdxShaderSyntax.ShaderNodeKind.HlslRegion then yield node.span
                  for child in node.children do yield! collect child ]
            collect semantic.syntax.root
        let insideHlsl offset = hlslSpans |> List.exists (fun span -> spanContainsOffset span offset)
        let indent depth = if insertSpaces then String(' ', max 1 tabSize * depth) else String('\t', depth)
        let lines = filetext.Replace("\r\n", "\n").Split('\n')
        let lineStarts = ResizeArray<int>()
        let mutable running = 0
        for line in lines do
            lineStarts.Add running
            running <- running + line.Length + 1
        let mutable depth = 0
        let formatted =
            lines
            |> Array.mapi (fun lineIndex line ->
                let start = lineStarts[lineIndex]
                let trimmed = line.TrimStart(' ', '\t')
                let firstOffset = start + (line.Length - trimmed.Length)
                if String.IsNullOrWhiteSpace line || insideHlsl firstOffset || trimmed.StartsWith("#") || trimmed.StartsWith("@") then line
                else
                    let lineTokens =
                        semantic.syntax.tokens
                        |> Array.filter (fun token -> token.span.startOffset >= start && token.span.startOffset < start + line.Length)
                    let closesFirst = lineTokens |> Array.tryFind (fun token -> token.kind <> PdxShaderSyntax.ShaderTokenKind.Whitespace) |> Option.exists (fun token -> token.kind = PdxShaderSyntax.ShaderTokenKind.CloseBrace)
                    let lineDepth = if closesFirst then max 0 (depth - 1) else depth
                    let result = indent lineDepth + trimmed
                    for token in lineTokens do
                        if not (insideHlsl token.span.startOffset) then
                            match token.kind with
                            | PdxShaderSyntax.ShaderTokenKind.OpenBrace -> depth <- depth + 1
                            | PdxShaderSyntax.ShaderTokenKind.CloseBrace -> depth <- max 0 (depth - 1)
                            | _ -> ()
                    result)
        let newline = if filetext.Contains("\r\n") then "\r\n" else "\n"
        String.Join(newline, formatted)

    let renameTargetAt (resources: Resource seq) (pos: pos) filepath filetext : ShaderRenameTarget option =
        let current, _ = snapshotView resources filepath filetext
        let semantic = PdxShaderProject.semanticSnapshot current
        let offset = offsetAt filetext pos
        let hlsl =
            semantic.hlsl.symbols
            |> List.tryFind (fun symbol -> spanContainsOffset symbol.selectionSpan offset)
            |> Option.map (fun symbol -> symbol.name, hlslSymbolKindName symbol.kind, symbol.selectionSpan)
            |> Option.orElseWith (fun () ->
                semantic.hlsl.references
                |> List.tryFind (fun reference -> spanContainsOffset reference.span offset)
                |> Option.map (fun reference -> reference.name, "hlsl_reference", reference.span))
        let outer =
            outerDefinitions current
            |> List.tryFind (fun (_, _, span) -> spanContainsOffset span offset)
            |> Option.map (fun (kind, name, span) -> name, kind, span)
        (hlsl |> Option.orElse outer)
        |> Option.map (fun (name, kind, span) ->
            { name = name
              kind = kind
              range = rangeBetweenOffsets filepath filetext span.startOffset span.endOffset
              edits = referencesAt resources pos filepath filetext })
