namespace CWTools.Games

open System
open System.IO
open System.Text.RegularExpressions
open CWTools.Common
open CWTools.Utilities.Position

/// Lightweight language features for the Paradox FX shader DSL.
///
/// FX files are not Clausewitz script files, but they still need to participate in
/// the same resource cache and LSP entry points as the rest of CWTools. This module
/// deliberately extracts only the DSL surface needed for validation and completion;
/// HLSL bodies inside [[ ... ]] are treated as opaque text.
module PdxShaderFeatures =
    type ShaderSource =
        { filepath: string
          logicalpath: string
          filetext: string }

    type ShaderSymbols =
        { vertexMainCodes: Set<string>
          pixelMainCodes: Set<string>
          constantBuffers: Set<string>
          blendStates: Set<string>
          depthStencilStates: Set<string>
          rasterizerStates: Set<string>
          defines: Set<string>
          includeFiles: Set<string> }

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

    type private ShaderBlock =
        { name: string option
          headerStart: int
          blockStart: int
          blockEnd: int
          nameStart: int option
          nameLength: int
          contentStart: int
          contentEnd: int }

    type private ReferenceKind =
        | VertexMainCode
        | PixelMainCode
        | ConstantBuffer
        | BlendState
        | DepthStencilState
        | RasterizerState
        | IncludeFile

    type private ShaderReference =
        { owner: string
          target: string
          targetStart: int
          targetLength: int
          kind: ReferenceKind }

    type private ShaderDefinition =
        { name: string
          kind: ReferenceKind
          source: ShaderSource
          nameStart: int
          nameLength: int
          detail: string }

    type private ScopeContext =
        { headers: string list
          insideHlsl: bool }

    let private regex options pattern = Regex(pattern, options ||| RegexOptions.Compiled)
    let private keywordOptions = RegexOptions.IgnoreCase ||| RegexOptions.Singleline
    let private singlelineOptions = RegexOptions.Singleline

    let private vertexShaderBlockPattern =
        regex keywordOptions @"\bVertexShader\s*=\s*\{"

    let private pixelShaderBlockPattern =
        regex keywordOptions @"\bPixelShader\s*=\s*\{"

    let private vertexStructBlockPattern =
        regex keywordOptions @"\bVertexStruct\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{"

    let private constantBufferBlockPattern =
        regex keywordOptions @"\bConstantBuffer\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)[^)]*\)\s*\{"

    let private effectBlockPattern =
        regex keywordOptions @"\bEffect\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{"

    let private blendStateBlockPattern =
        regex keywordOptions @"\bBlendState\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{"

    let private depthStencilStateBlockPattern =
        regex keywordOptions @"\bDepthStencilState\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{"

    let private rasterizerStateBlockPattern =
        regex keywordOptions @"\bRasterizerState\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{"

    let private samplersBlockPattern =
        regex keywordOptions @"\bSamplers\s*=\s*\{"

    let private samplerBlockPattern =
        regex keywordOptions @"\b([A-Za-z_][A-Za-z0-9_]*)\s*=\s*\{"

    let private codeBlockPattern =
        regex keywordOptions @"\bCode\s*\[\["

    let private mainCodePattern =
        regex keywordOptions @"\bMainCode\s+([A-Za-z_][A-Za-z0-9_]*)\b"

    let private constantBufferPattern =
        regex keywordOptions @"\bConstantBuffer\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)"

    let private blendStatePattern =
        regex keywordOptions @"\bBlendState\s+([A-Za-z_][A-Za-z0-9_]*)\b"

    let private depthStencilStatePattern =
        regex keywordOptions @"\bDepthStencilState\s+([A-Za-z_][A-Za-z0-9_]*)\b"

    let private rasterizerStatePattern =
        regex keywordOptions @"\bRasterizerState\s+([A-Za-z_][A-Za-z0-9_]*)\b"

    let private effectPropertyPattern =
        regex keywordOptions @"\b(VertexShader|PixelShader|BlendState|DepthStencilState|RasterizerState)\s*=\s*""([^""]+)"""

    let private constantBufferReferencePattern =
        regex keywordOptions @"\bConstantBuffers\s*=\s*\{([^}]*)\}"

    let private includesPattern =
        regex keywordOptions @"\bIncludes\s*=\s*\{([^}]*)\}"

    let private definesPattern =
        regex keywordOptions @"\bDefines\s*=\s*\{([^}]*)\}"

    let private identifierPattern =
        regex RegexOptions.None @"[A-Za-z_][A-Za-z0-9_]*"

    let private quotedValuePattern =
        regex RegexOptions.None @"""([^""]+)"""

    let private conditionalDefinePattern =
        regex (RegexOptions.IgnoreCase ||| RegexOptions.Multiline) @"(?:@|#)\s*ifn?def\s+([A-Za-z_][A-Za-z0-9_]*)\b"

    let private definedCallPattern =
        regex (RegexOptions.IgnoreCase ||| RegexOptions.Multiline) @"\bdefined\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)"

    let private recentWindowSize = 16 * 1024

    let private emptySymbols =
        { vertexMainCodes = Set.empty
          pixelMainCodes = Set.empty
          constantBuffers = Set.empty
          blendStates = Set.empty
          depthStencilStates = Set.empty
          rasterizerStates = Set.empty
          defines = Set.empty
          includeFiles = Set.empty }

    let isShaderFile (filepath: string) =
        let extension = Path.GetExtension(filepath)
        extension.Equals(".shader", StringComparison.OrdinalIgnoreCase)
        || extension.Equals(".fxh", StringComparison.OrdinalIgnoreCase)

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
            vanillaFxSources <-
                allFiles
                |> Array.choose (fun fp ->
                    try
                        Some
                            { filepath = fp
                              logicalpath = fp
                              filetext = File.ReadAllText fp }
                    with _ -> None)
                |> Array.toList
        with _ -> ()

    let private fileName (path: string) =
        let normalized = path.Replace('\\', '/')
        let lastSlash = normalized.LastIndexOf('/')
        if lastSlash >= 0 then normalized.Substring(lastSlash + 1) else normalized

    let private blankNonNewline (chars: char array) i =
        if chars[i] <> '\r' && chars[i] <> '\n' then chars[i] <- ' '

    /// Keep string offsets stable while removing comments, preprocessors and embedded HLSL.
    let private cleanDslText (text: string) =
        let chars = text.ToCharArray()
        let mutable i = 0
        let mutable inString = false

        let blankUntilLineEnd start =
            let mutable j = start
            while j < chars.Length && chars[j] <> '\r' && chars[j] <> '\n' do
                blankNonNewline chars j
                j <- j + 1
            j

        while i < chars.Length do
            if not inString && i + 1 < chars.Length && chars[i] = '[' && chars[i + 1] = '[' then
                blankNonNewline chars i
                blankNonNewline chars (i + 1)
                i <- i + 2
                let mutable doneHlsl = false

                while i < chars.Length && not doneHlsl do
                    if i + 1 < chars.Length && chars[i] = ']' && chars[i + 1] = ']' then
                        blankNonNewline chars i
                        blankNonNewline chars (i + 1)
                        i <- i + 2
                        doneHlsl <- true
                    else
                        blankNonNewline chars i
                        i <- i + 1
            elif not inString && i + 1 < chars.Length && chars[i] = '/' && chars[i + 1] = '*' then
                blankNonNewline chars i
                blankNonNewline chars (i + 1)
                i <- i + 2
                let mutable doneComment = false

                while i < chars.Length && not doneComment do
                    if i + 1 < chars.Length && chars[i] = '*' && chars[i + 1] = '/' then
                        blankNonNewline chars i
                        blankNonNewline chars (i + 1)
                        i <- i + 2
                        doneComment <- true
                    else
                        blankNonNewline chars i
                        i <- i + 1
            elif not inString && i + 1 < chars.Length && chars[i] = '/' && chars[i + 1] = '/' then
                i <- blankUntilLineEnd i
            elif not inString && chars[i] = '#' then
                i <- blankUntilLineEnd i
            else
                if chars[i] = '"' then inString <- not inString
                i <- i + 1

        String(chars)

    let private findOpenBrace (m: Match) =
        m.Index + m.Value.LastIndexOf('{')

    let private findClosingBrace (cleaned: string) openBrace =
        let mutable depth = 0
        let mutable i = openBrace
        let mutable closing = cleaned.Length

        while i < cleaned.Length && closing = cleaned.Length do
            match cleaned[i] with
            | '{' -> depth <- depth + 1
            | '}' ->
                depth <- depth - 1
                if depth = 0 then closing <- i
            | _ -> ()

            i <- i + 1

        closing

    let private findBlocks (pattern: Regex) includeName (cleaned: string) =
        pattern.Matches(cleaned)
        |> Seq.cast<Match>
        |> Seq.choose (fun m ->
            let openBrace = findOpenBrace m
            if openBrace < m.Index then
                None
            else
                let closeBrace = findClosingBrace cleaned openBrace
                let nameGroup =
                    if includeName && m.Groups.Count > 1 && m.Groups[1].Success then
                        Some m.Groups[1]
                    else
                        None

                Some
                    { name =
                        nameGroup |> Option.map _.Value
                      headerStart = m.Index
                      blockStart = m.Index
                      blockEnd = if closeBrace < cleaned.Length then closeBrace + 1 else closeBrace
                      nameStart = nameGroup |> Option.map _.Index
                      nameLength = nameGroup |> Option.map _.Length |> Option.defaultValue 0
                      contentStart = openBrace + 1
                      contentEnd = closeBrace })
        |> Seq.toList

    let private matchNames (pattern: Regex) (text: string) =
        pattern.Matches(text)
        |> Seq.cast<Match>
        |> Seq.choose (fun m ->
            if m.Groups.Count > 1 && m.Groups[1].Success then Some m.Groups[1].Value else None)
        |> Set.ofSeq

    let private shaderBlockMainCodes (pattern: Regex) (cleaned: string) =
        findBlocks pattern false cleaned
        |> Seq.collect (fun block ->
            let length = max 0 (block.contentEnd - block.contentStart)
            mainCodePattern.Matches(cleaned.Substring(block.contentStart, length))
            |> Seq.cast<Match>
            |> Seq.choose (fun m ->
                if m.Groups.Count > 1 && m.Groups[1].Success then Some m.Groups[1].Value else None))
        |> Set.ofSeq

    let private shaderDefineNames (rawText: string) (cleaned: string) =
        seq {
            yield! matchNames conditionalDefinePattern rawText
            yield! matchNames definedCallPattern rawText

            for m in definesPattern.Matches(cleaned) |> Seq.cast<Match> do
                let values = m.Groups[1]

                for value in quotedValuePattern.Matches(values.Value) |> Seq.cast<Match> do
                    let define = value.Groups[1]
                    if define.Success then yield define.Value
        }
        |> Set.ofSeq

    let private extractSymbolsFromText (source: ShaderSource) =
        let cleaned = cleanDslText source.filetext

        { vertexMainCodes = shaderBlockMainCodes vertexShaderBlockPattern cleaned
          pixelMainCodes = shaderBlockMainCodes pixelShaderBlockPattern cleaned
          constantBuffers = matchNames constantBufferPattern cleaned
          blendStates = matchNames blendStatePattern cleaned
          depthStencilStates = matchNames depthStencilStatePattern cleaned
          rasterizerStates = matchNames rasterizerStatePattern cleaned
          defines = shaderDefineNames source.filetext cleaned
          includeFiles =
            if String.IsNullOrWhiteSpace source.filepath then
                Set.empty
            else
                Set.singleton (fileName source.filepath) }

    let private mergeSymbols a b =
        { vertexMainCodes = Set.union a.vertexMainCodes b.vertexMainCodes
          pixelMainCodes = Set.union a.pixelMainCodes b.pixelMainCodes
          constantBuffers = Set.union a.constantBuffers b.constantBuffers
          blendStates = Set.union a.blendStates b.blendStates
          depthStencilStates = Set.union a.depthStencilStates b.depthStencilStates
          rasterizerStates = Set.union a.rasterizerStates b.rasterizerStates
          defines = Set.union a.defines b.defines
          includeFiles = Set.union a.includeFiles b.includeFiles }

    let symbolsFromSources sources =
        sources |> Seq.map extractSymbolsFromText |> Seq.fold mergeSymbols emptySymbols

    let private sourceForCurrentFile filepath filetext =
        { filepath = filepath
          logicalpath = filepath
          filetext = filetext }

    let private resourceSources (resources: IResourceAPI<_>) filepath filetext =
        let currentPath =
            try Path.GetFullPath filepath
            with _ -> filepath

        resources.GetResources()
        |> Seq.choose (function
            | FileWithContentResource(_, resource) when
                resource.overwrite <> Overwrite.Overwritten
                && isShaderFile resource.filepath
                ->
                let candidatePath =
                    try Path.GetFullPath resource.filepath
                    with _ -> resource.filepath

                if candidatePath.Equals(currentPath, StringComparison.OrdinalIgnoreCase) then
                    None
                else
                    Some
                        { filepath = resource.filepath
                          logicalpath = resource.logicalpath
                          filetext = resource.filetext }
            | FileResource(_, resource) when isShaderFile resource.filepath ->
                let candidatePath =
                    try Path.GetFullPath resource.filepath
                    with _ -> resource.filepath

                if candidatePath.Equals(currentPath, StringComparison.OrdinalIgnoreCase) then
                    None
                else
                    try
                        if File.Exists resource.filepath then
                            Some
                                { filepath = resource.filepath
                                  logicalpath = resource.logicalpath
                                  filetext = File.ReadAllText resource.filepath }
                        else
                            None
                    with _ -> None
            | _ -> None)
        |> Seq.append [ sourceForCurrentFile filepath filetext ]
        |> Seq.append (
            vanillaFxSources
            |> List.filter (fun s ->
                let sp =
                    try Path.GetFullPath s.filepath
                    with _ -> s.filepath
                not (sp.Equals(currentPath, StringComparison.OrdinalIgnoreCase))))
        |> Seq.toList

    let private resourceIncludeNames (resources: IResourceAPI<_>) =
        let fromResources =
            resources.GetResources()
            |> Seq.choose (function
                | FileResource(_, resource) when isShaderFile resource.filepath -> Some(fileName resource.filepath)
                | FileWithContentResource(_, resource) when
                    resource.overwrite <> Overwrite.Overwritten
                    && isShaderFile resource.filepath
                    ->
                    Some(fileName resource.filepath)
                | _ -> None)
            |> Set.ofSeq
        let fromVanilla =
            vanillaFxSources |> List.map (fun s -> fileName s.filepath) |> Set.ofList
        Set.union fromResources fromVanilla

    let private symbolsWithIncludeNames sources includeNames =
        let symbols = symbolsFromSources sources
        { symbols with includeFiles = Set.union symbols.includeFiles includeNames }

    let private posFromOffset (text: string) offset =
        let targetOffset = max 0 (min text.Length offset)
        let mutable line = 1
        let mutable column = 0
        let mutable i = 0

        while i < targetOffset do
            if text[i] = '\n' then
                line <- line + 1
                column <- 0
            elif text[i] <> '\r' then
                column <- column + 1

            i <- i + 1

        mkPos line column

    let private rangeBetweenOffsets filepath (text: string) startOffset endOffset =
        mkRange filepath (posFromOffset text startOffset) (posFromOffset text endOffset)

    let private rangeFromOffset filepath (text: string) offset length =
        rangeBetweenOffsets filepath text offset (offset + max 1 length)

    let private definitionRange definition =
        if definition.kind = IncludeFile then
            mkRange definition.source.filepath pos0 pos0
        else
            rangeFromOffset definition.source.filepath definition.source.filetext definition.nameStart definition.nameLength

    let private addMainCodeDefinitions kind detail source cleaned (definitions: ResizeArray<ShaderDefinition>) pattern =
        for block in findBlocks pattern false cleaned do
            let blockLength = max 0 (block.contentEnd - block.contentStart)
            let content = cleaned.Substring(block.contentStart, blockLength)

            for m in mainCodePattern.Matches(content) |> Seq.cast<Match> do
                let name = m.Groups[1]

                if name.Success then
                    definitions.Add
                        { name = name.Value
                          kind = kind
                          source = source
                          nameStart = block.contentStart + name.Index
                          nameLength = name.Length
                          detail = detail }

    let private addNamedDefinitions kind detail source (definitions: ResizeArray<ShaderDefinition>) (pattern: Regex) cleaned =
        for m in pattern.Matches(cleaned) |> Seq.cast<Match> do
            let name = m.Groups[1]

            if name.Success then
                definitions.Add
                    { name = name.Value
                      kind = kind
                      source = source
                      nameStart = name.Index
                      nameLength = name.Length
                      detail = detail }

    let private definitionsFromSource source =
        let cleaned = cleanDslText source.filetext
        let definitions = ResizeArray<ShaderDefinition>()

        addMainCodeDefinitions VertexMainCode "Vertex MainCode" source cleaned definitions vertexShaderBlockPattern
        addMainCodeDefinitions PixelMainCode "Pixel MainCode" source cleaned definitions pixelShaderBlockPattern
        addNamedDefinitions ConstantBuffer "ConstantBuffer" source definitions constantBufferPattern cleaned
        addNamedDefinitions BlendState "BlendState" source definitions blendStatePattern cleaned
        addNamedDefinitions DepthStencilState "DepthStencilState" source definitions depthStencilStatePattern cleaned
        addNamedDefinitions RasterizerState "RasterizerState" source definitions rasterizerStatePattern cleaned

        if not (String.IsNullOrWhiteSpace source.filepath) then
            definitions.Add
                { name = fileName source.filepath
                  kind = IncludeFile
                  source = source
                  nameStart = 0
                  nameLength = 0
                  detail = "FX include file" }

        definitions |> Seq.toList

    let private definitionsFromSources (sources: ShaderSource list) =
        sources |> List.collect definitionsFromSource

    let private symbol
        (filepath: string)
        (filetext: string)
        kind
        name
        detail
        startOffset
        endOffset
        selectionStart
        selectionLength
        children
        : ShaderDocumentSymbol =
        { name = name
          detail = detail
          kind = kind
          range = rangeBetweenOffsets filepath filetext startOffset endOffset
          selectionRange = rangeFromOffset filepath filetext selectionStart selectionLength
          children = children }

    let private blockSymbol filepath filetext kind (fallbackName: string) detail children (block: ShaderBlock) =
        let selectionStart = block.nameStart |> Option.defaultValue block.headerStart
        let selectionLength =
            if block.nameLength > 0 then
                block.nameLength
            else
                fallbackName.Length

        symbol
            filepath
            filetext
            kind
            (block.name |> Option.defaultValue fallbackName)
            detail
            block.blockStart
            block.blockEnd
            selectionStart
            selectionLength
            children

    let private mainCodeSymbols filepath filetext (cleaned: string) (block: ShaderBlock) =
        let blockLength = max 0 (block.contentEnd - block.contentStart)
        let content = cleaned.Substring(block.contentStart, blockLength)

        mainCodePattern.Matches(content)
        |> Seq.cast<Match>
        |> Seq.choose (fun m ->
            let name = m.Groups[1]

            if name.Success then
                let nameStart = block.contentStart + name.Index
                let startOffset = block.contentStart + m.Index

                Some(
                    symbol
                        filepath
                        filetext
                        MainCodeSymbol
                        name.Value
                        "MainCode"
                        startOffset
                        (nameStart + name.Length)
                        nameStart
                        name.Length
                        []
                )
            else
                None)
        |> Seq.toList

    let private includeSymbols filepath filetext (cleaned: string) =
        includesPattern.Matches(cleaned)
        |> Seq.cast<Match>
        |> Seq.map (fun m ->
            let values = m.Groups[1]

            let children =
                quotedValuePattern.Matches(values.Value)
                |> Seq.cast<Match>
                |> Seq.choose (fun quoted ->
                    let name = quoted.Groups[1]

                    if name.Success then
                        let nameStart = values.Index + name.Index

                        Some(
                            symbol
                                filepath
                                filetext
                                IncludeFileSymbol
                                name.Value
                                "FX include"
                                nameStart
                                (nameStart + name.Length)
                                nameStart
                                name.Length
                                []
                        )
                    else
                        None)
                |> Seq.toList

            symbol
                filepath
                filetext
                IncludesSymbol
                "Includes"
                "FX include list"
                m.Index
                (m.Index + m.Length)
                m.Index
                "Includes".Length
                children)
        |> Seq.toList

    let private codeSymbols filepath (filetext: string) (cleaned: string) =
        codeBlockPattern.Matches(cleaned)
        |> Seq.cast<Match>
        |> Seq.map (fun m ->
            let codeEnd = filetext.IndexOf("]]", m.Index + m.Length, StringComparison.Ordinal)
            let endOffset = if codeEnd < 0 then filetext.Length else codeEnd + 2

            symbol
                filepath
                filetext
                CodeBlockSymbol
                "Code"
                "Shared HLSL"
                m.Index
                endOffset
                m.Index
                "Code".Length
                [])
        |> Seq.toList

    let private samplerSymbols filepath filetext (cleaned: string) =
        findBlocks samplersBlockPattern false cleaned
        |> List.map (fun (samplers: ShaderBlock) ->
            let blockLength = max 0 (samplers.contentEnd - samplers.contentStart)
            let content = cleaned.Substring(samplers.contentStart, blockLength)

            let children =
                samplerBlockPattern.Matches(content)
                |> Seq.cast<Match>
                |> Seq.choose (fun m ->
                    let name = m.Groups[1]

                    if name.Success then
                        let blockStart = samplers.contentStart + m.Index
                        let openBrace = blockStart + m.Value.LastIndexOf('{')
                        let closeBrace = findClosingBrace cleaned openBrace
                        let nameStart = samplers.contentStart + name.Index

                        Some(
                            symbol
                                filepath
                                filetext
                                SamplerSymbol
                                name.Value
                                "Sampler"
                                blockStart
                                (if closeBrace < cleaned.Length then closeBrace + 1 else closeBrace)
                                nameStart
                                name.Length
                                []
                        )
                    else
                        None)
                |> Seq.toList

            blockSymbol filepath filetext SamplersSymbol "Samplers" "Sampler list" children samplers)

    let documentSymbols (filepath: string) (filetext: string) =
        let cleaned = cleanDslText filetext

        [ yield! includeSymbols filepath filetext cleaned
          yield!
              findBlocks vertexStructBlockPattern true cleaned
              |> List.map (fun block ->
                  blockSymbol filepath filetext VertexStructSymbol "VertexStruct" "Vertex struct" [] block)
          yield!
              findBlocks constantBufferBlockPattern true cleaned
              |> List.map (fun block ->
                  blockSymbol filepath filetext ConstantBufferSymbol "ConstantBuffer" "ConstantBuffer" [] block)
          yield!
              findBlocks vertexShaderBlockPattern false cleaned
              |> List.map (fun block ->
                  blockSymbol
                      filepath
                      filetext
                      ShaderBlockSymbol
                      "VertexShader"
                      "Vertex shader block"
                      (mainCodeSymbols filepath filetext cleaned block)
                      block)
          yield!
              findBlocks pixelShaderBlockPattern false cleaned
              |> List.map (fun block ->
                  blockSymbol
                      filepath
                      filetext
                      ShaderBlockSymbol
                      "PixelShader"
                      "Pixel shader block"
                      (mainCodeSymbols filepath filetext cleaned block)
                      block)
          yield!
              findBlocks effectBlockPattern true cleaned
              |> List.map (fun block ->
                  blockSymbol filepath filetext EffectSymbol "Effect" "Effect" [] block)
          yield!
              findBlocks blendStateBlockPattern true cleaned
              |> List.map (fun block ->
                  blockSymbol filepath filetext BlendStateSymbol "BlendState" "BlendState" [] block)
          yield!
              findBlocks depthStencilStateBlockPattern true cleaned
              |> List.map (fun block ->
                  blockSymbol
                      filepath
                      filetext
                      DepthStencilStateSymbol
                      "DepthStencilState"
                      "DepthStencilState"
                      []
                      block)
          yield!
              findBlocks rasterizerStateBlockPattern true cleaned
              |> List.map (fun block ->
                  blockSymbol
                      filepath
                      filetext
                      RasterizerStateSymbol
                      "RasterizerState"
                      "RasterizerState"
                      []
                      block)
          yield! samplerSymbols filepath filetext cleaned
          yield! codeSymbols filepath filetext cleaned ]
        |> List.sortBy (fun item -> item.range.StartLine, item.range.StartColumn)

    let private referencesFromText (text: string) =
        let cleaned = cleanDslText text
        let references = ResizeArray<ShaderReference>()

        for block in findBlocks effectBlockPattern true cleaned do
            let blockLength = max 0 (block.contentEnd - block.contentStart)
            let content = cleaned.Substring(block.contentStart, blockLength)
            let owner = block.name |> Option.defaultValue "Effect"

            for m in effectPropertyPattern.Matches(content) |> Seq.cast<Match> do
                let property = m.Groups[1].Value
                let target = m.Groups[2]

                let kind =
                    match property.ToLowerInvariant() with
                    | "vertexshader" -> VertexMainCode
                    | "pixelshader" -> PixelMainCode
                    | "blendstate" -> BlendState
                    | "depthstencilstate" -> DepthStencilState
                    | _ -> RasterizerState

                references.Add
                    { owner = owner
                      target = target.Value
                      targetStart = block.contentStart + target.Index
                      targetLength = target.Length
                      kind = kind }

        for m in constantBufferReferencePattern.Matches(cleaned) |> Seq.cast<Match> do
            let values = m.Groups[1]

            for value in identifierPattern.Matches(values.Value) |> Seq.cast<Match> do
                references.Add
                    { owner = "MainCode"
                      target = value.Value
                      targetStart = values.Index + value.Index
                      targetLength = value.Length
                      kind = ConstantBuffer }

        for m in includesPattern.Matches(cleaned) |> Seq.cast<Match> do
            let values = m.Groups[1]

            for value in quotedValuePattern.Matches(values.Value) |> Seq.cast<Match> do
                let target = value.Groups[1]

                references.Add
                    { owner = "Includes"
                      target = target.Value
                      targetStart = values.Index + target.Index
                      targetLength = target.Length
                      kind = IncludeFile }

        references |> Seq.toList

    let private resourcePathCandidates (resources: Resource seq) =
        resources
        |> Seq.choose (function
            | FileResource(_, resource) when isShaderFile resource.filepath ->
                Some(resource.filepath, resource.logicalpath)
            | FileWithContentResource(_, resource) when
                resource.overwrite <> Overwrite.Overwritten
                && isShaderFile resource.filepath
                ->
                Some(resource.filepath, resource.logicalpath)
            | _ -> None)
        |> Seq.toList

    let private normalizedPath (path: string) =
        path.Replace('\\', '/').TrimStart('/').ToLowerInvariant()

    let private resolveIncludeTarget (resources: Resource seq) (filepath: string) (includePath: string) =
        let currentDirectory =
            Path.GetDirectoryName(filepath) |> Option.ofObj |> Option.defaultValue ""

        let physicalCandidate =
            if Path.IsPathRooted includePath then
                includePath
            else
                Path.Combine(currentDirectory, includePath)

        if File.Exists physicalCandidate then
            Some(Path.GetFullPath physicalCandidate)
        else
            let includeName = fileName includePath
            let includeLogicalPath = normalizedPath includePath

            resourcePathCandidates resources
            |> List.tryPick (fun (candidatePath, candidateLogicalPath) ->
                let logicalPath = normalizedPath candidateLogicalPath

                if
                    File.Exists candidatePath
                    && (fileName candidatePath).Equals(includeName, StringComparison.OrdinalIgnoreCase)
                    && (logicalPath.EndsWith(includeLogicalPath, StringComparison.OrdinalIgnoreCase)
                        || includeLogicalPath = normalizedPath includeName)
                then
                    Some candidatePath
                else
                    None)

    let documentLinks (resources: Resource seq) (filepath: string) (filetext: string) =
        referencesFromText filetext
        |> List.choose (fun (reference: ShaderReference) ->
            match reference.kind with
            | IncludeFile ->
                resolveIncludeTarget resources filepath reference.target
                |> Option.map (fun target ->
                    { range = rangeFromOffset filepath filetext reference.targetStart reference.targetLength
                      targetFilepath = target })
            | _ -> None)

    let private containsIgnoreCase (values: Set<string>) target =
        values |> Set.exists (fun value -> value.Equals(target, StringComparison.OrdinalIgnoreCase))

    let private symbolExists symbols (reference: ShaderReference) =
        match reference.kind with
        | VertexMainCode -> containsIgnoreCase symbols.vertexMainCodes reference.target
        | PixelMainCode -> containsIgnoreCase symbols.pixelMainCodes reference.target
        | ConstantBuffer -> containsIgnoreCase symbols.constantBuffers reference.target
        | BlendState -> containsIgnoreCase symbols.blendStates reference.target
        | DepthStencilState -> containsIgnoreCase symbols.depthStencilStates reference.target
        | RasterizerState -> containsIgnoreCase symbols.rasterizerStates reference.target
        | IncludeFile ->
            containsIgnoreCase symbols.includeFiles reference.target
            || symbols.includeFiles
               |> Set.exists (fun includeFile ->
                   (fileName includeFile).Equals(fileName reference.target, StringComparison.OrdinalIgnoreCase))

    let private missingReferenceError filepath text (reference: ShaderReference) =
        let code, message =
            match reference.kind with
            | VertexMainCode ->
                "CWFX001",
                sprintf "Effect \"%s\" references undefined VertexShader \"%s\"" reference.owner reference.target
            | PixelMainCode ->
                "CWFX001",
                sprintf "Effect \"%s\" references undefined PixelShader \"%s\"" reference.owner reference.target
            | ConstantBuffer ->
                "CWFX002", sprintf "MainCode references undefined ConstantBuffer \"%s\"" reference.target
            | BlendState ->
                "CWFX003", sprintf "Effect \"%s\" references undefined BlendState \"%s\"" reference.owner reference.target
            | DepthStencilState ->
                "CWFX003",
                sprintf "Effect \"%s\" references undefined DepthStencilState \"%s\"" reference.owner reference.target
            | RasterizerState ->
                "CWFX003",
                sprintf "Effect \"%s\" references undefined RasterizerState \"%s\"" reference.owner reference.target
            | IncludeFile -> "CWFX004", sprintf "Include file \"%s\" is not loaded" reference.target

        { code = code
          severity = Severity.Warning
          range = rangeFromOffset filepath text reference.targetStart reference.targetLength
          keyLength = max 1 reference.targetLength
          message = message
          data = None
          relatedErrors = None }

    let validateFromSources sources includeNames filepath filetext =
        let symbols =
            symbolsWithIncludeNames
                (Seq.append sources [ sourceForCurrentFile filepath filetext ])
                (Set.add (fileName filepath) includeNames)

        referencesFromText filetext
        |> List.filter (symbolExists symbols >> not)
        |> List.map (missingReferenceError filepath filetext)

    let validate (resources: IResourceAPI<_>) filepath filetext =
        validateFromSources (resourceSources resources filepath filetext) (resourceIncludeNames resources) filepath filetext

    let private linePrefixAt (text: string) (pos: pos) =
        let lines = text.Split('\n')
        let lineIndex = int pos.Line - 1

        if lineIndex < 0 || lineIndex >= lines.Length then
            ""
        else
            let line = lines[lineIndex].TrimEnd('\r')
            line.Substring(0, min (int pos.Column) line.Length)

    let private offsetAt (text: string) (pos: pos) =
        let mutable line = 1
        let mutable offset = 0

        while offset < text.Length && line < int pos.Line do
            if text[offset] = '\n' then line <- line + 1
            offset <- offset + 1

        min text.Length (offset + max 0 (int pos.Column))

    let private sameFilePath left right =
        let normalize path =
            try Path.GetFullPath path
            with _ -> path

        (normalize left).Equals(normalize right, StringComparison.OrdinalIgnoreCase)

    let private containsOffset startOffset length offset =
        offset >= startOffset && offset <= startOffset + max 1 length

    let private referenceAtOffset filetext offset =
        referencesFromText filetext
        |> List.tryFind (fun (reference: ShaderReference) ->
            containsOffset reference.targetStart reference.targetLength offset)

    let private definitionsForCurrentFile sources filepath =
        definitionsFromSources sources
        |> List.filter (fun definition -> sameFilePath definition.source.filepath filepath)

    let private definitionAtOffset sources filepath offset =
        definitionsForCurrentFile sources filepath
        |> List.tryFind (fun definition ->
            definition.kind <> IncludeFile
            && containsOffset definition.nameStart definition.nameLength offset)

    let private definitionMatches (reference: ShaderReference) (definition: ShaderDefinition) =
        reference.kind = definition.kind
        && (definition.name.Equals(reference.target, StringComparison.OrdinalIgnoreCase)
            || (reference.kind = IncludeFile
                && (fileName definition.name).Equals(fileName reference.target, StringComparison.OrdinalIgnoreCase)))

    let private definitionForReference (definitions: ShaderDefinition list) (reference: ShaderReference) =
        definitions |> List.tryFind (definitionMatches reference)

    let private goToDefinitionWithSources sources pos filepath filetext =
        let offset = offsetAt filetext pos
        let definitions = definitionsFromSources sources

        referenceAtOffset filetext offset
        |> Option.bind (definitionForReference definitions)
        |> Option.map definitionRange

    let goToDefinitionFromSources sources pos filepath filetext =
        goToDefinitionWithSources
            (Seq.append sources [ sourceForCurrentFile filepath filetext ] |> Seq.toList)
            pos
            filepath
            filetext

    let goToDefinition (resources: IResourceAPI<_>) pos filepath filetext =
        goToDefinitionWithSources (resourceSources resources filepath filetext) pos filepath filetext

    let private definitionKindLabel (definition: ShaderDefinition) =
        match definition.kind with
        | VertexMainCode -> "Vertex MainCode"
        | PixelMainCode -> "Pixel MainCode"
        | ConstantBuffer -> "ConstantBuffer"
        | BlendState -> "BlendState"
        | DepthStencilState -> "DepthStencilState"
        | RasterizerState -> "RasterizerState"
        | IncludeFile -> "FX include"

    let private definitionMarkdown prefix (definition: ShaderDefinition) =
        let logicalpath =
            if String.IsNullOrWhiteSpace definition.source.logicalpath then
                definition.source.filepath
            else
                definition.source.logicalpath

        let location =
            if String.IsNullOrWhiteSpace logicalpath then
                ""
            else
                sprintf "\n\n%s `%s`." prefix logicalpath

        sprintf "**%s** `%s`%s" (definitionKindLabel definition) definition.name location

    let private definitionInfo prefix (definition: ShaderDefinition) =
        { typename = "pdx_shader"
          name = definition.name
          localisation = []
          ruleDescription = Some(definitionMarkdown prefix definition)
          ruleRequiredScopes = [] }

    let infoAtPos (resources: IResourceAPI<_>) pos filepath filetext =
        let sources = resourceSources resources filepath filetext
        let offset = offsetAt filetext pos
        let definitions = definitionsFromSources sources

        match referenceAtOffset filetext offset with
        | Some reference ->
            definitionForReference definitions reference
            |> Option.map (definitionInfo "Defined in")
        | None ->
            definitionAtOffset sources filepath offset
            |> Option.map (definitionInfo "Declared in")

    let private recentTextBefore (text: string) (pos: pos) =
        let offset = offsetAt text pos
        let startOffset = max 0 (offset - recentWindowSize)
        text.Substring(startOffset, offset - startOffset)

    let private tailMatches (pattern: string) (text: string) =
        Regex.IsMatch(text, pattern, RegexOptions.IgnoreCase ||| RegexOptions.Singleline)

    let private propertyReferenceCompletions property names detail recentText =
        let valuePattern = sprintf @"\b%s\s*=\s*""[^""]*$" property
        let emptyOrPartialPattern = sprintf @"\b%s\s*=\s*[A-Za-z0-9_]*$" property

        if tailMatches valuePattern recentText then
            Some(names, detail, false)
        elif tailMatches emptyOrPartialPattern recentText then
            Some(names, detail, true)
        else
            None

    let private referenceCompletions symbols recentText =
        propertyReferenceCompletions "VertexShader" symbols.vertexMainCodes "Vertex MainCode" recentText
        |> Option.orElseWith (fun () ->
            propertyReferenceCompletions "PixelShader" symbols.pixelMainCodes "Pixel MainCode" recentText)
        |> Option.orElseWith (fun () ->
            if tailMatches @"\bConstantBuffers\s*=\s*\{[^}]*[A-Za-z0-9_]*$" recentText then
                Some(symbols.constantBuffers, "ConstantBuffer", false)
            else
                None)
        |> Option.orElseWith (fun () ->
            propertyReferenceCompletions "BlendState" symbols.blendStates "BlendState" recentText)
        |> Option.orElseWith (fun () ->
            propertyReferenceCompletions "DepthStencilState" symbols.depthStencilStates "DepthStencilState" recentText)
        |> Option.orElseWith (fun () ->
            propertyReferenceCompletions "RasterizerState" symbols.rasterizerStates "RasterizerState" recentText)
        |> Option.orElseWith (fun () ->
            if tailMatches @"\bIncludes\s*=\s*\{[^}]*""[^""}]*$" recentText then
                Some(symbols.includeFiles, "FX include file", false)
            elif tailMatches @"\bIncludes\s*=\s*\{[^}]*$" recentText then
                Some(symbols.includeFiles, "FX include file", true)
            else
                None)
        |> Option.orElseWith (fun () ->
            if tailMatches @"\bDefines\s*=\s*\{[^}]*""[^""}]*$" recentText then
                Some(symbols.defines, "FX preprocessor define", false)
            elif tailMatches @"\bDefines\s*=\s*\{[^}]*$" recentText then
                Some(symbols.defines, "FX preprocessor define", true)
            else
                None)

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

    let private headerMatches (pattern: string) (header: string) =
        Regex.IsMatch(header, pattern, RegexOptions.IgnoreCase ||| RegexOptions.Singleline)

    let private scopeContextBefore (text: string) offset =
        let endOffset = max 0 (min text.Length offset)
        let headers = ResizeArray<string>()
        let mutable lastBoundary = 0
        let mutable i = 0
        let mutable inString = false
        let mutable insideHlsl = false

        while i < endOffset && not insideHlsl do
            if not inString && i + 1 < endOffset && text[i] = '[' && text[i + 1] = '[' then
                let close = text.IndexOf("]]", i + 2, StringComparison.Ordinal)
                if close < 0 || close >= endOffset then
                    insideHlsl <- true
                else
                    i <- close + 2
            elif not inString && i + 1 < endOffset && text[i] = '/' && text[i + 1] = '/' then
                let next = text.IndexOf('\n', i + 2)
                i <- if next < 0 || next >= endOffset then endOffset else next + 1
            elif not inString && text[i] = '#' then
                let next = text.IndexOf('\n', i + 1)
                i <- if next < 0 || next >= endOffset then endOffset else next + 1
            else
                match text[i] with
                | '"' ->
                    inString <- not inString
                    i <- i + 1
                | '{' when not inString ->
                    let headerStart = max lastBoundary (max 0 (i - 240))
                    headers.Add(text.Substring(headerStart, i - headerStart).Trim())
                    lastBoundary <- i + 1
                    i <- i + 1
                | '}' when not inString ->
                    if headers.Count > 0 then headers.RemoveAt(headers.Count - 1)
                    lastBoundary <- i + 1
                    i <- i + 1
                | _ -> i <- i + 1

        { headers = headers |> Seq.toList
          insideHlsl = insideHlsl }

    let private inBlock pattern scope =
        scope.headers |> List.exists (headerMatches pattern)

    let private blankOrPartialIdentifier (linePrefix: string) =
        Regex.IsMatch(linePrefix, @"^\s*[A-Za-z_]*$")

    let private valuesForLine linePrefix =
        propertyValues
        |> Map.tryPick (fun property values ->
            let pattern = sprintf @"\b%s\s*=\s*""?[A-Za-z0-9_-]*$" (Regex.Escape property)
            if headerMatches pattern linePrefix then Some(property, values) else None)

    let private inferLocalVariables (filetext: string) =
        let mutable varMap = Map.empty
        // 1. Match function parameters (e.g. VS_INPUT v)
        let paramRegex = Regex(@"\b(VS_INPUT|PS_INPUT|VS_OUTPUT|PS_OUTPUT|VS_OUPUT|VS_OUT|PS_OUT|v2f)\s+(\w+)\b", RegexOptions.Compiled)
        for m in paramRegex.Matches(filetext) do
            if m.Groups.Count >= 3 then
                let typeName = m.Groups.[1].Value
                let varName = m.Groups.[2].Value
                varMap <- Map.add varName typeName varMap
        // 2. Match local declarations (e.g. VS_OUTPUT Out;)
        let declRegex = Regex(@"\b(VS_INPUT|PS_INPUT|VS_OUTPUT|PS_OUTPUT|VS_OUPUT|VS_OUT|PS_OUT|v2f)\s+(\w+)\s*;", RegexOptions.Compiled)
        for m in declRegex.Matches(filetext) do
            if m.Groups.Count >= 3 then
                let typeName = m.Groups.[1].Value
                let varName = m.Groups.[2].Value
                varMap <- Map.add varName typeName varMap
        varMap

    let private parseVertexStructs (sources: seq<ShaderSource>) =
        let mutable structMap = Map.empty
        let structStartRegex = Regex(@"\bVertexStruct\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{", RegexOptions.Compiled)
        let fieldRegex = Regex(@"\b(?:float|int|uint|half|bool)(?:2|3|4|2x2|3x3|4x4)?\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?::|;)", RegexOptions.Compiled)
        for source in sources do
            let matches = structStartRegex.Matches(source.filetext)
            for m in matches do
                if m.Groups.Count >= 2 then
                    let structName = m.Groups.[1].Value
                    let startIndex = m.Index + m.Length
                    let mutable depth = 1
                    let mutable curr = startIndex
                    let text = source.filetext
                    while curr < text.Length && depth > 0 do
                        if text.[curr] = '{' then depth <- depth + 1
                        elif text.[curr] = '}' then depth <- depth - 1
                        curr <- curr + 1
                    if depth = 0 then
                        let structContent = text.Substring(startIndex, curr - startIndex - 1)
                        let mutable fields = []
                        for fm in fieldRegex.Matches(structContent) do
                            if fm.Groups.Count >= 2 then
                                fields <- fm.Groups.[1].Value :: fields
                        structMap <- Map.add structName (List.rev fields) structMap
        structMap

    let builtinVariablesSet = 
        lazy (
            let hs = System.Collections.Generic.HashSet<string>()
            for g in hlslPdxGlobals do
                match g with
                | CompletionResponse.Snippet(label, _, _, _, _) -> hs.Add(label) |> ignore
                | CompletionResponse.Simple(label, _, _) -> hs.Add(label) |> ignore
                | CompletionResponse.Detailed(label, _, _, _) -> hs.Add(label) |> ignore
            hs
        )

    let builtinFunctionsSet = 
        lazy (
            let hs = System.Collections.Generic.HashSet<string>()
            for f in hlslBuiltinSnippets do
                match f with
                | CompletionResponse.Snippet(label, _, _, _, _) -> hs.Add(label) |> ignore
                | CompletionResponse.Simple(label, _, _) -> hs.Add(label) |> ignore
                | CompletionResponse.Detailed(label, _, _, _) -> hs.Add(label) |> ignore
            hs
        )

    type private ParsedCacheEntry =
        { fileHash: int
          variables: Set<string>
          functions: CompletionResponse list }

    let private shaderParseCache = System.Collections.Concurrent.ConcurrentDictionary<string, ParsedCacheEntry>()

    let private parseSingleSource (source: ShaderSource) =
        let hash = if isNull source.filetext then 0 else source.filetext.GetHashCode()
        match shaderParseCache.TryGetValue(source.filepath) with
        | true, entry when entry.fileHash = hash ->
            entry.variables, entry.functions
        | _ ->
            let mutable vars = Set.empty
            let cbufferBlockRegex = Regex(@"\bConstantBuffer\s*\([^)]+\)\s*\{([^}]+)\}", RegexOptions.Compiled ||| RegexOptions.Singleline)
            let varDeclRegex = Regex(@"\b(?:float|int|uint|half|bool)(?:2|3|4|2x2|3x3|4x4)?\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?::|;)", RegexOptions.Compiled)
            
            for m in cbufferBlockRegex.Matches(source.filetext) do
                if m.Groups.Count >= 2 then
                    let cbContent = m.Groups.[1].Value
                    for fm in varDeclRegex.Matches(cbContent) do
                        if fm.Groups.Count >= 2 then
                            vars <- Set.add fm.Groups.[1].Value vars
                            
            let globalVarRegex = Regex(@"^\s*(?:float|int|uint|half|bool)(?:2|3|4|2x2|3x3|4x4)?\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?::|;)\s*$", RegexOptions.Compiled ||| RegexOptions.Multiline)
            for m in globalVarRegex.Matches(source.filetext) do
                if m.Groups.Count >= 2 then
                    vars <- Set.add m.Groups.[1].Value vars
                    
            let samplerStartRegex = Regex(@"\bSamplers\s*=\s*\{", RegexOptions.Compiled)
            let sMatches = samplerStartRegex.Matches(source.filetext)
            for m in sMatches do
                let startIndex = m.Index + m.Length
                let mutable depth = 1
                let mutable curr = startIndex
                let text = source.filetext
                while curr < text.Length && depth > 0 do
                    if text.[curr] = '{' then depth <- depth + 1
                    elif text.[curr] = '}' then depth <- depth - 1
                    curr <- curr + 1
                if depth = 0 then
                    let sContent = text.Substring(startIndex, curr - startIndex - 1)
                    let mutable subDepth = 0
                    let mutable j = 0
                    let mutable nameStart = 0
                    let sLen = sContent.Length
                    while j < sLen do
                        let c = sContent.[j]
                        if c = '{' then
                            if subDepth = 0 then
                                let candidate = sContent.Substring(nameStart, j - nameStart)
                                let nm = Regex.Match(candidate, @"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*$", RegexOptions.Multiline)
                                if nm.Success && nm.Groups.Count >= 2 then
                                    vars <- Set.add nm.Groups.[1].Value vars
                            subDepth <- subDepth + 1
                        elif c = '}' then
                            subDepth <- subDepth - 1
                            if subDepth = 0 then
                                nameStart <- j + 1
                        j <- j + 1

            let mutable funcs = Map.empty
            let hlslBlockRegex = Regex(@"\[\[([\s\S]*?)\]\]", RegexOptions.Compiled)
            let funcDeclRegex = Regex(@"\b(void|float[234]?|int[234]?|uint[234]?|half[234]?|bool[234]?|PointLight|LightingProperties|float[234]x[234]|double[234]?)\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(([^)]*)\)", RegexOptions.Compiled)
            let paramWordRegex = Regex(@"\b([A-Za-z_][A-Za-z0-9_]*)\s*$", RegexOptions.Compiled)
            
            for hlslMatch in hlslBlockRegex.Matches(source.filetext) do
                let hlslContent = hlslMatch.Groups.[1].Value
                for m in funcDeclRegex.Matches(hlslContent) do
                    if m.Groups.Count >= 4 then
                        let retType = m.Groups.[1].Value
                        let funcName = m.Groups.[2].Value
                        let paramsStr = m.Groups.[3].Value
                        
                        let paramsList = 
                            paramsStr.Split([|','|], StringSplitOptions.RemoveEmptyEntries)
                            |> Array.map (fun p -> p.Trim())
                            |> Array.choose (fun p ->
                                let pm = paramWordRegex.Match(p)
                                if pm.Success then Some pm.Groups.[1].Value else None
                            )
                            |> Array.toList
                        
                        let snippetText =
                            if List.isEmpty paramsList then
                                sprintf "%s()" funcName
                            else
                                let placeholders = 
                                    paramsList 
                                    |> List.mapi (fun idx p -> sprintf "${%d:%s}" (idx + 1) p)
                                    |> String.concat ", "
                                sprintf "%s(%s)" funcName placeholders
                                
                        let desc = sprintf "%s: Dynamic helper function parsed from includes" retType
                        let item = CompletionResponse.CreateSnippet(funcName, snippetText, Some desc)
                        funcs <- Map.add funcName item funcs
            
            let funcList = funcs |> Map.toList |> List.map snd
            let newEntry = { fileHash = hash; variables = vars; functions = funcList }
            shaderParseCache.[source.filepath] <- newEntry
            vars, funcList

    let parseGlobalVariables (sources: seq<ShaderSource>) =
        sources
        |> Seq.map parseSingleSource
        |> Seq.map fst
        |> Set.unionMany

    let parseGlobalFunctions (sources: seq<ShaderSource>) =
        sources
        |> Seq.map parseSingleSource
        |> Seq.map snd
        |> Seq.toList
        |> List.concat


    let getShaderSources (resources: seq<Resource>) filepath filetext =
        let currentPath =
            try Path.GetFullPath filepath
            with _ -> filepath

        let modSources =
            resources
            |> Seq.choose (function
                | FileResource(_, resource) when isShaderFile resource.filepath ->
                    let candidatePath =
                        try Path.GetFullPath resource.filepath
                        with _ -> resource.filepath

                    if candidatePath.Equals(currentPath, StringComparison.OrdinalIgnoreCase) then
                        None
                    else
                        try
                            if File.Exists resource.filepath then
                                Some
                                    { filepath = resource.filepath
                                      logicalpath = resource.logicalpath
                                      filetext = File.ReadAllText resource.filepath }
                            else
                                None
                        with _ -> None
                | FileWithContentResource(_, resource) when resource.overwrite <> Overwrite.Overwritten && isShaderFile resource.filepath ->
                    let candidatePath =
                        try Path.GetFullPath resource.filepath
                        with _ -> resource.filepath

                    if candidatePath.Equals(currentPath, StringComparison.OrdinalIgnoreCase) then
                        None
                    else
                        try
                            if File.Exists resource.filepath then
                                Some
                                    { filepath = resource.filepath
                                      logicalpath = resource.logicalpath
                                      filetext = File.ReadAllText resource.filepath }
                            else
                                None
                        with _ -> None
                | _ -> None)

        modSources
        |> Seq.append [ sourceForCurrentFile filepath filetext ]
        |> Seq.append (
            vanillaFxSources
            |> List.filter (fun s ->
                let sp =
                    try Path.GetFullPath s.filepath
                    with _ -> s.filepath
                not (sp.Equals(currentPath, StringComparison.OrdinalIgnoreCase))))
        |> Seq.toList




    let completeFromSources sources includeNames pos filepath filetext =
        let symbols =
            symbolsWithIncludeNames
                (Seq.append sources [ sourceForCurrentFile filepath filetext ])
                (Set.add (fileName filepath) includeNames)

        let recentText = recentTextBefore filetext pos
        let linePrefix = linePrefixAt filetext pos

        match referenceCompletions symbols recentText with
        | Some(names, detail, requiresQuotes) ->
            names
            |> Set.toList
            |> List.map (fun name -> referenceCompletion requiresQuotes name detail)
        | None ->
            let scope = scopeContextBefore filetext (offsetAt filetext pos)

            if scope.insideHlsl then
                let dotMatch = Regex.Match(linePrefix, @"\b([A-Za-z_][A-Za-z0-9_]*)\.$")
                if dotMatch.Success then
                    let varName = dotMatch.Groups.[1].Value
                    let localVars = inferLocalVariables filetext
                    match localVars.TryFind(varName) with
                    | Some(typeName) ->
                        let structs = parseVertexStructs (Seq.append sources [ sourceForCurrentFile filepath filetext ])
                        match structs.TryFind(typeName) with
                        | Some(fields) ->
                            fields |> List.map (fun field -> valueCompletion field "Vertex field")
                        | None -> []
                    | None -> []
                else
                    let typeCompletions =
                        hlslTypes |> List.map (fun t -> valueCompletion t "HLSL type")
                    
                    let mutable parenDepth = 0
                    for c in linePrefix do
                        if c = '(' then parenDepth <- parenDepth + 1
                        elif c = ')' then parenDepth <- max 0 (parenDepth - 1)
                    
                    let pdxGlobalCompletions = hlslPdxGlobals
                    let pdxGlobalNames =
                        hlslPdxGlobals
                        |> List.choose (function
                            | CompletionResponse.Snippet(label, _, _, _, _) -> Some label
                            | CompletionResponse.Simple(label, _, _) -> Some label
                            | CompletionResponse.Detailed(label, _, _, _) -> Some label)
                        |> Set.ofList

                    let allSources = Seq.append sources [ sourceForCurrentFile filepath filetext ]
                    let parsedGlobals = parseGlobalVariables allSources
                    let parsedGlobalCompletions =
                        parsedGlobals
                        |> Set.filter (fun v -> not (Set.contains v pdxGlobalNames))
                        |> Set.toList
                        |> List.map (fun v -> completionItem v "HLSL variable" CompletionCategory.Value)

                    let parsedFunctions = parseGlobalFunctions allSources

                    if parenDepth > 0 then
                        typeCompletions @ hlslPdxGlobals @ parsedGlobalCompletions @ parsedFunctions @ hlslBuiltinSnippets
                    else
                        let controlFlowCompletions =
                            hlslControlFlow |> List.map (fun kw -> completionItem kw "HLSL keyword" CompletionCategory.Value)
                        let pdxDirectiveCompletions =
                            hlslPdxDirectives |> List.map (fun d -> completionItem d "Paradox directive" CompletionCategory.Global)
                        typeCompletions @ controlFlowCompletions @ pdxDirectiveCompletions @ pdxGlobalCompletions @ parsedGlobalCompletions @ parsedFunctions @ hlslBuiltinSnippets
            elif Regex.IsMatch(linePrefix, @":\s*[A-Za-z0-9_]*$") && inBlock @"\bVertexStruct\s+\w+\s*$" scope then
                vertexSemantics |> List.map (fun semantic -> valueCompletion semantic "Vertex semantic")
            else
                match valuesForLine linePrefix with
                | Some(property, values) ->
                    values |> List.map (fun value -> valueCompletion value (sprintf "%s value" property))
                | None when
                    blankOrPartialIdentifier linePrefix
                    && (inBlock @"\bVertexStruct\s+\w+\s*$" scope
                        || inBlock @"\bConstantBuffer\s*\(" scope)
                    ->
                    shaderFieldTypes |> List.map (fun fieldType -> valueCompletion fieldType "FX field type")
                | None when blankOrPartialIdentifier linePrefix && inBlock @"\bEffect\s+\w+\s*$" scope ->
                    effectProperties
                    |> List.map (fun property -> completionItem property "Effect property" CompletionCategory.Value)
                | None when
                    blankOrPartialIdentifier linePrefix
                    && scope.headers.Length > 0
                    && headerMatches @"\b[A-Za-z_][A-Za-z0-9_]*\s*=\s*$" scope.headers[scope.headers.Length - 1]
                    && inBlock @"\bSamplers\s*=\s*$" scope
                    ->
                    samplerProperties
                    |> List.map (fun property -> completionItem property "Sampler property" CompletionCategory.Value)
                | None when blankOrPartialIdentifier linePrefix && inBlock @"\bBlendState\s+\w+\s*$" scope ->
                    blendProperties
                    |> List.map (fun property -> completionItem property "BlendState property" CompletionCategory.Value)
                | None when blankOrPartialIdentifier linePrefix && inBlock @"\bDepthStencilState\s+\w+\s*$" scope ->
                    depthStencilProperties
                    |> List.map (fun property -> completionItem property "DepthStencilState property" CompletionCategory.Value)
                | None when blankOrPartialIdentifier linePrefix && inBlock @"\bRasterizerState\s+\w+\s*$" scope ->
                    rasterizerProperties
                    |> List.map (fun property -> completionItem property "RasterizerState property" CompletionCategory.Value)
                | None when blankOrPartialIdentifier linePrefix -> snippets
                | None -> []

    let completion (resourceManager: ResourceManager<_>) pos filepath filetext =
        completeFromSources
            (resourceSources resourceManager.Api filepath filetext)
            (resourceIncludeNames resourceManager.Api)
            pos
            filepath
            filetext
