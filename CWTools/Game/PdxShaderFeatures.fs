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

    let private identifierPattern =
        regex RegexOptions.None @"[A-Za-z_][A-Za-z0-9_]*"

    let private quotedValuePattern =
        regex RegexOptions.None @"""([^""]+)"""

    let private recentWindowSize = 16 * 1024

    let private emptySymbols =
        { vertexMainCodes = Set.empty
          pixelMainCodes = Set.empty
          constantBuffers = Set.empty
          blendStates = Set.empty
          depthStencilStates = Set.empty
          rasterizerStates = Set.empty
          includeFiles = Set.empty }

    let isShaderFile (filepath: string) =
        let extension = Path.GetExtension(filepath)
        extension.Equals(".shader", StringComparison.OrdinalIgnoreCase)
        || extension.Equals(".fxh", StringComparison.OrdinalIgnoreCase)

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

    let private extractSymbolsFromText (source: ShaderSource) =
        let cleaned = cleanDslText source.filetext

        { vertexMainCodes = shaderBlockMainCodes vertexShaderBlockPattern cleaned
          pixelMainCodes = shaderBlockMainCodes pixelShaderBlockPattern cleaned
          constantBuffers = matchNames constantBufferPattern cleaned
          blendStates = matchNames blendStatePattern cleaned
          depthStencilStates = matchNames depthStencilStatePattern cleaned
          rasterizerStates = matchNames rasterizerStatePattern cleaned
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
            | _ -> None)
        |> Seq.append [ sourceForCurrentFile filepath filetext ]
        |> Seq.toList

    let private resourceIncludeNames (resources: IResourceAPI<_>) =
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

    let private symbolExists symbols (reference: ShaderReference) =
        match reference.kind with
        | VertexMainCode -> Set.contains reference.target symbols.vertexMainCodes
        | PixelMainCode -> Set.contains reference.target symbols.pixelMainCodes
        | ConstantBuffer -> Set.contains reference.target symbols.constantBuffers
        | BlendState -> Set.contains reference.target symbols.blendStates
        | DepthStencilState -> Set.contains reference.target symbols.depthStencilStates
        | RasterizerState -> Set.contains reference.target symbols.rasterizerStates
        | IncludeFile ->
            Set.contains reference.target symbols.includeFiles
            || Set.contains (fileName reference.target) symbols.includeFiles

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

    let private referenceCompletions symbols recentText =
        if tailMatches @"\bVertexShader\s*=\s*""[^""]*$" recentText then
            Some(symbols.vertexMainCodes, "Vertex MainCode")
        elif tailMatches @"\bPixelShader\s*=\s*""[^""]*$" recentText then
            Some(symbols.pixelMainCodes, "Pixel MainCode")
        elif tailMatches @"\bConstantBuffers\s*=\s*\{[^}]*[A-Za-z0-9_]*$" recentText then
            Some(symbols.constantBuffers, "ConstantBuffer")
        elif tailMatches @"\bBlendState\s*=\s*""[^""]*$" recentText then
            Some(symbols.blendStates, "BlendState")
        elif tailMatches @"\bDepthStencilState\s*=\s*""[^""]*$" recentText then
            Some(symbols.depthStencilStates, "DepthStencilState")
        elif tailMatches @"\bRasterizerState\s*=\s*""[^""]*$" recentText then
            Some(symbols.rasterizerStates, "RasterizerState")
        elif tailMatches @"\bIncludes\s*=\s*\{[^}]*""[^""}]*$" recentText then
            Some(symbols.includeFiles, "FX include file")
        else
            None

    let private completionItem label detail category =
        CompletionResponse.Detailed(label, Some detail, None, category)

    let private valueCompletion label detail =
        completionItem label detail CompletionCategory.Value

    let private snippets =
        [ CompletionResponse.CreateSnippet(
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
              [ "SRC_ALPHA"
                "INV_SRC_ALPHA"
                "ONE"
                "ZERO"
                "SRC_COLOR"
                "INV_SRC_COLOR"
                "DEST_ALPHA"
                "INV_DEST_ALPHA"
                "DEST_COLOR"
                "INV_DEST_COLOR" ]
              "DestBlend",
              [ "SRC_ALPHA"
                "INV_SRC_ALPHA"
                "ONE"
                "ZERO"
                "SRC_COLOR"
                "INV_SRC_COLOR"
                "DEST_ALPHA"
                "INV_DEST_ALPHA"
                "DEST_COLOR"
                "INV_DEST_COLOR" ]
              "SourceAlpha", [ "SRC_ALPHA"; "INV_SRC_ALPHA"; "ONE"; "ZERO" ]
              "DestAlpha", [ "SRC_ALPHA"; "INV_SRC_ALPHA"; "ONE"; "ZERO" ]
              "BlendOp", [ "ADD"; "SUBTRACT"; "REV_SUBTRACT"; "MIN"; "MAX" ]
              "BlendOpAlpha", [ "ADD"; "SUBTRACT"; "REV_SUBTRACT"; "MIN"; "MAX" ]
              "WriteMask", [ "RED"; "GREEN"; "BLUE"; "ALPHA"; "0x0F"; "0x0E"; "0x0C"; "0x08"; "0x00" ]
              "CullMode", [ "none"; "cw"; "ccw" ]
              "FillMode", [ "solid"; "wireframe" ]
              "FrontCCW", [ "yes"; "no" ]
              "DepthEnable", [ "yes"; "no" ]
              "DepthWriteEnable", [ "yes"; "no" ]
              "DepthWriteMask", [ "DEPTH_WRITE_ALL"; "DEPTH_WRITE_ZERO" ]
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

    let completeFromSources sources includeNames pos filepath filetext =
        let symbols =
            symbolsWithIncludeNames
                (Seq.append sources [ sourceForCurrentFile filepath filetext ])
                (Set.add (fileName filepath) includeNames)

        let recentText = recentTextBefore filetext pos
        let linePrefix = linePrefixAt filetext pos

        match referenceCompletions symbols recentText with
        | Some(names, detail) ->
            names
            |> Set.toList
            |> List.map (fun name -> completionItem name detail CompletionCategory.Link)
        | None ->
            let scope = scopeContextBefore filetext (offsetAt filetext pos)

            if scope.insideHlsl then
                []
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
                | None when blankOrPartialIdentifier linePrefix && List.isEmpty scope.headers -> snippets
                | None -> []

    let completion (resourceManager: ResourceManager<_>) pos filepath filetext =
        completeFromSources
            (resourceSources resourceManager.Api filepath filetext)
            (resourceIncludeNames resourceManager.Api)
            pos
            filepath
            filetext
