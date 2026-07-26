namespace CWTools.Games

open System
open System.Collections.Generic
open PdxShaderSyntax
open PdxShaderPreprocessor

/// Tolerant HLSL/Cg declaration, binding and type model for embedded [[ ]]
/// regions and hybrid raw .fxh files. Unsupported constructs remain in the
/// lossless syntax tree and produce conservative unknown types, not crashes.
module PdxShaderHlsl =
    type ShaderStage =
        | VertexStage
        | PixelStage
        | GeometryStage
        | UnknownStage

    type ScalarKind =
        | Bool
        | Int
        | UInt
        | Half
        | Float
        | Double

    type HlslType =
        | VoidType
        | ScalarType of ScalarKind
        | VectorType of ScalarKind * int
        | MatrixType of ScalarKind * int * int
        | ArrayType of HlslType * int option
        | StructType of string
        | TextureType of string
        | SamplerType of string
        | BufferType of string * HlslType option
        | UnknownType of string
        | ErrorType

    type ParameterDirection =
        | In
        | Out
        | InOut

    type HlslParameter =
        { name: string
          parameterType: HlslType
          direction: ParameterDirection
          semantic: string option
          span: TextSpan }

    type HlslSymbolKind =
        | TypeSymbol
        | StructSymbol
        | FieldSymbol
        | ConstantBufferSymbol
        | ResourceSymbol
        | SamplerSymbol
        | FunctionSymbol
        | ParameterSymbol
        | GlobalVariableSymbol
        | LocalVariableSymbol
        | MacroSymbol

    type HlslScopeKind =
        | FileScope
        | StructScope
        | FunctionScope
        | LexicalScope

    type ResourceBinding =
        { registerClass: string
          registerIndex: int }

    type HlslSymbol =
        { id: string
          name: string
          kind: HlslSymbolKind
          symbolType: HlslType
          span: TextSpan
          selectionSpan: TextSpan
          scopeId: int
          condition: PresenceCondition
          stage: ShaderStage
          parameters: HlslParameter list
          semantic: string option
          binding: ResourceBinding option }

    type HlslScope =
        { id: int
          kind: HlslScopeKind
          parentId: int option
          span: TextSpan }

    type HlslReferenceKind =
        | ReadReference
        | WriteReference
        | CallReference
        | TypeReference
        | MemberReference

    type HlslReference =
        { name: string
          kind: HlslReferenceKind
          span: TextSpan
          scopeId: int
          condition: PresenceCondition
          stage: ShaderStage
          candidateIds: string list }

    type HlslDiagnostic =
        { code: string
          message: string
          span: TextSpan
          condition: PresenceCondition
          stage: ShaderStage }

    type HlslCallEdge =
        { callerId: string option
          calleeIds: string list
          span: TextSpan
          condition: PresenceCondition }

    type HlslAnalysis =
        { symbols: HlslSymbol list
          references: HlslReference list
          scopes: HlslScope list
          diagnostics: HlslDiagnostic list
          calls: HlslCallEdge list }

    type private FunctionRegion =
        { symbolId: string
          scopeId: int
          bodyStart: int
          bodyEnd: int
          stage: ShaderStage }

    let private isTrivia kind =
        kind = Whitespace
        || kind = NewLine
        || kind = LineComment
        || kind = BlockComment
        || kind = DirectiveLine
        || kind = HlslOpen
        || kind = HlslClose
        || kind = EndOfFile

    let private builtinScalar =
        Map.ofList
            [ "bool", Bool
              "int", Int
              "uint", UInt
              "half", Half
              "float", Float
              "double", Double ]

    let private resourcePrefixes =
        [ "texture"; "rwtexture"; "sampler"; "buffer"; "rwbuffer"; "structuredbuffer"; "byteaddressbuffer" ]

    let private keywords =
        set
            [ "if"
              "else"
              "switch"
              "case"
              "default"
              "for"
              "while"
              "do"
              "break"
              "continue"
              "return"
              "discard"
              "struct"
              "typedef"
              "const"
              "static"
              "uniform"
              "volatile"
              "precise"
              "in"
              "out"
              "inout"
              "true"
              "false"
              "register"
              "vertexstruct"
              "constantbuffer"
              "maincode"
              "vertexshader"
              "pixelshader"
              "geometryshader"
              "effect"
              "includes"
              "samplers" ]

    let parseTypeName (name: string) =
        let lower = name.ToLowerInvariant()

        if lower = "void" then
            VoidType
        elif builtinScalar.ContainsKey lower then
            ScalarType builtinScalar[lower]
        else
            let scalarWithDimensions =
                builtinScalar
                |> Seq.tryPick (fun pair ->
                    if lower.StartsWith(pair.Key, StringComparison.Ordinal) then
                        let suffix = lower.Substring(pair.Key.Length)

                        if suffix.Length = 1 && Char.IsDigit suffix[0] then
                            Some(VectorType(pair.Value, int (string suffix[0])))
                        elif suffix.Length = 3 && Char.IsDigit suffix[0] && suffix[1] = 'x' && Char.IsDigit suffix[2] then
                            Some(MatrixType(pair.Value, int (string suffix[0]), int (string suffix[2])))
                        else
                            None
                    else
                        None)

            match scalarWithDimensions with
            | Some value -> value
            | None when lower.StartsWith("sampler", StringComparison.Ordinal) -> SamplerType name
            | None when lower.StartsWith("texture", StringComparison.Ordinal)
                        || lower.StartsWith("rwtexture", StringComparison.Ordinal) -> TextureType name
            | None when resourcePrefixes |> List.exists lower.StartsWith -> BufferType(name, None)
            | None -> StructType name

    let rec private conversionScore source target =
        if source = target then
            Some 0
        else
            match source, target with
            | ErrorType, _
            | _, ErrorType -> None
            | UnknownType _, _
            | _, UnknownType _ -> Some 8
            | ScalarType sourceScalar, ScalarType targetScalar ->
                let numericRank =
                    function
                    | Bool -> 0
                    | Int -> 1
                    | UInt -> 2
                    | Half -> 3
                    | Float -> 4
                    | Double -> 5

                if sourceScalar = Bool || targetScalar = Bool then None
                else Some(1 + abs (numericRank targetScalar - numericRank sourceScalar))
            | ScalarType scalar, VectorType(targetScalar, _) ->
                conversionScore (ScalarType scalar) (ScalarType targetScalar)
                |> Option.map ((+) 2)
            | VectorType(sourceScalar, sourceWidth), VectorType(targetScalar, targetWidth) when sourceWidth = targetWidth ->
                conversionScore (ScalarType sourceScalar) (ScalarType targetScalar)
            | MatrixType(sourceScalar, sourceRows, sourceColumns), MatrixType(targetScalar, targetRows, targetColumns) when
                sourceRows = targetRows && sourceColumns = targetColumns
                ->
                conversionScore (ScalarType sourceScalar) (ScalarType targetScalar)
            | ArrayType(sourceElement, sourceLength), ArrayType(targetElement, targetLength) when sourceLength = targetLength ->
                conversionScore sourceElement targetElement
            | _ -> None

    let resolveOverload (argumentTypes: HlslType list) (candidates: HlslSymbol list) =
        let scored =
            candidates
            |> List.choose (fun candidate ->
                if candidate.kind <> FunctionSymbol || candidate.parameters.Length <> argumentTypes.Length then
                    None
                else
                    let scores =
                        List.zip argumentTypes (candidate.parameters |> List.map _.parameterType)
                        |> List.map (fun (source, target) -> conversionScore source target)

                    if scores |> List.exists Option.isNone then None
                    else Some(candidate, scores |> List.sumBy Option.get))
            |> List.sortBy (fun (candidate, score) -> score, candidate.id)

        match scored with
        | [] -> []
        | (_, bestScore) :: _ ->
            scored
            |> List.takeWhile (fun (_, score) -> score = bestScore)
            |> List.map fst

    let private stableId (filepath: string) (kind: HlslSymbolKind) (name: string) (offset: int) =
        sprintf "shader:%s:%A:%s:%d" (filepath.Replace('\\', '/').ToLowerInvariant()) kind name offset

    let private significantTokens (tree: ShaderSyntaxTree) startOffset endOffset =
        tree.tokens
        |> Array.filter (fun token ->
            not (isTrivia token.kind)
            && token.span.startOffset >= startOffset
            && token.span.endOffset <= endOffset)

    let private matchingIndex openKind closeKind (tokens: ShaderToken array) openIndex =
        let mutable depth = 0
        let mutable index = openIndex
        let mutable result = None

        while index < tokens.Length && Option.isNone result do
            if tokens[index].kind = openKind then depth <- depth + 1
            elif tokens[index].kind = closeKind then
                depth <- depth - 1
                if depth = 0 then result <- Some index
            index <- index + 1

        result

    let private semanticAfter (tokens: ShaderToken array) startIndex endIndex =
        let mutable index = startIndex
        let mutable result = None

        while index + 1 < endIndex && Option.isNone result do
            if tokens[index].kind = Colon && tokens[index + 1].kind = Identifier then
                result <- Some tokens[index + 1].text
            index <- index + 1

        result

    let private parseBinding (tokens: ShaderToken array) startIndex endIndex =
        let mutable index = startIndex
        let mutable result = None

        while index + 3 < endIndex && Option.isNone result do
            if tokens[index].kind = Identifier
               && tokens[index].text.Equals("register", StringComparison.OrdinalIgnoreCase)
               && tokens[index + 1].kind = OpenParen
               && tokens[index + 2].kind = Identifier then
                let register = tokens[index + 2].text
                let mutable split = 0

                while split < register.Length && Char.IsLetter register[split] do
                    split <- split + 1

                match Int32.TryParse(register.Substring(split)) with
                | true, registerIndex ->
                    result <-
                        Some
                            { registerClass = register.Substring(0, split).ToLowerInvariant()
                              registerIndex = registerIndex }
                | _ -> ()

            index <- index + 1

        result

    let private parameterFromSegment (segment: ShaderToken list) =
        let identifiers = segment |> List.filter (fun token -> token.kind = Identifier)

        if identifiers.Length < 2 then
            None
        else
            let direction =
                if identifiers |> List.exists (fun token -> token.text.Equals("inout", StringComparison.OrdinalIgnoreCase)) then InOut
                elif identifiers |> List.exists (fun token -> token.text.Equals("out", StringComparison.OrdinalIgnoreCase)) then Out
                else In
            let meaningful =
                identifiers
                |> List.filter (fun token ->
                    let lower = token.text.ToLowerInvariant()
                    lower <> "const" && lower <> "in" && lower <> "out" && lower <> "inout" && lower <> "uniform")

            if meaningful.Length < 2 then
                None
            else
                let typeToken = meaningful[0]
                let nameToken = meaningful[meaningful.Length - 1]
                let semantic = semanticAfter (segment |> List.toArray) 0 segment.Length

                Some
                    { name = nameToken.text
                      parameterType = parseTypeName typeToken.text
                      direction = direction
                      semantic = semantic
                      span =
                        { startOffset = typeToken.span.startOffset
                          endOffset = nameToken.span.endOffset } }

    let private parseParameters (tokens: ShaderToken array) openIndex closeIndex =
        let parameters = ResizeArray<HlslParameter>()
        let mutable segmentStart = openIndex + 1
        let mutable depth = 0

        for index in openIndex + 1 .. closeIndex do
            let atBoundary =
                index = closeIndex
                || (tokens[index].kind = Comma && depth = 0)

            if atBoundary then
                let segment =
                    if index > segmentStart then tokens[segmentStart .. index - 1] |> Array.toList else []
                parameterFromSegment segment |> Option.iter parameters.Add
                segmentStart <- index + 1
            elif tokens[index].kind = OpenParen || tokens[index].kind = OpenBracket then depth <- depth + 1
            elif tokens[index].kind = CloseParen || tokens[index].kind = CloseBracket then depth <- max 0 (depth - 1)

        parameters |> Seq.toList

    let private stageRegions (tree: ShaderSyntaxTree) =
        let regions = ResizeArray<TextSpan * ShaderStage>()

        let rec visit (stage: ShaderStage) (node: ShaderSyntaxNode) =
            let stage =
                match node.kind with
                | ShaderNodeKind.VertexShader -> VertexStage
                | ShaderNodeKind.PixelShader -> PixelStage
                | ShaderNodeKind.GeometryShader -> GeometryStage
                | _ -> stage

            if node.kind = ShaderNodeKind.HlslRegion then regions.Add(node.span, stage)
            node.children |> List.iter (visit stage)

        visit UnknownStage tree.root
        regions |> Seq.toList

    let private stageAt regions offset =
        regions
        |> List.tryPick (fun (region, stage) ->
            if offset >= region.startOffset && offset < region.endOffset then Some stage else None)
        |> Option.defaultValue UnknownStage

    let analyze (tree: ShaderSyntaxTree) (preprocessor: PreprocessorResult) : HlslAnalysis =
        let symbols = ResizeArray<HlslSymbol>()
        let references = ResizeArray<HlslReference>()
        let scopes = ResizeArray<HlslScope>()
        let diagnostics = ResizeArray<HlslDiagnostic>()
        let calls = ResizeArray<HlslCallEdge>()
        let functionRegions = ResizeArray<FunctionRegion>()
        let declarationSpans = HashSet<int * int>()
        let structTypeByScopeId = Dictionary<int, string>()
        let mutable nextScopeId = 1
        let stageSpans = stageRegions tree

        scopes.Add(
            { id = 0
              kind = FileScope
              parentId = None
              span = tree.root.span }
        )

        let newScope kind parent span =
            let scopeId = nextScopeId
            nextScopeId <- nextScopeId + 1
            scopes.Add(
                { id = scopeId
                  kind = kind
                  parentId = parent
                  span = span }
            )
            scopeId

        let scopeAtOffset offset =
            scopes
            |> Seq.filter (fun scope ->
                (scope.kind = FunctionScope || scope.kind = LexicalScope)
                && offset >= scope.span.startOffset
                && offset < scope.span.endOffset)
            |> Seq.sortBy (fun scope -> scope.span.Length)
            |> Seq.tryHead
            |> Option.map _.id
            |> Option.defaultValue 0

        let addSymbol kind name symbolType fullSpan selectionSpan scopeId parameters semantic binding =
            let condition = conditionAt selectionSpan.startOffset preprocessor
            let stage = stageAt stageSpans selectionSpan.startOffset
            let symbol =
                { id = stableId tree.filepath kind name selectionSpan.startOffset
                  name = name
                  kind = kind
                  symbolType = symbolType
                  span = fullSpan
                  selectionSpan = selectionSpan
                  scopeId = scopeId
                  condition = condition
                  stage = stage
                  parameters = parameters
                  semantic = semantic
                  binding = binding }
            symbols.Add symbol
            declarationSpans.Add(selectionSpan.startOffset, selectionSpan.endOffset) |> ignore
            symbol

        let parseFields ownerScope (tokens: ShaderToken array) openIndex closeIndex =
            let mutable startIndex = openIndex + 1
            let mutable depth = 0

            let consume endIndex =
                if endIndex > startIndex then
                    let segment = tokens[startIndex .. endIndex - 1]
                    let identifiers = segment |> Array.filter (fun token -> token.kind = Identifier)

                    if identifiers.Length >= 2 then
                        let typeToken = identifiers[0]
                        let nameToken = identifiers[1]
                        let fieldType = parseTypeName typeToken.text
                        let arrayType =
                            if segment |> Array.exists (fun token -> token.kind = OpenBracket) then ArrayType(fieldType, None)
                            else fieldType
                        addSymbol
                            FieldSymbol
                            nameToken.text
                            arrayType
                            { startOffset = segment[0].span.startOffset
                              endOffset = segment[segment.Length - 1].span.endOffset }
                            nameToken.span
                            ownerScope
                            []
                            (semanticAfter segment 0 segment.Length)
                            None
                        |> ignore

                startIndex <- endIndex + 1

            for index in openIndex + 1 .. closeIndex do
                if index = closeIndex then consume index
                elif tokens[index].kind = OpenBrace || tokens[index].kind = OpenParen then depth <- depth + 1
                elif tokens[index].kind = CloseBrace || tokens[index].kind = CloseParen then depth <- max 0 (depth - 1)
                elif tokens[index].kind = Semicolon && depth = 0 then consume index

        let parseStream (tokens: ShaderToken array) =
            let mutable index = 0
            let mutable braceDepth = 0

            while index < tokens.Length do
                let token = tokens[index]

                if token.kind = OpenBrace then
                    braceDepth <- braceDepth + 1
                    index <- index + 1
                elif token.kind = CloseBrace then
                    braceDepth <- max 0 (braceDepth - 1)
                    index <- index + 1
                elif token.kind = Identifier
                     && (token.text.Equals("struct", StringComparison.OrdinalIgnoreCase)
                         || token.text.Equals("VertexStruct", StringComparison.OrdinalIgnoreCase))
                     && index + 2 < tokens.Length
                     && tokens[index + 1].kind = Identifier then
                    let nameToken = tokens[index + 1]
                    let mutable openIndex = index + 2
                    while openIndex < tokens.Length && tokens[openIndex].kind <> OpenBrace do openIndex <- openIndex + 1

                    if openIndex < tokens.Length then
                        match matchingIndex OpenBrace CloseBrace tokens openIndex with
                        | Some closeIndex ->
                            let ownerScope =
                                newScope
                                    StructScope
                                    (Some 0)
                                    { startOffset = token.span.startOffset
                                      endOffset = tokens[closeIndex].span.endOffset }
                            structTypeByScopeId[ownerScope] <- nameToken.text
                            addSymbol
                                StructSymbol
                                nameToken.text
                                (StructType nameToken.text)
                                { startOffset = token.span.startOffset
                                  endOffset = tokens[closeIndex].span.endOffset }
                                nameToken.span
                                0
                                []
                                None
                                None
                            |> ignore
                            parseFields ownerScope tokens openIndex closeIndex
                            index <- closeIndex + 1
                        | None -> index <- openIndex + 1
                    else
                        index <- index + 1
                elif token.kind = Identifier
                     && token.text.Equals("ConstantBuffer", StringComparison.OrdinalIgnoreCase)
                     && index + 3 < tokens.Length
                     && tokens[index + 1].kind = OpenParen
                     && tokens[index + 2].kind = Identifier then
                    let nameToken = tokens[index + 2]

                    match matchingIndex OpenParen CloseParen tokens (index + 1) with
                    | Some closeParen ->
                        let mutable openIndex = closeParen + 1
                        while openIndex < tokens.Length && tokens[openIndex].kind <> OpenBrace do openIndex <- openIndex + 1

                        if openIndex < tokens.Length then
                            match matchingIndex OpenBrace CloseBrace tokens openIndex with
                            | Some closeBrace ->
                                let ownerScope =
                                    newScope
                                        StructScope
                                        (Some 0)
                                        { startOffset = token.span.startOffset
                                          endOffset = tokens[closeBrace].span.endOffset }
                                let binding =
                                    let commaNumbers =
                                        tokens[index + 3 .. closeParen - 1]
                                        |> Array.filter (fun item -> item.kind = NumberLiteral)

                                    if commaNumbers.Length > 0 then
                                        match Int32.TryParse commaNumbers[0].text with
                                        | true, value -> Some { registerClass = "b"; registerIndex = value }
                                        | _ -> None
                                    else None
                                addSymbol
                                    ConstantBufferSymbol
                                    nameToken.text
                                    (BufferType("ConstantBuffer", None))
                                    { startOffset = token.span.startOffset
                                      endOffset = tokens[closeBrace].span.endOffset }
                                    nameToken.span
                                    0
                                    []
                                    None
                                    binding
                                |> ignore
                                parseFields ownerScope tokens openIndex closeBrace
                                index <- closeBrace + 1
                            | None -> index <- openIndex + 1
                        else index <- closeParen + 1
                    | None -> index <- index + 1
                elif braceDepth = 0
                     && token.kind = Identifier
                     && index + 2 < tokens.Length
                     && tokens[index + 1].kind = Identifier
                     && tokens[index + 2].kind = OpenParen then
                    let returnType = parseTypeName token.text
                    let nameToken = tokens[index + 1]

                    match matchingIndex OpenParen CloseParen tokens (index + 2) with
                    | Some closeParen ->
                        let parameters = parseParameters tokens (index + 2) closeParen
                        let mutable after = closeParen + 1
                        let mutable semantic = None

                        if after + 1 < tokens.Length && tokens[after].kind = Colon && tokens[after + 1].kind = Identifier then
                            semantic <- Some tokens[after + 1].text
                            after <- after + 2

                        let binding = parseBinding tokens after (min tokens.Length (after + 8))
                        let bodyClose =
                            if after < tokens.Length && tokens[after].kind = OpenBrace then
                                matchingIndex OpenBrace CloseBrace tokens after
                            else None
                        let endIndex = bodyClose |> Option.defaultValue (min (tokens.Length - 1) after)
                        let functionScope =
                            newScope
                                FunctionScope
                                (Some 0)
                                { startOffset = token.span.startOffset
                                  endOffset = tokens[endIndex].span.endOffset }
                        let functionSymbol =
                            addSymbol
                                FunctionSymbol
                                nameToken.text
                                returnType
                                { startOffset = token.span.startOffset
                                  endOffset = tokens[endIndex].span.endOffset }
                                nameToken.span
                                0
                                parameters
                                semantic
                                binding

                        for parameter in parameters do
                            addSymbol
                                ParameterSymbol
                                parameter.name
                                parameter.parameterType
                                parameter.span
                                { startOffset = parameter.span.endOffset - parameter.name.Length
                                  endOffset = parameter.span.endOffset }
                                functionScope
                                []
                                parameter.semantic
                                None
                            |> ignore

                        match bodyClose with
                        | Some closeBrace ->
                            functionRegions.Add(
                                { symbolId = functionSymbol.id
                                  scopeId = functionScope
                                  bodyStart = tokens[after].span.startOffset
                                  bodyEnd = tokens[closeBrace].span.endOffset
                                  stage = stageAt stageSpans nameToken.span.startOffset }
                            )

                            // Materialize nested lexical scopes before assigning
                            // locals and references. FunctionScope represents the
                            // outer body; every nested brace pair gets a child.
                            let lexicalStack = Stack<int>()
                            lexicalStack.Push functionScope

                            for braceIndex in after + 1 .. closeBrace - 1 do
                                if tokens[braceIndex].kind = OpenBrace then
                                    match matchingIndex OpenBrace CloseBrace tokens braceIndex with
                                    | Some lexicalClose when lexicalClose <= closeBrace ->
                                        let lexicalScope =
                                            newScope
                                                LexicalScope
                                                (Some(lexicalStack.Peek()))
                                                { startOffset = tokens[braceIndex].span.startOffset
                                                  endOffset = tokens[lexicalClose].span.endOffset }
                                        lexicalStack.Push lexicalScope
                                    | _ -> ()
                                elif tokens[braceIndex].kind = CloseBrace && lexicalStack.Count > 1 then
                                    lexicalStack.Pop() |> ignore

                            let mutable localIndex = after + 1

                            while localIndex + 2 < closeBrace do
                                let first = tokens[localIndex]
                                let second = tokens[localIndex + 1]
                                let third = tokens[localIndex + 2]

                                if first.kind = Identifier
                                   && second.kind = Identifier
                                   && (third.kind = ShaderTokenKind.Equals
                                       || third.kind = ShaderTokenKind.Semicolon
                                       || third.kind = ShaderTokenKind.OpenBracket
                                       || third.kind = ShaderTokenKind.Colon
                                       || third.kind = ShaderTokenKind.Comma) then
                                    let lower = first.text.ToLowerInvariant()

                                    if not (keywords.Contains lower) then
                                        addSymbol
                                            LocalVariableSymbol
                                            second.text
                                            (parseTypeName first.text)
                                            { startOffset = first.span.startOffset
                                              endOffset = second.span.endOffset }
                                            second.span
                                            (scopeAtOffset second.span.startOffset)
                                            []
                                            None
                                            None
                                        |> ignore

                                localIndex <- localIndex + 1

                            index <- closeBrace + 1
                        | None -> index <- closeParen + 1
                    | None -> index <- index + 1
                elif braceDepth = 0
                     && token.kind = Identifier
                     && index + 1 < tokens.Length
                     && tokens[index + 1].kind = Identifier then
                    let nameToken = tokens[index + 1]
                    let symbolType = parseTypeName token.text
                    let symbolKind =
                        match symbolType with
                        | TextureType _
                        | BufferType _ -> ResourceSymbol
                        | SamplerType _ -> SamplerSymbol
                        | _ -> GlobalVariableSymbol
                    let endIndex =
                        seq { index + 1 .. min (tokens.Length - 1) (index + 16) }
                        |> Seq.tryFind (fun candidate -> tokens[candidate].kind = Semicolon)
                        |> Option.defaultValue (index + 1)
                    addSymbol
                        symbolKind
                        nameToken.text
                        symbolType
                        { startOffset = token.span.startOffset
                          endOffset = tokens[endIndex].span.endOffset }
                        nameToken.span
                        0
                        []
                        (semanticAfter tokens (index + 2) (endIndex + 1))
                        (parseBinding tokens (index + 2) (endIndex + 1))
                    |> ignore
                    index <- endIndex + 1
                else
                    index <- index + 1

        let extensionIsFxh = tree.filepath.EndsWith(".fxh", StringComparison.OrdinalIgnoreCase)

        if extensionIsFxh then
            parseStream (significantTokens tree 0 tree.text.Length)
        else
            let semanticNodes =
                PdxShaderSyntax.descendants tree.root
                |> Seq.filter (fun node ->
                    node.kind = HlslRegion || node.kind = VertexStruct || node.kind = ConstantBuffer)
                |> Seq.toList
            let covered = ResizeArray<TextSpan>()

            for node in semanticNodes do
                if not (covered |> Seq.exists (fun span -> node.span.startOffset >= span.startOffset && node.span.endOffset <= span.endOffset)) then
                    parseStream (significantTokens tree node.span.startOffset node.span.endOffset)
                    covered.Add node.span

        let callerForOffset offset =
            functionRegions
            |> Seq.tryFind (fun region -> offset >= region.bodyStart && offset < region.bodyEnd)

        let scopeParents =
            scopes |> Seq.map (fun scope -> scope.id, scope.parentId) |> Map.ofSeq

        let scopeChain scopeId =
            let rec collect current acc =
                match Map.tryFind current scopeParents with
                | Some(Some parent) -> collect parent (current :: acc)
                | _ -> List.rev (current :: acc)

            collect scopeId []

        let isValueSymbolKind =
            function
            | ParameterSymbol
            | GlobalVariableSymbol
            | LocalVariableSymbol
            | ConstantBufferSymbol
            | ResourceSymbol
            | SamplerSymbol
            | MacroSymbol -> true
            | _ -> false

        let visibleValueCandidates scopeId offset name =
            let sameName =
                symbols
                |> Seq.filter (fun symbol ->
                    symbol.name = name
                    && isValueSymbolKind symbol.kind
                    && symbol.selectionSpan.startOffset <= offset)
                |> Seq.toList

            scopeChain scopeId
            |> List.tryPick (fun candidateScope ->
                let inScope = sameName |> List.filter (fun symbol -> symbol.scopeId = candidateScope)
                if inScope.IsEmpty then None else Some inScope)
            |> Option.defaultValue []

        let structFields structName memberName =
            let ownerScopes =
                structTypeByScopeId
                |> Seq.choose (fun pair -> if pair.Value = structName then Some pair.Key else None)
                |> Set.ofSeq

            symbols
            |> Seq.filter (fun symbol ->
                symbol.kind = FieldSymbol
                && symbol.name = memberName
                && ownerScopes.Contains symbol.scopeId)
            |> Seq.toList

        let trySwizzleType receiverType (memberName: string) =
            let componentIndex (character: char) =
                [ "xyzw"; "rgba"; "stpq" ]
                |> List.tryPick (fun components ->
                    let index = components.IndexOf(character)
                    if index >= 0 then Some index else None)

            match receiverType with
            | VectorType(scalar, width) when memberName.Length >= 1 && memberName.Length <= 4 ->
                let valid =
                    memberName
                    |> Seq.forall (fun character ->
                        componentIndex character
                        |> Option.exists (fun index -> index < width))

                if valid then
                    if memberName.Length = 1 then Some(ScalarType scalar)
                    else Some(VectorType(scalar, memberName.Length))
                else None
            | _ -> None

        let memberCandidatesAndType receiverType memberName =
            match receiverType with
            | StructType structName ->
                let candidates = structFields structName memberName
                let memberType =
                    candidates
                    |> List.tryHead
                    |> Option.map _.symbolType
                    |> Option.defaultValue (UnknownType memberName)
                candidates, memberType
            | _ ->
                [], trySwizzleType receiverType memberName |> Option.defaultValue (UnknownType memberName)

        let argumentRanges (tokens: ShaderToken array) openIndex closeIndex =
            let ranges = ResizeArray<int * int>()
            let mutable startIndex = openIndex + 1
            let mutable depth = 0

            for index in openIndex + 1 .. closeIndex do
                let boundary = index = closeIndex || (tokens[index].kind = Comma && depth = 0)

                if boundary then
                    if index > startIndex then ranges.Add(startIndex, index - 1)
                    startIndex <- index + 1
                elif
                    tokens[index].kind = OpenParen
                    || tokens[index].kind = OpenBracket
                    || tokens[index].kind = OpenBrace
                then
                    depth <- depth + 1
                elif
                    tokens[index].kind = CloseParen
                    || tokens[index].kind = CloseBracket
                    || tokens[index].kind = CloseBrace
                then
                    depth <- max 0 (depth - 1)

            ranges |> Seq.toList

        let rec inferExpressionType scopeId (tokens: ShaderToken array) startIndex endIndex =
            if startIndex > endIndex || startIndex < 0 || endIndex >= tokens.Length then
                UnknownType ""
            elif
                tokens[startIndex].kind = OpenParen
                && matchingIndex OpenParen CloseParen tokens startIndex = Some endIndex
            then
                inferExpressionType scopeId tokens (startIndex + 1) (endIndex - 1)
            else
                let mutable depth = 0
                let mutable lastTopLevelDot = None

                for index in startIndex .. endIndex do
                    match tokens[index].kind with
                    | OpenParen
                    | OpenBracket
                    | OpenBrace -> depth <- depth + 1
                    | CloseParen
                    | CloseBracket
                    | CloseBrace -> depth <- max 0 (depth - 1)
                    | Dot when depth = 0 -> lastTopLevelDot <- Some index
                    | _ -> ()

                match lastTopLevelDot with
                | Some dotIndex when dotIndex + 1 <= endIndex && tokens[dotIndex + 1].kind = Identifier ->
                    let receiverType = inferExpressionType scopeId tokens startIndex (dotIndex - 1)
                    memberCandidatesAndType receiverType tokens[dotIndex + 1].text |> snd
                | _ when
                    startIndex + 1 <= endIndex
                    && tokens[startIndex].kind = Identifier
                    && tokens[startIndex + 1].kind = OpenParen
                    && matchingIndex OpenParen CloseParen tokens (startIndex + 1) = Some endIndex
                    ->
                    let name = tokens[startIndex].text
                    let parsedType = parseTypeName name
                    let isKnownConstructor =
                        match parsedType with
                        | StructType structName ->
                            symbols
                            |> Seq.exists (fun symbol -> symbol.kind = StructSymbol && symbol.name = structName)
                        | _ -> true

                    if isKnownConstructor then parsedType
                    else
                        let argumentTypes =
                            argumentRanges tokens (startIndex + 1) endIndex
                            |> List.map (fun (argumentStart, argumentEnd) ->
                                inferExpressionType scopeId tokens argumentStart argumentEnd)
                        let overloads =
                            symbols
                            |> Seq.filter (fun symbol -> symbol.kind = FunctionSymbol && symbol.name = name)
                            |> Seq.toList
                        resolveOverload argumentTypes overloads
                        |> List.tryHead
                        |> Option.map _.symbolType
                        |> Option.defaultValue (UnknownType name)
                | _ when startIndex = endIndex ->
                    match tokens[startIndex].kind with
                    | NumberLiteral ->
                        if tokens[startIndex].text.Contains(".", StringComparison.Ordinal)
                           || tokens[startIndex].text.Contains("e", StringComparison.OrdinalIgnoreCase)
                        then ScalarType Float
                        else ScalarType Int
                    | Identifier when tokens[startIndex].text = "true" || tokens[startIndex].text = "false" -> ScalarType Bool
                    | Identifier ->
                        visibleValueCandidates scopeId tokens[startIndex].span.startOffset tokens[startIndex].text
                        |> List.tryHead
                        |> Option.map _.symbolType
                        |> Option.defaultValue (UnknownType tokens[startIndex].text)
                    | _ -> UnknownType tokens[startIndex].text
                | _ ->
                    // For tolerant binding, use the first known operand type in
                    // a compound expression. This keeps overload selection useful
                    // without rejecting vendor-specific operators.
                    [ startIndex .. endIndex ]
                    |> List.choose (fun index ->
                        match tokens[index].kind with
                        | NumberLiteral
                        | Identifier ->
                            match inferExpressionType scopeId tokens index index with
                            | UnknownType _ -> None
                            | inferred -> Some inferred
                        | _ -> None)
                    |> List.tryHead
                    |> Option.defaultValue (UnknownType "expression")

        let callCandidates scopeId (tokens: ShaderToken array) index =
            let sameName =
                symbols
                |> Seq.filter (fun symbol -> symbol.kind = FunctionSymbol && symbol.name = tokens[index].text)
                |> Seq.toList

            if index + 1 >= tokens.Length || tokens[index + 1].kind <> OpenParen then
                sameName
            else
                match matchingIndex OpenParen CloseParen tokens (index + 1) with
                | None -> sameName
                | Some closeIndex ->
                    let argumentTypes =
                        argumentRanges tokens (index + 1) closeIndex
                        |> List.map (fun (argumentStart, argumentEnd) ->
                            inferExpressionType scopeId tokens argumentStart argumentEnd)
                    let resolved = resolveOverload argumentTypes sameName
                    if resolved.IsEmpty then sameName else resolved

        let candidatesFor (tokens: ShaderToken array) index scopeId offset name kind =
            match kind with
            | MemberReference when index >= 2 ->
                let mutable receiverStart = index - 2

                while (receiverStart >= 2
                       && tokens[receiverStart - 1].kind = Dot
                       && tokens[receiverStart - 2].kind = Identifier) do
                    receiverStart <- receiverStart - 2

                let receiverType = inferExpressionType scopeId tokens receiverStart (index - 2)
                memberCandidatesAndType receiverType name |> fst
            | MemberReference -> []
            | CallReference -> callCandidates scopeId tokens index
            | TypeReference ->
                symbols
                |> Seq.filter (fun symbol ->
                    symbol.name = name
                    && (symbol.kind = StructSymbol || symbol.kind = TypeSymbol))
                |> Seq.toList
            | _ -> visibleValueCandidates scopeId offset name

        let scanReferences (tokens: ShaderToken array) =
            for index in 0 .. tokens.Length - 1 do
                let token = tokens[index]

                if token.kind = ShaderTokenKind.Identifier
                   && not (declarationSpans.Contains(token.span.startOffset, token.span.endOffset))
                   && not (keywords.Contains(token.text.ToLowerInvariant())) then
                    let previous = if index > 0 then Some tokens[index - 1] else None
                    let next = if index + 1 < tokens.Length then Some tokens[index + 1] else None
                    let kind =
                        match previous, next with
                        | Some previousToken, _ when previousToken.kind = ShaderTokenKind.Dot -> MemberReference
                        | _, Some nextToken when nextToken.kind = ShaderTokenKind.OpenParen -> CallReference
                        | _, Some nextToken when nextToken.kind = ShaderTokenKind.Identifier -> TypeReference
                        | _, Some nextToken when nextToken.kind = ShaderTokenKind.Equals -> WriteReference
                        | _ -> ReadReference
                    let scopeId = scopeAtOffset token.span.startOffset
                    let candidates = candidatesFor tokens index scopeId token.span.startOffset token.text kind
                    let condition = conditionAt token.span.startOffset preprocessor
                    let stage = stageAt stageSpans token.span.startOffset
                    let reference =
                        { name = token.text
                          kind = kind
                          span = token.span
                          scopeId = scopeId
                          condition = condition
                          stage = stage
                          candidateIds = candidates |> List.map _.id }
                    references.Add reference

                    if kind = CallReference then
                        let caller = callerForOffset token.span.startOffset
                        calls.Add(
                            { callerId = caller |> Option.map _.symbolId
                              calleeIds = reference.candidateIds
                              span = token.span
                              condition = condition }
                        )

                        let pixelOnly =
                            token.text.Equals("ddx", StringComparison.OrdinalIgnoreCase)
                            || token.text.Equals("ddy", StringComparison.OrdinalIgnoreCase)
                            || token.text.Equals("fwidth", StringComparison.OrdinalIgnoreCase)
                            || token.text.Equals("clip", StringComparison.OrdinalIgnoreCase)

                        if pixelOnly && stage = VertexStage then
                            diagnostics.Add(
                                { code = "CWFX402"
                                  message = sprintf "%s is only valid in a pixel-stage entry point." token.text
                                  span = token.span
                                  condition = condition
                                  stage = stage }
                            )

        if extensionIsFxh then
            scanReferences (significantTokens tree 0 tree.text.Length)
        else
            for node in PdxShaderSyntax.nodesOfKind ShaderNodeKind.HlslRegion tree do
                scanReferences (significantTokens tree node.span.startOffset node.span.endOffset)

        symbols
        |> Seq.choose (fun symbol -> symbol.binding |> Option.map (fun binding -> symbol, binding))
        |> Seq.groupBy (fun (_, binding) -> binding.registerClass, binding.registerIndex)
        |> Seq.iter (fun ((registerClass, registerIndex), entries) ->
            let entries = entries |> Seq.map fst |> Seq.toList

            if entries.Length > 1 then
                for entry in entries do
                    let possibleConflict =
                        entries
                        |> List.exists (fun other ->
                            other.id <> entry.id
                            && satisfiable (conjunction entry.condition other.condition) <> ConditionFalse)

                    if possibleConflict then
                        diagnostics.Add(
                            { code = "CWFX403"
                              message = sprintf "Resource binding %s%d may be declared more than once." registerClass registerIndex
                              span = entry.selectionSpan
                              condition = entry.condition
                              stage = entry.stage }
                        ))

        { symbols = symbols |> Seq.distinctBy _.id |> Seq.toList
          references = references |> Seq.toList
          scopes = scopes |> Seq.toList
          diagnostics = diagnostics |> Seq.toList
          calls = calls |> Seq.toList }

    let analyzeText filepath text =
        let syntax = PdxShaderSyntax.parse filepath text
        let preprocessor = PdxShaderPreprocessor.analyze syntax
        syntax, preprocessor, analyze syntax preprocessor
