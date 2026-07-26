namespace CWTools.Games

open System
open System.Collections.Generic

/// Lossless, error-tolerant syntax front-end for the Paradox shader DSL.
/// Tokens cover the complete input (including trivia and malformed text) and
/// nodes retain offsets into the original UTF-16 string used by LSP.
module PdxShaderSyntax =
    [<Struct>]
    type TextSpan =
        { startOffset: int
          endOffset: int }

        member this.Length = max 0 (this.endOffset - this.startOffset)

    type ShaderTokenKind =
        | Identifier
        | NumberLiteral
        | StringLiteral
        | Whitespace
        | NewLine
        | LineComment
        | BlockComment
        | DirectiveLine
        | HlslOpen
        | HlslClose
        | OpenBrace
        | CloseBrace
        | OpenParen
        | CloseParen
        | OpenBracket
        | CloseBracket
        | Comma
        | Semicolon
        | Colon
        | Equals
        | Dot
        | Operator
        | BadToken
        | EndOfFile

    type ShaderToken =
        { kind: ShaderTokenKind
          text: string
          span: TextSpan }

    type SyntaxDiagnosticKind =
        | UnterminatedString
        | UnterminatedComment
        | UnterminatedBlock
        | UnterminatedHlslRegion
        | UnexpectedClosingDelimiter
        | MissingName

    type SyntaxDiagnostic =
        { kind: SyntaxDiagnosticKind
          message: string
          span: TextSpan }

    type ShaderNodeKind =
        | ShaderDocument
        | Includes
        | IncludeFile
        | VertexShader
        | PixelShader
        | GeometryShader
        | MainCode
        | VertexStruct
        | ConstantBuffer
        | BlendState
        | DepthStencilState
        | RasterizerState
        | Samplers
        | Sampler
        | Effect
        | Property
        | HlslRegion
        | PreprocessorDirective
        | UnknownNode

    type ShaderSyntaxNode =
        { kind: ShaderNodeKind
          name: string option
          span: TextSpan
          nameSpan: TextSpan option
          tokenStart: int
          tokenEnd: int
          children: ShaderSyntaxNode list }

    type ShaderSyntaxTree =
        { filepath: string
          text: string
          tokens: ShaderToken array
          root: ShaderSyntaxNode
          diagnostics: SyntaxDiagnostic list }

        member this.IsLossless =
            this.tokens
            |> Array.filter (fun token -> token.kind <> EndOfFile)
            |> Array.mapi (fun index token -> index, token)
            |> Array.forall (fun (index, token) ->
                let expectedStart =
                    if index = 0 then 0 else this.tokens[index - 1].span.endOffset

                token.span.startOffset = expectedStart)
            && (this.tokens.Length = 0
                || this.tokens[this.tokens.Length - 1].span.endOffset = this.text.Length)

    let private span startOffset endOffset =
        { startOffset = startOffset
          endOffset = max startOffset endOffset }

    let private directiveNames =
        set
            [ "if"
              "ifdef"
              "ifndef"
              "elif"
              "else"
              "endif"
              "define"
              "undef"
              "include"
              "pragma"
              "error"
              "line" ]

    let private isIdentifierStart character =
        Char.IsLetter character || character = '_' || character = '$'

    let private isIdentifierPart character =
        Char.IsLetterOrDigit character || character = '_' || character = '$'

    let private isNewline character = character = '\r' || character = '\n'

    let private consumeLine (text: string) startOffset =
        let mutable current = startOffset

        while current < text.Length && not (isNewline text[current]) do
            current <- current + 1

        current

    let private isDirectiveAt (text: string) offset lineHasContent =
        if lineHasContent || offset >= text.Length || (text[offset] <> '#' && text[offset] <> '@') then
            false
        else
            let mutable current = offset + 1

            while current < text.Length && (text[current] = ' ' || text[current] = '\t') do
                current <- current + 1

            let wordStart = current

            while current < text.Length && Char.IsLetter text[current] do
                current <- current + 1

            current > wordStart
            && directiveNames.Contains(text.Substring(wordStart, current - wordStart).ToLowerInvariant())

    let lex (text: string) : ShaderToken array * SyntaxDiagnostic list =
        let tokens = ResizeArray<ShaderToken>()
        let diagnostics = ResizeArray<SyntaxDiagnostic>()
        let mutable offset = 0
        let mutable lineHasContent = false

        let add kind startOffset endOffset =
            tokens.Add(
                { kind = kind
                  text = text.Substring(startOffset, max 0 (endOffset - startOffset))
                  span = span startOffset endOffset }
            )

        while offset < text.Length do
            let startOffset = offset
            let character = text[offset]

            if character = '\r' || character = '\n' then
                if character = '\r' && offset + 1 < text.Length && text[offset + 1] = '\n' then
                    offset <- offset + 2
                else
                    offset <- offset + 1

                add NewLine startOffset offset
                lineHasContent <- false
            elif character = ' ' || character = '\t' || character = '\u000C' then
                while offset < text.Length && (text[offset] = ' ' || text[offset] = '\t' || text[offset] = '\u000C') do
                    offset <- offset + 1

                add Whitespace startOffset offset
            elif isDirectiveAt text offset lineHasContent then
                offset <- consumeLine text offset
                add DirectiveLine startOffset offset
                lineHasContent <- true
            elif character = '#' then
                offset <- consumeLine text offset
                add LineComment startOffset offset
                lineHasContent <- true
            elif character = '/' && offset + 1 < text.Length && text[offset + 1] = '/' then
                offset <- consumeLine text offset
                add LineComment startOffset offset
                lineHasContent <- true
            elif character = '/' && offset + 1 < text.Length && text[offset + 1] = '*' then
                offset <- offset + 2
                let mutable terminated = false

                while offset < text.Length && not terminated do
                    if offset + 1 < text.Length && text[offset] = '*' && text[offset + 1] = '/' then
                        offset <- offset + 2
                        terminated <- true
                    else
                        offset <- offset + 1

                add BlockComment startOffset offset
                lineHasContent <- true

                if not terminated then
                    diagnostics.Add(
                        { kind = UnterminatedComment
                          message = "Unterminated block comment."
                          span = span startOffset offset }
                    )
            elif character = '"' || character = '\'' then
                let quote = character
                offset <- offset + 1
                let mutable terminated = false

                while offset < text.Length && not terminated && not (isNewline text[offset]) do
                    if text[offset] = '\\' && offset + 1 < text.Length then
                        offset <- offset + 2
                    elif text[offset] = quote then
                        offset <- offset + 1
                        terminated <- true
                    else
                        offset <- offset + 1

                add StringLiteral startOffset offset
                lineHasContent <- true

                if not terminated then
                    diagnostics.Add(
                        { kind = UnterminatedString
                          message = "Unterminated string literal."
                          span = span startOffset offset }
                    )
            elif character = '[' && offset + 1 < text.Length && text[offset + 1] = '[' then
                offset <- offset + 2
                add HlslOpen startOffset offset
                lineHasContent <- true
            elif character = ']' && offset + 1 < text.Length && text[offset + 1] = ']' then
                offset <- offset + 2
                add HlslClose startOffset offset
                lineHasContent <- true
            elif isIdentifierStart character || (character = '@' && offset + 1 < text.Length && isIdentifierStart text[offset + 1]) then
                offset <- offset + 1

                while offset < text.Length && isIdentifierPart text[offset] do
                    offset <- offset + 1

                add Identifier startOffset offset
                lineHasContent <- true
            elif Char.IsDigit character || (character = '.' && offset + 1 < text.Length && Char.IsDigit text[offset + 1]) then
                offset <- offset + 1

                while offset < text.Length
                      && (Char.IsLetterOrDigit text[offset]
                          || text[offset] = '.'
                          || text[offset] = '_') do
                    offset <- offset + 1

                add NumberLiteral startOffset offset
                lineHasContent <- true
            else
                let kind, width =
                    match character with
                    | '{' -> OpenBrace, 1
                    | '}' -> CloseBrace, 1
                    | '(' -> OpenParen, 1
                    | ')' -> CloseParen, 1
                    | '[' -> OpenBracket, 1
                    | ']' -> CloseBracket, 1
                    | ',' -> Comma, 1
                    | ';' -> Semicolon, 1
                    | ':' -> Colon, 1
                    | '=' when offset + 1 < text.Length && text[offset + 1] = '=' -> Operator, 2
                    | '=' -> Equals, 1
                    | '.' -> Dot, 1
                    | '+'
                    | '-'
                    | '*'
                    | '/'
                    | '%'
                    | '!'
                    | '<'
                    | '>'
                    | '&'
                    | '|'
                    | '^'
                    | '~'
                    | '?' ->
                        let next = if offset + 1 < text.Length then text[offset + 1] else '\u0000'
                        let width =
                            if (character = '&' && next = '&')
                               || (character = '|' && next = '|')
                               || next = '='
                               || (character = '<' && next = '<')
                               || (character = '>' && next = '>') then
                                2
                            else
                                1

                        Operator, width
                    | _ -> BadToken, 1

                offset <- offset + width
                add kind startOffset offset
                lineHasContent <- true

        tokens.Add(
            { kind = EndOfFile
              text = ""
              span = span text.Length text.Length }
        )

        tokens.ToArray(), diagnostics |> Seq.toList

    let private isTrivia kind =
        kind = Whitespace || kind = NewLine || kind = LineComment || kind = BlockComment

    let private unquote (value: string) =
        if value.Length >= 2
           && ((value[0] = '"' && value[value.Length - 1] = '"')
               || (value[0] = '\'' && value[value.Length - 1] = '\'')) then
            value.Substring(1, value.Length - 2)
        else
            value

    let private classifyBlock (parentKind: ShaderNodeKind option) (keyword: string) =
        match keyword.ToLowerInvariant(), parentKind with
        | "includes", _ -> Includes
        | "vertexshader", _ -> VertexShader
        | "pixelshader", _ -> PixelShader
        | "geometryshader", _ -> GeometryShader
        | "vertexstruct", _ -> VertexStruct
        | "constantbuffer", _ -> ConstantBuffer
        | "blendstate", _ -> BlendState
        | "depthstencilstate", _ -> DepthStencilState
        | "rasterizerstate", _ -> RasterizerState
        | "samplers", _ -> Samplers
        | "effect", _ -> Effect
        | _, Some Samplers -> Sampler
        | _ -> Property

    let parse (filepath: string) (text: string) : ShaderSyntaxTree =
        let tokens, lexDiagnostics = lex text
        let diagnostics = ResizeArray<SyntaxDiagnostic>(lexDiagnostics)

        let nextSignificant index limit =
            let mutable current = index

            while current < limit && isTrivia tokens[current].kind do
                current <- current + 1

            current

        let findMatching openKind closeKind openIndex limit =
            let mutable depth = 0
            let mutable current = openIndex
            let mutable result = None

            while current < limit && Option.isNone result do
                if tokens[current].kind = openKind then
                    depth <- depth + 1
                elif tokens[current].kind = closeKind then
                    depth <- depth - 1

                    if depth = 0 then
                        result <- Some current

                current <- current + 1

            result

        let makeNode kind name nameSpan tokenStart tokenEnd children =
            let endIndex = min (tokens.Length - 1) (max tokenStart tokenEnd)

            { kind = kind
              name = name
              span = span tokens[tokenStart].span.startOffset tokens[endIndex].span.endOffset
              nameSpan = nameSpan
              tokenStart = tokenStart
              tokenEnd = endIndex
              children = children }

        let rec parseSequence parentKind startIndex endIndex =
            let nodes = ResizeArray<ShaderSyntaxNode>()
            let mutable current = startIndex

            while current < endIndex do
                let token = tokens[current]

                match token.kind with
                | kind when isTrivia kind -> current <- current + 1
                | DirectiveLine ->
                    nodes.Add(makeNode PreprocessorDirective None None current current [])
                    current <- current + 1
                | HlslOpen ->
                    match findMatching HlslOpen HlslClose current endIndex with
                    | Some closeIndex ->
                        nodes.Add(makeNode HlslRegion None None current closeIndex [])
                        current <- closeIndex + 1
                    | None ->
                        nodes.Add(makeNode HlslRegion None None current (endIndex - 1) [])
                        diagnostics.Add(
                            { kind = UnterminatedHlslRegion
                              message = "Unterminated embedded HLSL region; expected ]]."
                              span = span token.span.startOffset text.Length }
                        )
                        current <- endIndex
                | CloseBrace
                | CloseParen
                | CloseBracket
                | HlslClose ->
                    diagnostics.Add(
                        { kind = UnexpectedClosingDelimiter
                          message = "Unexpected closing delimiter."
                          span = token.span }
                    )
                    current <- current + 1
                | Identifier ->
                    let keyword = token.text
                    let afterKeyword = nextSignificant (current + 1) endIndex

                    if keyword.Equals("MainCode", StringComparison.OrdinalIgnoreCase) then
                        let nameIndex = afterKeyword
                        let hasName = nameIndex < endIndex && tokens[nameIndex].kind = Identifier
                        let searchStart = if hasName then nameIndex + 1 else afterKeyword
                        let hlslStart =
                            seq { nextSignificant searchStart endIndex .. endIndex - 1 }
                            |> Seq.tryFind (fun index -> tokens[index].kind = HlslOpen)

                        match hlslStart with
                        | Some openIndex ->
                            let closeIndex =
                                findMatching HlslOpen HlslClose openIndex endIndex
                                |> Option.defaultValue (endIndex - 1)
                            let children =
                                (parseSequence (Some MainCode) searchStart openIndex)
                                @ [ makeNode HlslRegion None None openIndex closeIndex [] ]
                            let name = if hasName then Some tokens[nameIndex].text else None
                            let nameRange = if hasName then Some tokens[nameIndex].span else None
                            nodes.Add(makeNode MainCode name nameRange current closeIndex children)

                            if not hasName then
                                diagnostics.Add(
                                    { kind = MissingName
                                      message = "MainCode requires a name."
                                      span = token.span }
                                )

                            if tokens[closeIndex].kind <> HlslClose then
                                diagnostics.Add(
                                    { kind = UnterminatedHlslRegion
                                      message = "Unterminated MainCode HLSL region; expected ]]."
                                      span = span tokens[openIndex].span.startOffset text.Length }
                                )

                            current <- closeIndex + 1
                        | None ->
                            let endToken = if hasName then nameIndex else current
                            nodes.Add(
                                makeNode
                                    MainCode
                                    (if hasName then Some tokens[nameIndex].text else None)
                                    (if hasName then Some tokens[nameIndex].span else None)
                                    current
                                    endToken
                                    []
                            )
                            current <- endToken + 1
                    else
                        let mutable scan = afterKeyword
                        let mutable nameIndex = None
                        let mutable isAssignment = false

                        if scan < endIndex && tokens[scan].kind = Identifier then
                            nameIndex <- Some scan
                            scan <- nextSignificant (scan + 1) endIndex

                        if scan < endIndex && tokens[scan].kind = Equals then
                            isAssignment <- true
                            scan <- nextSignificant (scan + 1) endIndex

                        if scan < endIndex && tokens[scan].kind = OpenParen then
                            if Option.isNone nameIndex
                               && keyword.Equals("ConstantBuffer", StringComparison.OrdinalIgnoreCase) then
                                let candidateName = nextSignificant (scan + 1) endIndex

                                if candidateName < endIndex && tokens[candidateName].kind = Identifier then
                                    nameIndex <- Some candidateName

                            match findMatching OpenParen CloseParen scan endIndex with
                            | Some closeParen -> scan <- nextSignificant (closeParen + 1) endIndex
                            | None -> scan <- endIndex

                        if scan < endIndex && tokens[scan].kind = OpenBrace then
                            let closeIndex = findMatching OpenBrace CloseBrace scan endIndex
                            let actualClose = closeIndex |> Option.defaultValue (endIndex - 1)
                            let nodeKind = classifyBlock parentKind keyword
                            let explicitName =
                                match nodeKind, nameIndex with
                                | Includes, _
                                | VertexShader, _
                                | PixelShader, _
                                | GeometryShader, _
                                | Samplers, _ -> None
                                | _, Some index -> Some tokens[index].text
                                | Sampler, None -> Some keyword
                                | Property, None -> Some keyword
                                | _ -> None
                            let explicitNameSpan =
                                match nodeKind, nameIndex with
                                | Includes, _
                                | VertexShader, _
                                | PixelShader, _
                                | GeometryShader, _
                                | Samplers, _ -> None
                                | _, Some index -> Some tokens[index].span
                                | Sampler, None -> Some token.span
                                | Property, None -> Some token.span
                                | _ -> None
                            let childNodes =
                                if nodeKind = Includes then
                                    let includes = ResizeArray<ShaderSyntaxNode>()
                                    let mutable includeIndex = scan + 1
                                    let mutable depth = 0

                                    while includeIndex < actualClose do
                                        match tokens[includeIndex].kind with
                                        | OpenBrace -> depth <- depth + 1
                                        | CloseBrace -> depth <- max 0 (depth - 1)
                                        | StringLiteral when depth = 0 ->
                                            includes.Add(
                                                makeNode
                                                    IncludeFile
                                                    (Some(unquote tokens[includeIndex].text))
                                                    (Some tokens[includeIndex].span)
                                                    includeIndex
                                                    includeIndex
                                                    []
                                            )
                                        | _ -> ()

                                        includeIndex <- includeIndex + 1

                                    includes |> Seq.toList
                                else
                                    parseSequence (Some nodeKind) (scan + 1) actualClose

                            nodes.Add(makeNode nodeKind explicitName explicitNameSpan current actualClose childNodes)

                            if Option.isNone closeIndex then
                                diagnostics.Add(
                                    { kind = UnterminatedBlock
                                      message = sprintf "Unterminated %s block; expected }." keyword
                                      span = span token.span.startOffset text.Length }
                                )

                            current <- actualClose + 1
                        else
                            let statementEnd =
                                let mutable probe = current
                                let mutable found = false

                                while probe + 1 < endIndex && not found do
                                    if tokens[probe].kind = Semicolon || tokens[probe].kind = NewLine then
                                        found <- true
                                    else
                                        probe <- probe + 1

                                probe
                            let nodeKind =
                                if keyword.Equals("Effect", StringComparison.OrdinalIgnoreCase) then Effect
                                elif keyword.Equals("VertexStruct", StringComparison.OrdinalIgnoreCase) then VertexStruct
                                elif keyword.Equals("ConstantBuffer", StringComparison.OrdinalIgnoreCase) then ConstantBuffer
                                elif isAssignment then Property
                                else UnknownNode
                            let nodeName =
                                if nodeKind = Property then Some keyword
                                else nameIndex |> Option.map (fun index -> tokens[index].text)
                            let nodeNameSpan =
                                if nodeKind = Property then Some token.span
                                else nameIndex |> Option.map (fun index -> tokens[index].span)
                            nodes.Add(makeNode nodeKind nodeName nodeNameSpan current statementEnd [])
                            current <- statementEnd + 1
                | _ ->
                    nodes.Add(makeNode UnknownNode None None current current [])
                    current <- current + 1

            nodes |> Seq.toList

        let children = parseSequence None 0 (tokens.Length - 1)

        let root =
            { kind = ShaderDocument
              name = None
              span = span 0 text.Length
              nameSpan = None
              tokenStart = 0
              tokenEnd = tokens.Length - 1
              children = children }

        { filepath = filepath
          text = text
          tokens = tokens
          root = root
          diagnostics = diagnostics |> Seq.toList }

    let rec descendants (node: ShaderSyntaxNode) =
        seq {
            for child in node.children do
                yield child
                yield! descendants child
        }

    let nodesOfKind kind (tree: ShaderSyntaxTree) =
        descendants tree.root |> Seq.filter (fun node -> node.kind = kind) |> Seq.toList

    let sourceText (tree: ShaderSyntaxTree) (node: ShaderSyntaxNode) =
        tree.text.Substring(node.span.startOffset, node.span.Length)
