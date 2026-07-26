namespace CWTools.Games

open System
open System.Collections.Generic
open PdxShaderSyntax

/// Variant-preserving preprocessor model shared by the DSL and HLSL layers.
/// It records branch presence conditions instead of discarding inactive text.
module PdxShaderPreprocessor =
    type PresenceCondition =
        | Always
        | Never
        | Defined of string
        | Symbol of string
        | Equals of string * string
        | Not of PresenceCondition
        | And of PresenceCondition list
        | Or of PresenceCondition list
        | UnknownCondition of string

    type ConditionValue =
        | ConditionTrue
        | ConditionFalse
        | ConditionUnknown

    type PreprocessorDirectiveKind =
        | If
        | IfDef
        | IfNDef
        | Elif
        | Else
        | EndIf
        | Define
        | Undef
        | Include
        | Pragma
        | Error
        | UnknownDirective

    type MacroKind =
        | ObjectLike
        | FunctionLike of parameters: string list
        | EnginePredefined

    type MacroDefinition =
        { name: string
          kind: MacroKind
          replacement: string
          span: TextSpan
          condition: PresenceCondition }

    type PreprocessorDirective =
        { kind: PreprocessorDirectiveKind
          keyword: string
          argument: string
          span: TextSpan
          condition: PresenceCondition }

    type PresenceRegion =
        { span: TextSpan
          condition: PresenceCondition }

    type PreprocessorDiagnostic =
        { code: string
          message: string
          span: TextSpan }

    type PreprocessorResult =
        { directives: PreprocessorDirective list
          macros: MacroDefinition list
          regions: PresenceRegion list
          diagnostics: PreprocessorDiagnostic list }

    type MacroEnvironment =
        { defined: Set<string>
          values: Map<string, string> }

    type PlatformVariant =
        { name: string
          environment: MacroEnvironment }

    type VariantCondition =
        { condition: PresenceCondition
          activeVariants: string list
          unknownVariants: string list }

    type private ExpressionToken =
        | ExpressionIdentifier of string
        | ExpressionNumber of string
        | ExpressionNot
        | ExpressionAnd
        | ExpressionOr
        | ExpressionEquals
        | ExpressionNotEquals
        | ExpressionOpen
        | ExpressionClose
        | ExpressionOther of string

    type private BranchFrame =
        { parent: PresenceCondition
          taken: PresenceCondition
          current: PresenceCondition }

    let private conditionKey condition = sprintf "%A" condition

    let rec simplify condition =
        match condition with
        | Not Always -> Never
        | Not Never -> Always
        | Not(Not value) -> simplify value
        | Not value -> Not(simplify value)
        | And values ->
            let values =
                values
                |> List.collect (fun value ->
                    match simplify value with
                    | And nested -> nested
                    | simplified -> [ simplified ])
                |> List.filter ((<>) Always)
                |> List.distinctBy conditionKey

            if values |> List.contains Never then Never
            elif List.isEmpty values then Always
            elif values.Length = 1 then values.Head
            elif values |> List.exists (fun value -> values |> List.contains (Not value)) then Never
            else And values
        | Or values ->
            let values =
                values
                |> List.collect (fun value ->
                    match simplify value with
                    | Or nested -> nested
                    | simplified -> [ simplified ])
                |> List.filter ((<>) Never)
                |> List.distinctBy conditionKey

            if values |> List.contains Always then Always
            elif List.isEmpty values then Never
            elif values.Length = 1 then values.Head
            elif values |> List.exists (fun value -> values |> List.contains (Not value)) then Always
            else Or values
        | value -> value

    let conjunction left right = simplify (And [ left; right ])
    let disjunction left right = simplify (Or [ left; right ])
    let negate condition = simplify (Not condition)

    let private tokenizeExpression (text: string) =
        let tokens = ResizeArray<ExpressionToken>()
        let mutable offset = 0

        while offset < text.Length do
            let character = text[offset]

            if Char.IsWhiteSpace character then
                offset <- offset + 1
            elif Char.IsLetter character || character = '_' then
                let startOffset = offset
                offset <- offset + 1

                while offset < text.Length && (Char.IsLetterOrDigit text[offset] || text[offset] = '_') do
                    offset <- offset + 1

                tokens.Add(ExpressionIdentifier(text.Substring(startOffset, offset - startOffset)))
            elif Char.IsDigit character then
                let startOffset = offset
                offset <- offset + 1

                while offset < text.Length && (Char.IsLetterOrDigit text[offset] || text[offset] = '_') do
                    offset <- offset + 1

                tokens.Add(ExpressionNumber(text.Substring(startOffset, offset - startOffset)))
            else
                match character with
                | '!' when offset + 1 < text.Length && text[offset + 1] = '=' ->
                    tokens.Add ExpressionNotEquals
                    offset <- offset + 2
                | '!' ->
                    tokens.Add ExpressionNot
                    offset <- offset + 1
                | '&' when offset + 1 < text.Length && text[offset + 1] = '&' ->
                    tokens.Add ExpressionAnd
                    offset <- offset + 2
                | '|' when offset + 1 < text.Length && text[offset + 1] = '|' ->
                    tokens.Add ExpressionOr
                    offset <- offset + 2
                | '=' when offset + 1 < text.Length && text[offset + 1] = '=' ->
                    tokens.Add ExpressionEquals
                    offset <- offset + 2
                | '(' ->
                    tokens.Add ExpressionOpen
                    offset <- offset + 1
                | ')' ->
                    tokens.Add ExpressionClose
                    offset <- offset + 1
                | _ ->
                    tokens.Add(ExpressionOther(string character))
                    offset <- offset + 1

        tokens.ToArray()

    let parseCondition (text: string) =
        let tokens = tokenizeExpression text
        let mutable position = 0

        let current () =
            if position < tokens.Length then Some tokens[position] else None

        let advance () = position <- position + 1

        let rec parseOr () =
            let mutable left = parseAnd ()
            let mutable keepParsing = true

            while keepParsing do
                match current () with
                | Some ExpressionOr ->
                    advance ()
                    left <- disjunction left (parseAnd ())
                | _ -> keepParsing <- false

            left

        and parseAnd () =
            let mutable left = parseEquality ()
            let mutable keepParsing = true

            while keepParsing do
                match current () with
                | Some ExpressionAnd ->
                    advance ()
                    left <- conjunction left (parseEquality ())
                | _ -> keepParsing <- false

            left

        and parseEquality () =
            let left = parseUnary ()

            match current () with
            | Some ExpressionEquals
            | Some ExpressionNotEquals as operator ->
                advance ()
                let right = parseUnary ()
                let asValue = function
                    | Symbol name -> Some name
                    | Defined name -> Some name
                    | Always -> Some "1"
                    | Never -> Some "0"
                    | _ -> None

                match asValue left, asValue right with
                | Some leftValue, Some rightValue ->
                    let equality = Equals(leftValue, rightValue)

                    match operator with
                    | Some ExpressionNotEquals -> negate equality
                    | _ -> equality
                | _ -> UnknownCondition text
            | _ -> left

        and parseUnary () =
            match current () with
            | Some ExpressionNot ->
                advance ()
                negate (parseUnary ())
            | _ -> parsePrimary ()

        and parsePrimary () =
            match current () with
            | Some(ExpressionIdentifier name) when name.Equals("defined", StringComparison.OrdinalIgnoreCase) ->
                advance ()

                match current () with
                | Some ExpressionOpen ->
                    advance ()

                    match current () with
                    | Some(ExpressionIdentifier symbol) ->
                        advance ()
                        if current () = Some ExpressionClose then advance ()
                        Defined symbol
                    | _ -> UnknownCondition text
                | Some(ExpressionIdentifier symbol) ->
                    advance ()
                    Defined symbol
                | _ -> UnknownCondition text
            | Some(ExpressionIdentifier name) ->
                advance ()
                Symbol name
            | Some(ExpressionNumber number) ->
                advance ()
                if number = "0" then Never elif number = "1" then Always else Symbol number
            | Some ExpressionOpen ->
                advance ()
                let value = parseOr ()
                if current () = Some ExpressionClose then advance ()
                value
            | Some token ->
                advance ()
                UnknownCondition(sprintf "%A" token)
            | None -> UnknownCondition text

        let result = parseOr () |> simplify
        if position < tokens.Length then UnknownCondition text else result

    let private splitDirective (raw: string) =
        let trimmed = raw.TrimStart()
        let body =
            if trimmed.StartsWith("#") || trimmed.StartsWith("@") then trimmed.Substring(1).TrimStart()
            else trimmed
        let mutable index = 0

        while index < body.Length && Char.IsLetter body[index] do
            index <- index + 1

        let keyword = body.Substring(0, index).ToLowerInvariant()
        let argument = if index < body.Length then body.Substring(index).Trim() else ""
        keyword, argument

    let private directiveKind keyword =
        match keyword with
        | "if" -> If
        | "ifdef" -> IfDef
        | "ifndef" -> IfNDef
        | "elif" -> Elif
        | "else" -> Else
        | "endif" -> EndIf
        | "define" -> Define
        | "undef" -> Undef
        | "include" -> Include
        | "pragma" -> Pragma
        | "error" -> Error
        | _ -> UnknownDirective

    let private firstIdentifier (text: string) =
        let mutable startOffset = 0

        while startOffset < text.Length && not (Char.IsLetter text[startOffset] || text[startOffset] = '_') do
            startOffset <- startOffset + 1

        let mutable endOffset = startOffset

        while endOffset < text.Length && (Char.IsLetterOrDigit text[endOffset] || text[endOffset] = '_') do
            endOffset <- endOffset + 1

        if endOffset > startOffset then text.Substring(startOffset, endOffset - startOffset) else ""

    let private parseMacro argument directiveSpan condition =
        let name = firstIdentifier argument

        if String.IsNullOrEmpty name then
            None
        else
            let nameStart = argument.IndexOf(name, StringComparison.Ordinal)
            let afterName = nameStart + name.Length

            if afterName < argument.Length && argument[afterName] = '(' then
                let mutable closeIndex = afterName + 1
                let mutable depth = 1

                while closeIndex < argument.Length && depth > 0 do
                    if argument[closeIndex] = '(' then depth <- depth + 1
                    elif argument[closeIndex] = ')' then depth <- depth - 1
                    closeIndex <- closeIndex + 1

                let parameterText =
                    if depth = 0 then argument.Substring(afterName + 1, closeIndex - afterName - 2) else ""
                let parameters =
                    parameterText.Split([| ',' |], StringSplitOptions.RemoveEmptyEntries)
                    |> Array.map _.Trim()
                    |> Array.filter (String.IsNullOrWhiteSpace >> not)
                    |> Array.toList
                let replacement = if closeIndex < argument.Length then argument.Substring(closeIndex).Trim() else ""

                Some
                    { name = name
                      kind = FunctionLike parameters
                      replacement = replacement
                      span = directiveSpan
                      condition = condition }
            else
                let replacement = if afterName < argument.Length then argument.Substring(afterName).Trim() else ""

                Some
                    { name = name
                      kind = ObjectLike
                      replacement = replacement
                      span = directiveSpan
                      condition = condition }

    let analyze (tree: ShaderSyntaxTree) : PreprocessorResult =
        let directives = ResizeArray<PreprocessorDirective>()
        let macros = ResizeArray<MacroDefinition>()
        let regions = ResizeArray<PresenceRegion>()
        let diagnostics = ResizeArray<PreprocessorDiagnostic>()
        let stack = Stack<BranchFrame>()
        let mutable currentCondition = Always
        let mutable regionStart = 0

        let addRegion endOffset =
            if endOffset > regionStart then
                regions.Add(
                    { span =
                        { startOffset = regionStart
                          endOffset = endOffset }
                      condition = currentCondition }
                )

        for token in tree.tokens do
            if token.kind = DirectiveLine then
                addRegion token.span.startOffset
                let keyword, argument = splitDirective token.text
                let kind = directiveKind keyword

                directives.Add(
                    { kind = kind
                      keyword = keyword
                      argument = argument
                      span = token.span
                      condition = currentCondition }
                )

                match kind with
                | If
                | IfDef
                | IfNDef ->
                    let branch =
                        match kind with
                        | If -> parseCondition argument
                        | IfDef -> Defined(firstIdentifier argument)
                        | _ -> negate (Defined(firstIdentifier argument))
                    let frame =
                        { parent = currentCondition
                          taken = branch
                          current = conjunction currentCondition branch }
                    stack.Push frame
                    currentCondition <- frame.current
                | Elif ->
                    if stack.Count = 0 then
                        diagnostics.Add(
                            { code = "CWFX103"
                              message = "Unexpected preprocessor elif without a matching if."
                              span = token.span }
                        )
                    else
                        let previous = stack.Pop()
                        let branch = parseCondition argument
                        let available = conjunction (negate previous.taken) branch
                        let frame =
                            { parent = previous.parent
                              taken = disjunction previous.taken branch
                              current = conjunction previous.parent available }
                        stack.Push frame
                        currentCondition <- frame.current
                | Else ->
                    if stack.Count = 0 then
                        diagnostics.Add(
                            { code = "CWFX103"
                              message = "Unexpected preprocessor else without a matching if."
                              span = token.span }
                        )
                    else
                        let previous = stack.Pop()
                        let frame =
                            { parent = previous.parent
                              taken = Always
                              current = conjunction previous.parent (negate previous.taken) }
                        stack.Push frame
                        currentCondition <- frame.current
                | EndIf ->
                    if stack.Count = 0 then
                        diagnostics.Add(
                            { code = "CWFX103"
                              message = "Unexpected preprocessor endif without a matching if."
                              span = token.span }
                        )
                    else
                        currentCondition <- stack.Pop().parent
                | Define ->
                    match parseMacro argument token.span currentCondition with
                    | Some macro -> macros.Add macro
                    | None ->
                        diagnostics.Add(
                            { code = "CWFX104"
                              message = "Macro definition is missing a valid name."
                              span = token.span }
                        )
                | _ -> ()

                regionStart <- token.span.endOffset

        addRegion tree.text.Length

        if stack.Count > 0 then
            diagnostics.Add(
                { code = "CWFX102"
                  message = sprintf "%d preprocessor condition block(s) are not closed." stack.Count
                  span =
                    { startOffset = tree.text.Length
                      endOffset = tree.text.Length } }
            )

        { directives = directives |> Seq.toList
          macros = macros |> Seq.toList
          regions = regions |> Seq.toList
          diagnostics = diagnostics |> Seq.toList }

    let conditionAt offset (result: PreprocessorResult) =
        result.regions
        |> List.tryFind (fun region -> offset >= region.span.startOffset && offset < region.span.endOffset)
        |> Option.map _.condition
        |> Option.defaultValue Always

    let rec evaluate (environment: MacroEnvironment) condition =
        let combineAnd values =
            if values |> List.contains ConditionFalse then ConditionFalse
            elif values |> List.contains ConditionUnknown then ConditionUnknown
            else ConditionTrue
        let combineOr values =
            if values |> List.contains ConditionTrue then ConditionTrue
            elif values |> List.contains ConditionUnknown then ConditionUnknown
            else ConditionFalse

        match simplify condition with
        | Always -> ConditionTrue
        | Never -> ConditionFalse
        | Defined name -> if environment.defined.Contains name then ConditionTrue else ConditionFalse
        | Symbol name ->
            match environment.values.TryFind name with
            | Some "0" -> ConditionFalse
            | Some _ -> ConditionTrue
            | None -> if environment.defined.Contains name then ConditionTrue else ConditionFalse
        | Equals(left, right) ->
            let resolve value = environment.values.TryFind value |> Option.defaultValue value
            if resolve left = resolve right then ConditionTrue else ConditionFalse
        | Not value ->
            match evaluate environment value with
            | ConditionTrue -> ConditionFalse
            | ConditionFalse -> ConditionTrue
            | ConditionUnknown -> ConditionUnknown
        | And values -> values |> List.map (evaluate environment) |> combineAnd
        | Or values -> values |> List.map (evaluate environment) |> combineOr
        | UnknownCondition _ -> ConditionUnknown

    let symbols condition =
        let rec collect accumulator = function
            | Defined name
            | Symbol name -> Set.add name accumulator
            | Equals(left, right) -> accumulator |> Set.add left |> Set.add right
            | Not value -> collect accumulator value
            | And values
            | Or values -> values |> List.fold collect accumulator
            | Always
            | Never
            | UnknownCondition _ -> accumulator

        collect Set.empty condition

    let satisfiable condition =
        let names = symbols condition |> Set.toArray

        if names.Length > 12 then
            ConditionUnknown
        else
            let combinations = 1 <<< names.Length
            let mutable result = ConditionFalse
            let mutable mask = 0

            while mask < combinations && result <> ConditionTrue do
                let defined =
                    names
                    |> Array.mapi (fun index name -> index, name)
                    |> Array.choose (fun (index, name) -> if (mask &&& (1 <<< index)) <> 0 then Some name else None)
                    |> Set.ofArray
                let value = evaluate { defined = defined; values = Map.empty } condition
                if value = ConditionTrue then result <- ConditionTrue
                elif value = ConditionUnknown then result <- ConditionUnknown
                mask <- mask + 1

            result

    let defaultPlatformVariants =
        [ { name = "directx11"
            environment =
                { defined = set [ "PDX_DIRECTX_11"; "PDX_WINDOWS" ]
                  values = Map.empty } }
          { name = "opengl"
            environment =
                { defined = set [ "PDX_OPENGL" ]
                  values = Map.empty } }
          { name = "pssl"
            environment =
                { defined = set [ "PDX_PSSL" ]
                  values = Map.empty } } ]

    let compareVariants variants conditions =
        conditions
        |> Seq.distinctBy conditionKey
        |> Seq.map (fun condition ->
            let active, unknown =
                variants
                |> List.fold
                    (fun (active, unknown) variant ->
                        match evaluate variant.environment condition with
                        | ConditionTrue -> variant.name :: active, unknown
                        | ConditionUnknown -> active, variant.name :: unknown
                        | ConditionFalse -> active, unknown)
                    ([], [])

            { condition = condition
              activeVariants = List.rev active
              unknownVariants = List.rev unknown })
        |> Seq.toList

    type ExpandedFragment =
        { text: string
          sourceSpan: TextSpan
          expansionStack: string list }

    let expandObjectMacro maxDepth (environment: MacroEnvironment) (macros: MacroDefinition list) name =
        let byName =
            macros
            |> List.choose (fun macro ->
                match macro.kind with
                | ObjectLike when evaluate environment macro.condition <> ConditionFalse -> Some(macro.name, macro)
                | _ -> None)
            |> Map.ofList

        let rec expand depth stack currentName =
            if depth >= maxDepth || List.contains currentName stack then
                { text = currentName
                  sourceSpan =
                    { startOffset = 0
                      endOffset = 0 }
                  expansionStack = List.rev (currentName :: stack) }
            else
                match byName.TryFind currentName with
                | None ->
                    { text = currentName
                      sourceSpan =
                        { startOffset = 0
                          endOffset = 0 }
                      expansionStack = List.rev stack }
                | Some macro ->
                    let replacementName = macro.replacement.Trim()

                    if replacementName <> ""
                       && replacementName |> Seq.forall (fun character -> Char.IsLetterOrDigit character || character = '_') then
                        expand (depth + 1) (currentName :: stack) replacementName
                    else
                        { text = macro.replacement
                          sourceSpan = macro.span
                          expansionStack = List.rev (currentName :: stack) }

        expand 0 [] name
