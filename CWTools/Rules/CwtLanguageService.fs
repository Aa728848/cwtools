namespace CWTools.CwtLanguage

open FParsec
open CWTools.Utilities.Position
open CWTools.Utilities.Utils
open CWTools.Common
open CWTools.Parser
open CWTools.Process
open CWTools.Process.STLProcess

/// Single-file CWT language service: parse, structure/expression diagnostics,
/// local symbols, and context completion. Built on the stable meta-model in
/// CwtLanguageSchema — never on the rules being edited (handoff doc §4.3).
module CwtLanguageService =

    let private mkRangeFile (filePath: string) (b: pos) (e: pos) = mkRange filePath b e

    // ---------------------------------------------------------------- parse

    type CwtParseResult =
        | ParseOk of Node
        | ParseError of string * pos

    let parseFile (filePath: string) (text: string) : CwtParseResult =
        match CKParser.parseString text filePath with
        | Failure(msg, p, _) ->
            let fp = p.Position
            ParseError(msg, mkPos (int fp.Line) (int fp.Column))
        | Success(s, _, _) ->
            let root = simpleProcess.ProcessNode () "root" (mkZeroFile filePath) s
            ParseOk root

    let private syntaxDiagnostic filePath msg p =
        { code = "CWT001"
          severity = Severity.Error
          messageKey = "cwt.syntaxError"
          messageArgs = [ msg ]
          range = mkRangeFile filePath p p
          phase = CwtDiagnosticPhase.Syntax
          related = [] }

    // ------------------------------------------------------------ directives

    /// Parses a comment line into a directive. CKParser removes the first `#`:
    /// a source `#` is plain text, source `##` starts with one `#` here, and
    /// source `###` starts with two. Only the middle form is a rule option.
    let tryParseDirective (comment: string) =
        let parserComment = comment.TrimStart()
        let isDirective =
            parserComment.StartsWith("#", System.StringComparison.Ordinal)
            && not (parserComment.StartsWith("##", System.StringComparison.Ordinal))
        let trimmed =
            if isDirective then parserComment.Substring(1).Trim()
            else ""

        if trimmed = "" then
            None
        else
            let equalsIndex = trimmed.IndexOf('=')

            if equalsIndex < 0 then
                let isNoneDirective name =
                    CwtMetaSchema.directives
                    |> List.exists (fun d ->
                        d.valueKind = "none" && d.name.Equals(name, System.StringComparison.OrdinalIgnoreCase))

                if isNoneDirective trimmed then Some(trimmed, None) else None
            else
                let name = trimmed.Substring(0, equalsIndex).Trim()

                let nameOk =
                    name.Length > 0
                    && name
                       |> Seq.forall (fun c -> System.Char.IsAsciiLetterLower c || c = '_')

                if nameOk then
                    let rawValue = trimmed.Substring(equalsIndex + 1).Trim()
                    let inlineComment = rawValue.IndexOf(" #", System.StringComparison.Ordinal)
                    let value =
                        if inlineComment >= 0 then rawValue.Substring(0, inlineComment).TrimEnd()
                        else rawValue
                    Some(name, Some value)
                else
                    None

    let private directiveValueRange (comment: string) (position: range) (valueStart: int) =
        // Comments are single-line (# to EOL); the value sits on the same
        // line as the comment start.
        let col = int64 position.StartColumn + int64 valueStart
        let endCol = col + int64 (max 1 (comment.Length - valueStart))
        mkRangeFile position.FileName (mkPos (int position.StartLine) (int col)) (mkPos (int position.StartLine) (int endCol))

    let private validateDirective (filePath: string) (comment: string) (position: range) =
        match tryParseDirective comment with
        | None -> []
        | Some(name, value) ->
            let mkDiag code severity messageKey args range =
                { code = code
                  severity = severity
                  messageKey = messageKey
                  messageArgs = args
                  range = range
                  phase = CwtDiagnosticPhase.Structure
                  related = [] }
            match CwtMetaSchema.tryDirective name, value with
            | None, Some _ ->
                [ mkDiag "CWT101" Severity.Warning "cwt.unknownDirective" [ name ] position ]
            | None, None -> []
            | Some directive, None ->
                if directive.valueKind = "none" then
                    []
                else
                    [ mkDiag "CWT104" Severity.Warning "cwt.directiveMissingValue" [ name ] position ]
            | Some directive, Some valueText ->
                let valueRange = directiveValueRange comment position (comment.IndexOf(valueText, System.StringComparison.Ordinal))
                let invalid () = [ mkDiag "CWT102" Severity.Error "cwt.illegalDirectiveValue" [ name; valueText ] valueRange ]
                match directive.valueKind with
                | "none" -> [ mkDiag "CWT104" Severity.Warning "cwt.directiveValueNotAllowed" [ name ] valueRange ]
                | "cardinality" ->
                    let bounds = valueText.Split("..")
                    let validBound s = s = "inf" || (s.Length > 0 && s |> Seq.forall System.Char.IsDigit)
                    let valid =
                        (valueText.StartsWith("~") |> not)
                        && bounds.Length = 2
                        && validBound bounds.[0]
                        && validBound bounds.[1]
                    if valid then [] else invalid ()
                | "severity" ->
                    match valueText.ToLowerInvariant() with
                    | "error" | "warning" | "info" | "information" | "hint" -> []
                    | _ -> invalid ()
                | "list" ->
                    if valueText.StartsWith("{") && valueText.EndsWith("}") then []
                    else invalid ()
                | "scope-map" ->
                    if valueText.StartsWith("{") && valueText.EndsWith("}") then []
                    else invalid ()
                | "inject" ->
                    if valueText.Contains("@") then [] else invalid ()
                | _ -> []

    // ----------------------------------------------------- field expressions

    /// Bracketed field-expression families whose arguments are validated.
    let private bracketedExpressions =
        set
            [ "int"; "float"; "value_field"; "int_value_field";
              "variable_field"; "int_variable_field"; "variable_field_32"; "int_variable_field_32";
              "enum"; "complex_enum"; "value"; "value_set";
              "dynamic_value"; "prefix_field"; "alias_name"; "alias_match_left";
              "single_alias_right"; "alias_keys_field"; "alias_params_field";
              "scope"; "scope_group"; "event_target"; "colour"; "color";
              "filepath"; "filename"; "icon"; "name_format"; "stellaris_name_format";
              "$tags"; "$tags_condition" ]

    /// Declaration prefixes that appear as keys (skipped by field validation).
    let private declarationPrefixes =
        set
            [ "type"; "subtype"; "enum"; "complex_enum"; "value"; "alias";
              "single_alias"; "scope_group" ]

    type FieldVerdict =
        | Literal
        | KnownField
        | UnknownStructured
        | MalformedKnown of string

    /// Classifies a single token (key or value) as a field expression.
    /// Arbitrary literals (`country`, `yes`, `"quoted"`, numbers) are Literal.
    let classifyFieldExpression (token: string) : FieldVerdict =
        let t = token.Trim()
        if t = "" then Literal
        elif t.StartsWith("\"") || t.EndsWith("\"") then Literal
        elif t = "yes" || t = "no" then Literal
        elif t |> Seq.forall (fun c -> System.Char.IsDigit c || c = '-' || c = '.' || c = ' ') then Literal
        else
            let bracketIdx = t.IndexOf('[')
            if bracketIdx > 0 then
                let name = t.Substring(0, bracketIdx)
                if not (t.EndsWith("]")) then UnknownStructured
                elif declarationPrefixes.Contains name then KnownField
                elif not (bracketedExpressions.Contains name) then UnknownStructured
                else
                    let args = t.Substring(bracketIdx + 1, t.Length - bracketIdx - 2)
                    if args = "" then MalformedKnown name
                    elif name = "int" || name = "float"
                         || name = "value_field" || name = "int_value_field"
                         || name = "variable_field" || name = "int_variable_field"
                         || name = "variable_field_32" || name = "int_variable_field_32" then
                        let bounds = args.Split("..")
                        let validBound s = s = "inf" || s = "-inf" || (s.Length > 0 && s |> Seq.forall (fun c -> System.Char.IsDigit c || c = '-' || c = '.'))
                        if bounds.Length = 2 && validBound bounds.[0] && validBound bounds.[1] then KnownField
                        else MalformedKnown name
                    else KnownField
            elif t.StartsWith("<") then
                if t.EndsWith(">") && t.Length > 2 then KnownField else UnknownStructured
            elif t.StartsWith("$") then
                if CwtMetaSchema.tryFieldExpression t |> Option.isSome then KnownField else UnknownStructured
            elif t.StartsWith("glob:") || t.StartsWith("glob.i:")
                 || t.StartsWith("ant:") || t.StartsWith("ant.i:")
                 || t.StartsWith("re:") || t.StartsWith("re.i:") then KnownField
            else
                match CwtMetaSchema.tryFieldExpression t with
                | Some _ -> KnownField
                | None -> Literal

    let private fieldDiag filePath code severity messageKey args range =
        { code = code
          severity = severity
          messageKey = messageKey
          messageArgs = args
          range = range
          phase = CwtDiagnosticPhase.Expression
          related = [] }

    // ------------------------------------------------------------ structure

    let private childNodes (clause: IClause) =
        clause.AllArray |> Array.toList

    let private keyOf (child: Child) =
        match child with
        | NodeC n -> Some(n.Key)
        | LeafC l -> Some(l.Key)
        | LeafValueC lv -> Some(lv.Key)
        | _ -> None

    let private rangeOf (child: Child) =
        match child with
        | NodeC n -> n.Position
        | LeafC l -> l.Position
        | LeafValueC lv -> lv.Position
        | CommentC c -> c.Position
        | ValueClauseC vc -> vc.Position

    /// Splits "type[planet_class]" into ("type", "planet_class").
    let trySplitDeclaration (key: string) =
        let idx = key.IndexOf('[')
        if idx > 0 && key.EndsWith("]") then
            Some(key.Substring(0, idx), key.Substring(idx + 1, key.Length - idx - 2))
        else None

    let private analyzeRoot (filePath: string) (root: Node) =
        let diagnostics = ResizeArray<CwtDiagnostic>()
        let mutable seenTypesRoot = false
        let mutable seenEnumsRoot = false
        let mutable seenValuesRoot = false

        for child in childNodes root do
            match keyOf child with
            | Some key when key = "types" ->
                seenTypesRoot <- true
                match child with
                | NodeC n ->
                    for inner in childNodes n do
                        match keyOf inner with
                        | Some k when k.StartsWith("type[") ->
                            match trySplitDeclaration k with
                            | Some(_, name) when name = "" ->
                                diagnostics.Add(fieldDiag filePath "CWT113" Severity.Error "cwt.emptyDeclaration" [ "type" ] (rangeOf inner))
                            | _ -> ()
                        | Some k when k.StartsWith("subtype[") || k = "localisation" -> ()
                        | Some _ ->
                            diagnostics.Add(fieldDiag filePath "CWT110" Severity.Warning "cwt.invalidTypesDeclaration" [] (rangeOf inner))
                        | None -> ()
                | _ -> ()
            | Some key when key = "enums" ->
                seenEnumsRoot <- true
                match child with
                | NodeC n ->
                    for inner in childNodes n do
                        match keyOf inner with
                        | Some k when k.StartsWith("enum[") || k.StartsWith("complex_enum[") ->
                            match trySplitDeclaration k with
                            | Some(_, name) when name = "" ->
                                diagnostics.Add(fieldDiag filePath "CWT113" Severity.Error "cwt.emptyDeclaration" [ "enum" ] (rangeOf inner))
                            | _ -> ()
                        | Some _ ->
                            diagnostics.Add(fieldDiag filePath "CWT111" Severity.Warning "cwt.invalidEnumsDeclaration" [] (rangeOf inner))
                        | None -> ()
                | _ -> ()
            | Some key when key = "values" ->
                seenValuesRoot <- true
                match child with
                | NodeC n ->
                    for inner in childNodes n do
                        match keyOf inner with
                        | Some k when k.StartsWith("value[") ->
                            match trySplitDeclaration k with
                            | Some(_, name) when name = "" ->
                                diagnostics.Add(fieldDiag filePath "CWT113" Severity.Error "cwt.emptyDeclaration" [ "value" ] (rangeOf inner))
                            | _ -> ()
                        | Some _ ->
                            diagnostics.Add(fieldDiag filePath "CWT112" Severity.Warning "cwt.invalidValuesDeclaration" [] (rangeOf inner))
                        | None -> ()
                | _ -> ()
            | _ -> ()

        // Field-expression validation on every leaf, plus directive validation
        // on every comment, anywhere in the tree.
        let rec walk (clause: IClause) =
            for c in childNodes clause do
                match c with
                | NodeC n -> walk n
                | ValueClauseC vc -> walk vc
                | LeafC l ->
                    let keyVerdict =
                        if l.KeyId.quoted then Literal
                        else classifyFieldExpression l.Key
                    // ValueText strips surrounding quotes, so quoted literals
                    // must be detected on the raw value string.
                    let valueVerdict =
                        if l.Value.ToString().StartsWith("\"") then Literal
                        else classifyFieldExpression l.ValueText
                    let diagFor token verdict =
                        match verdict with
                        | UnknownStructured ->
                            Some(fieldDiag filePath "CWT200" Severity.Warning "cwt.unknownFieldExpression" [ token ] l.Position)
                        | MalformedKnown name ->
                            Some(fieldDiag filePath "CWT201" Severity.Error "cwt.illegalFieldExpression" [ name; token ] l.Position)
                        | _ -> None
                    match valueVerdict with
                    | UnknownStructured | MalformedKnown _ ->
                        diagFor l.ValueText valueVerdict |> Option.iter diagnostics.Add
                    | _ ->
                        match keyVerdict with
                        | UnknownStructured | MalformedKnown _ ->
                            diagFor l.Key keyVerdict |> Option.iter diagnostics.Add
                        | _ -> ()
                | CommentC cm ->
                    diagnostics.AddRange(validateDirective filePath cm.Comment cm.Position)
                | _ -> ()

        walk root
        diagnostics |> Seq.toList

    /// Semantic diagnostics for a parsed document. Returns [] when the file
    /// does not parse (syntax diagnostics are produced by the caller).
    let semanticDiagnostics (filePath: string) (text: string) : CwtDiagnostic list =
        match parseFile filePath text with
        | ParseError _ -> []
        | ParseOk root -> analyzeRoot filePath root

    /// Public entry for project-level callers that already hold a parsed tree.
    let analyzeRootPublic (filePath: string) (root: Node) : CwtDiagnostic list =
        analyzeRoot filePath root

    // ------------------------------------------------------------- symbols

    let private symbol (kind: CwtSymbolKind) (name: string) (range: range) (filePath: string) : CwtSymbol =
        { kind = kind; name = name; range = range; filePath = filePath }

    let private splitDeclarationName (key: string) =
        trySplitDeclaration key |> Option.map snd

    /// Local symbols declared by a parsed document.
    let collectSymbols (filePath: string) (root: Node) : CwtSymbol list =
        let symbols = ResizeArray<CwtSymbol>()

        let addDeclaration kind key range =
            splitDeclarationName key
            |> Option.iter (fun name -> symbols.Add(symbol kind name range filePath))

        let rec collectNode (n: Node) =
            match n.Key with
            | k when k.StartsWith("alias[") ->
                addDeclaration CwtSymbolKind.CwtAlias k n.Position
            | k when k.StartsWith("single_alias[") ->
                addDeclaration CwtSymbolKind.CwtSingleAlias k n.Position
            | k when k = "aliases" ->
                for inner in childNodes n do
                    match inner with
                    | NodeC an when an.Key.StartsWith("alias[") ->
                        addDeclaration CwtSymbolKind.CwtAlias an.Key an.Position
                    | LeafC al when al.Key.StartsWith("alias[") ->
                        addDeclaration CwtSymbolKind.CwtAlias al.Key al.Position
                    | NodeC an when an.Key.StartsWith("single_alias[") ->
                        addDeclaration CwtSymbolKind.CwtSingleAlias an.Key an.Position
                    | LeafC al when al.Key.StartsWith("single_alias[") ->
                        addDeclaration CwtSymbolKind.CwtSingleAlias al.Key al.Position
                    | _ -> ()
            | k when k = "types" ->
                for inner in childNodes n do
                    match inner with
                    | NodeC t when t.Key.StartsWith("type[") ->
                        addDeclaration CwtSymbolKind.CwtType t.Key t.Position
                        for sub in childNodes t do
                            match keyOf sub with
                            | Some sk when sk.StartsWith("subtype[") ->
                                let name =
                                    splitDeclarationName sk |> Option.map (fun nm -> nm.TrimStart('!'))
                                name
                                |> Option.iter (fun nm ->
                                    symbols.Add(symbol CwtSymbolKind.CwtSubtype nm (rangeOf sub) filePath))
                            | _ -> ()
                    | _ -> ()
            | k when k = "enums" ->
                for inner in childNodes n do
                    match keyOf inner with
                    | Some ek when ek.StartsWith("complex_enum[") ->
                        addDeclaration CwtSymbolKind.CwtComplexEnum ek (rangeOf inner)
                    | Some ek when ek.StartsWith("enum[") ->
                        addDeclaration CwtSymbolKind.CwtEnum ek (rangeOf inner)
                    | _ -> ()
            | k when k = "values" ->
                for inner in childNodes n do
                    match keyOf inner with
                    | Some vk when vk.StartsWith("value[") ->
                        addDeclaration CwtSymbolKind.CwtValueSet vk (rangeOf inner)
                    | _ -> ()
            | k when k = "scopes" ->
                for inner in childNodes n do
                    match inner with
                    | NodeC scopeNode when not (scopeNode.Key.StartsWith("scope[")) ->
                        symbols.Add(symbol CwtSymbolKind.CwtScope (scopeNode.Key.Trim('"')) scopeNode.Position filePath)
                        for sub in childNodes scopeNode do
                            match sub with
                            | NodeC aliasNode when aliasNode.Key = "aliases" ->
                                for lv in aliasNode.LeafValues do
                                    symbols.Add(symbol CwtSymbolKind.CwtScope (lv.Key.Trim('"')) lv.Position filePath)
                            | _ -> ()
                    | _ -> ()
            | k when k = "scope_groups" ->
                for inner in childNodes n do
                    match keyOf inner with
                    | Some gk when gk.StartsWith("scope_group[") ->
                        addDeclaration CwtSymbolKind.CwtScopeGroup gk (rangeOf inner)
                    | _ -> ()
            | k when k = "links" ->
                for inner in childNodes n do
                    match keyOf inner with
                    | Some lk -> symbols.Add(symbol CwtSymbolKind.CwtLink (lk.Trim('"')) (rangeOf inner) filePath)
                    | None -> ()
            | k when k = "modifier_categories" ->
                for inner in childNodes n do
                    match keyOf inner with
                    | Some mk -> symbols.Add(symbol CwtSymbolKind.CwtModifierCategory (mk.Trim('"')) (rangeOf inner) filePath)
                    | None -> ()
            | k when k.StartsWith("enum[") ->
                addDeclaration CwtSymbolKind.CwtEnum k n.Position
            | k when k.StartsWith("complex_enum[") ->
                addDeclaration CwtSymbolKind.CwtComplexEnum k n.Position
            | k when k.StartsWith("value_set[") ->
                addDeclaration CwtSymbolKind.CwtValueSet k n.Position
            | k when k.StartsWith("scope_group[") ->
                addDeclaration CwtSymbolKind.CwtScopeGroup k n.Position
            | _ -> ()

        // `enum[x] = scalar` style leaf declarations can appear at any depth
        // (they are definitions, unlike `key = enum[x]` value references).
        let rec collectLeafDeclarations (clause: IClause) =
            for c in childNodes clause do
                match c with
                | LeafC l ->
                    let key = l.Key
                    if key.StartsWith("enum[") then addDeclaration CwtSymbolKind.CwtEnum key l.Position
                    elif key.StartsWith("complex_enum[") then addDeclaration CwtSymbolKind.CwtComplexEnum key l.Position
                    elif key.StartsWith("value_set[") then addDeclaration CwtSymbolKind.CwtValueSet key l.Position
                    elif key.StartsWith("scope_group[") then addDeclaration CwtSymbolKind.CwtScopeGroup key l.Position
                | NodeC node -> collectLeafDeclarations node
                | _ -> ()

        collectLeafDeclarations root

        for child in childNodes root do
            match child with
            | NodeC n -> collectNode n
            | LeafC l when l.Key.StartsWith("alias[") ->
                addDeclaration CwtSymbolKind.CwtAlias l.Key l.Position
            | LeafC l when l.Key.StartsWith("single_alias[") ->
                addDeclaration CwtSymbolKind.CwtSingleAlias l.Key l.Position
            | _ -> ()

        symbols |> Seq.toList

    // ----------------------------------------------------------- references

    /// Built-in scope names that need no project definition.
    let private builtInScopeNames =
        set [ "any"; "all"; "no_scope"; "none"; "invalid_scope" ]

    let private referenceFromToken (filePath: string) (token: string) (r: range) : CwtReference list =
        let t = token.Trim()
        let bracketIdx = t.IndexOf('[')

        if bracketIdx > 0 && t.EndsWith("]") then
            let name = t.Substring(0, bracketIdx)
            let arg = t.Substring(bracketIdx + 1, t.Length - bracketIdx - 2)

            if arg = "" then
                []
            else
                let mk (kind: CwtSymbolKind) : CwtReference list =
                    [ { kind = kind; name = arg; range = r; filePath = filePath } ]

                match name with
                | "enum" -> mk CwtSymbolKind.CwtEnum
                | "complex_enum" -> mk CwtSymbolKind.CwtComplexEnum
                | "value_set" -> mk CwtSymbolKind.CwtValueSet
                | "scope" -> if builtInScopeNames.Contains arg then [] else mk CwtSymbolKind.CwtScope
                | "scope_group" -> mk CwtSymbolKind.CwtScopeGroup
                | "event_target" -> if builtInScopeNames.Contains arg then [] else mk CwtSymbolKind.CwtScope
                | _ -> []
        elif t.StartsWith("<") && t.EndsWith(">") && t.Length > 2 then
            let reference: CwtReference =
                { kind = CwtSymbolKind.CwtType
                  name = t.Substring(1, t.Length - 2)
                  range = r
                  filePath = filePath }
            [ reference ]
        else
            []

    /// All symbol references in a parsed document, excluding declaration
    /// sites. Quoted values are skipped (raw Value.ToString() preserves the
    /// quotes).
    let referencesInDocument (filePath: string) (root: Node) : CwtReference list =
        let references = ResizeArray<CwtReference>()
        let declarationRanges = ResizeArray<range>()

        // Collect declaration ranges (definitions are not references).
        let rec collectDeclarations (clause: IClause) =
            for c in childNodes clause do
                match c with
                | NodeC n ->
                    let key = n.Key
                    let isDeclaration =
                        key.StartsWith("type[")
                        || key.StartsWith("subtype[")
                        || key.StartsWith("enum[")
                        || key.StartsWith("complex_enum[")
                        || key.StartsWith("value[")
                        || key.StartsWith("alias[")
                        || key.StartsWith("single_alias[")
                        || key.StartsWith("scope_group[")
                    if isDeclaration then declarationRanges.Add n.Position
                    collectDeclarations n
                | _ -> ()

        collectDeclarations root

        let isDeclarationRange (r: range) =
            declarationRanges |> Seq.exists (fun d -> d.StartLine = r.StartLine && d.StartColumn = r.StartColumn)

        let rec walk (clause: IClause) =
            for c in childNodes clause do
                match c with
                | NodeC n -> walk n
                | LeafC l ->
                    if not (isDeclarationRange l.Position) then
                        references.AddRange(referenceFromToken filePath l.Key l.Position)
                        // ValueText strips quotes; detect quoted values on the raw string.
                        if not (l.Value.ToString().StartsWith("\"")) then
                            references.AddRange(referenceFromToken filePath l.ValueText l.Position)
                | ValueClauseC vc -> walk vc
                | _ -> ()

        walk root
        references |> Seq.toList

    /// Concrete arguments used by bracketed field expressions. Unlike
    /// references, these include open-ended dynamic namespaces such as
    /// `value[variable]` and alias groups; they are completion evidence only.
    let completionArgumentsInDocument (root: Node) : CwtCompletionArgument list =
        let supportedFamilies =
            set
                [ "enum"; "complex_enum"; "value"; "value_set"; "dynamic_value";
                  "alias_name"; "alias_match_left"; "alias_keys_field"; "alias_params_field";
                  "single_alias_right"; "scope"; "scope_group"; "event_target";
                  "name_format"; "stellaris_name_format"; "$tags"; "$tags_condition" ]
        let arguments = ResizeArray<CwtCompletionArgument>()

        let addToken (token: string) =
            let t = token.Trim()
            let bracketIdx = t.IndexOf('[')
            if bracketIdx > 0 && t.EndsWith("]", System.StringComparison.Ordinal) then
                let family = t.Substring(0, bracketIdx)
                let name = t.Substring(bracketIdx + 1, t.Length - bracketIdx - 2).Trim()
                if supportedFamilies.Contains family && name <> "" then
                    arguments.Add({ family = family; name = name })

        let rec walk (clause: IClause) =
            for child in childNodes clause do
                match child with
                | NodeC n ->
                    addToken n.Key
                    walk n
                | ValueClauseC vc -> walk vc
                | LeafC l ->
                    if not l.KeyId.quoted then addToken l.Key
                    if not l.ValueId.quoted then addToken l.ValueText
                | LeafValueC lv ->
                    if not lv.ValueId.quoted then addToken lv.ValueText
                | _ -> ()

        walk root
        arguments
        |> Seq.distinct
        |> Seq.sortBy (fun argument -> argument.family, argument.name)
        |> Seq.toList

    /// `## inject` targets referenced by a document:
    /// (sourcePath, memberPath, range) triples.
    let injectReferencesInDocument (filePath: string) (root: Node) : (string * string * range) list =
        let mutable injects = []

        let rec walk (clause: IClause) =
            for c in childNodes clause do
                match c with
                | NodeC n -> walk n
                | ValueClauseC vc -> walk vc
                | CommentC cm ->
                    match tryParseDirective cm.Comment with
                    | Some("inject", Some value) ->
                        match value.Split('@', 2, System.StringSplitOptions.RemoveEmptyEntries) with
                        | [| sourcePath; memberPath |] -> injects <- (sourcePath, memberPath, cm.Position) :: injects
                        | _ -> ()
                    | _ -> ()
                | _ -> ()

        walk root
        injects

    let private rootBlockNamesOf (root: Node) =
        childNodes root
        |> List.choose keyOf
        |> List.filter (fun k -> not (k.StartsWith("alias[") || k.StartsWith("single_alias[")))
        |> List.distinct

    // ---------------------------------------------------------------- public

    let analyzeDocument (filePath: string) (text: string) : CwtAnalysisResult =
        match parseFile filePath text with
        | ParseError(msg, p) ->
            { document = None
              diagnostics = [ syntaxDiagnostic filePath msg p ]
              canContributeToProjectIndex = false
              canActivateRules = false }
        | ParseOk root ->
            { document =
                Some
                    { filePath = filePath
                      symbols = collectSymbols filePath root
                      rootBlockNames = rootBlockNamesOf root
                      references = referencesInDocument filePath root
                      completionArguments = completionArgumentsInDocument root
                      injects = injectReferencesInDocument filePath root }
              diagnostics = analyzeRoot filePath root
              canContributeToProjectIndex = true
              canActivateRules = true }

    // ------------------------------------------------------------ completion

    /// Brace depth and comment state at `offset` in `text`.
    let private scanContext (text: string) (offset: int) =
        let mutable depth = 0
        let mutable inString = false
        let mutable lineStart = 0
        let mutable inLineComment = false
        let mutable i = 0
        while i < min offset text.Length do
            let ch = text.[i]
            if inString then
                if ch = '"' then inString <- false
            elif inLineComment then
                if ch = '\n' then
                    inLineComment <- false
            elif ch = '#' then
                inLineComment <- true
            elif ch = '"' then
                inString <- true
            elif ch = '{' then depth <- depth + 1
            elif ch = '}' then depth <- max 0 (depth - 1)
            elif ch = '\n' then lineStart <- i + 1
            i <- i + 1
        depth, inLineComment, lineStart

    let private completionItem label kind detail documentation insertText =
        { label = label
          kind = kind
          detail = detail
          documentation = documentation
          insertText = insertText }

    let private symbolKindForDeclaration (name: string) =
        match name with
        | "type" -> Some CwtSymbolKind.CwtType
        | "subtype" -> Some CwtSymbolKind.CwtSubtype
        | "enum" -> Some CwtSymbolKind.CwtEnum
        | "complex_enum" -> Some CwtSymbolKind.CwtComplexEnum
        | "value" -> Some CwtSymbolKind.CwtValueSet
        | "alias" -> Some CwtSymbolKind.CwtAlias
        | "single_alias" -> Some CwtSymbolKind.CwtSingleAlias
        | "scope" -> Some CwtSymbolKind.CwtScope
        | "scope_group" -> Some CwtSymbolKind.CwtScopeGroup
        | _ -> None

    let private placeholderCompletionItem (field: CwtFieldExpression) =
        if field.pattern = "<type>" then
            completionItem "<type…>" "FieldExpression" (Some field.description) (Some field.description) (Some "<${1:type}>")
        elif field.pattern.EndsWith("[x]", System.StringComparison.Ordinal) then
            let family = field.pattern.Substring(0, field.pattern.Length - 3)
            completionItem (family + "[…]") "FieldExpression" (Some field.description) (Some field.description) (Some(family + "[${1:name}]"))
        else
            completionItem field.pattern "FieldExpression" (Some field.description) (Some field.description) None

    let private expressionDescription family =
        CwtMetaSchema.fieldExpressions
        |> List.tryFind (fun field ->
            field.pattern = family || field.pattern.StartsWith(family + "[", System.StringComparison.Ordinal))
        |> Option.map (fun field -> field.description)

    let private aliasGroup (name: string) =
        let separator = name.IndexOf(':')
        if separator > 0 then name.Substring(0, separator) else name

    let private concreteExpressionItems
        (symbols: CwtSymbol list)
        (arguments: CwtCompletionArgument list)
        =
        let mk family name =
            let label =
                if family = "type" then $"<%s{name}>"
                else $"%s{family}[%s{name}]"
            let description = expressionDescription family
            completionItem label "FieldExpression" description description None

        let fromSymbols =
            symbols
            |> List.collect (fun symbol ->
                match symbol.kind with
                | CwtSymbolKind.CwtType -> [ mk "type" symbol.name ]
                | CwtSymbolKind.CwtEnum -> [ mk "enum" symbol.name ]
                | CwtSymbolKind.CwtComplexEnum -> [ mk "complex_enum" symbol.name ]
                | CwtSymbolKind.CwtValueSet ->
                    [ mk "value" symbol.name; mk "value_set" symbol.name; mk "dynamic_value" symbol.name ]
                | CwtSymbolKind.CwtAlias ->
                    let group = aliasGroup symbol.name
                    [ mk "alias_name" group; mk "alias_match_left" group
                      mk "alias_keys_field" group; mk "alias_params_field" group ]
                | CwtSymbolKind.CwtSingleAlias -> [ mk "single_alias_right" symbol.name ]
                | CwtSymbolKind.CwtScope -> [ mk "scope" symbol.name; mk "event_target" symbol.name ]
                | CwtSymbolKind.CwtScopeGroup -> [ mk "scope_group" symbol.name ]
                | _ -> [])

        let fromArguments = arguments |> List.map (fun argument -> mk argument.family argument.name)
        fromSymbols @ fromArguments
        |> List.distinctBy (fun item -> item.label)
        |> List.sortBy (fun item -> item.label)

    /// Completion with cross-file declarations and observed dynamic arguments.
    let completeAtWithProjectContext
        (filePath: string)
        (text: string)
        (position: pos)
        (projectSymbols: CwtSymbol list option)
        (projectArguments: CwtCompletionArgument list option)
        : CwtCompletionItem list =
        try
            let lineIdx = max 0 (position.Line - 1)
            let lineStart =
                let mutable start = 0
                let mutable line = 0
                let mutable i = 0
                while i < text.Length && line < lineIdx do
                    if text.[i] = '\n' then
                        line <- line + 1
                        start <- i + 1
                    i <- i + 1
                start
            let offset = min text.Length (lineStart + position.Column)
            let depth, inComment, _ = scanContext text offset
            let linePrefix = text.Substring(lineStart, max 0 (offset - lineStart))
            let trimmed = linePrefix.TrimStart()
            let typed =
                linePrefix
                |> Seq.rev
                |> Seq.takeWhile (fun c -> System.Char.IsAsciiLetterLower c || c = '_')
                |> Seq.rev
                |> System.String.Concat

            let prefixMatch (items: CwtCompletionItem list) =
                items
                |> List.filter (fun item -> item.label.StartsWith(typed, System.StringComparison.OrdinalIgnoreCase))
                |> List.sortBy (fun item -> item.label)

            let localSymbols, localArguments =
                match parseFile filePath text with
                | ParseOk root -> collectSymbols filePath root, completionArgumentsInDocument root
                | ParseError _ -> [], []
            let allSymbols = localSymbols @ (projectSymbols |> Option.defaultValue []) |> List.distinct
            let allArguments = localArguments @ (projectArguments |> Option.defaultValue []) |> List.distinct
            let concreteItems = concreteExpressionItems allSymbols allArguments

            if inComment then
                // `## name` context: offer directive names.
                let m = System.Text.RegularExpressions.Regex.Match(trimmed, @"^#+\s*([a-z_]*)$")
                if m.Success && trimmed.StartsWith("##") && not (trimmed.StartsWith("###")) then
                    let before = m.Groups.[1].Value
                    CwtMetaSchema.directives
                    |> List.map (fun d ->
                        completionItem d.name "Directive" (Some d.description) (Some d.description) None)
                    |> List.filter (fun item -> item.label.StartsWith before)
                    |> List.sortBy (fun item -> item.label)
                else []
            elif depth = 0 && not (trimmed.Contains("=")) && not (trimmed.Contains("[")) then
                // File root: known root blocks.
                CwtMetaSchema.rootBlocks
                |> List.map (fun rb ->
                    completionItem rb.name "RootBlock" (Some rb.description) (Some rb.description) None)
                |> prefixMatch
            else
                // Right side of an assignment: field-expression families.
                let eqIdx = linePrefix.LastIndexOf('=')
                if eqIdx >= 0 then
                    let afterEq = linePrefix.Substring(eqIdx + 1)
                    let typedField =
                        afterEq.TrimStart()
                        |> Seq.takeWhile (fun c -> System.Char.IsAsciiLetterLower c || c = '_' || c = '$' || c = '<' || c = '[')
                        |> System.String.Concat
                    CwtMetaSchema.fieldExpressions
                    |> List.map placeholderCompletionItem
                    |> List.append concreteItems
                    |> List.filter (fun item -> item.label.StartsWith(typedField, System.StringComparison.OrdinalIgnoreCase))
                    |> List.distinctBy (fun item -> item.label)
                    |> List.sortBy (fun item -> item.label)
                    |> List.truncate 2000
                else
                    // Inside a declaration bracket: local symbols of the kind.
                    let bracketMatch = System.Text.RegularExpressions.Regex.Match(linePrefix, @"\[([a-z_]*)$")
                    let declMatch = System.Text.RegularExpressions.Regex.Match(linePrefix, @"([a-z_]+)\[[a-z_]*$")
                    if bracketMatch.Success && declMatch.Success then
                        match symbolKindForDeclaration declMatch.Groups.[1].Value with
                        | Some kind when not (trimmed.Contains("=")) ->
                            let typedSymbol = bracketMatch.Groups.[1].Value
                            allSymbols
                            |> List.filter (fun s -> s.kind = kind)
                            |> List.distinctBy (fun s -> s.name)
                            |> List.map (fun s ->
                                completionItem s.name "Symbol" None None None)
                            |> List.filter (fun item -> item.label.StartsWith(typedSymbol, System.StringComparison.OrdinalIgnoreCase))
                            |> List.sortBy (fun item -> item.label)
                        | _ -> []
                    else []
        with _ -> []

    /// Compatibility entry point for callers that only have declarations.
    let completeAtWithProject
        (filePath: string)
        (text: string)
        (position: pos)
        (projectSymbols: CwtSymbol list option)
        : CwtCompletionItem list =
        completeAtWithProjectContext filePath text position projectSymbols None

    /// Completion at a document position. Works on raw text so it stays
    /// usable while the file does not parse (recovery contract); local-symbol
    /// completion additionally needs a parseable tree.
    let completeAt (filePath: string) (text: string) (position: pos) : CwtCompletionItem list =
        completeAtWithProjectContext filePath text position None None
