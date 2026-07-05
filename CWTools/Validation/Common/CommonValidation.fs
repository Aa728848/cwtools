namespace CWTools.Validation.Common

open System
open System.Text.RegularExpressions
open CWTools.Process
open CWTools.Utilities
open CWTools.Validation
open CWTools.Validation.ValidationCore
open CWTools.Process.ProcessCore
open CWTools.Utilities.Utils
open CWTools.Common
open CWTools.Utilities.Position
open CWTools.Games
open CWTools.Parser
open CWTools.Rules

module CommonValidation =
    let private scriptedParameterPattern =
        Regex(@"\$([^$|]+)(?:\|([^$]*))?\$", RegexOptions.Compiled)

    let private parameterName (text: string) =
        let pipeIndex = text.IndexOf('|')
        if pipeIndex >= 0 then text.Substring(0, pipeIndex) else text

    let private normalizeParameterKey (key: string) =
        key.Trim().Trim('$') |> parameterName

    let private bracketParameterName (text: string) =
        let text = text.TrimStart()

        if text.StartsWith("[[") then
            let inner = text.Substring(2).TrimStart()
            let negated = inner.StartsWith("!")
            let inner = if negated then inner.Substring(1).TrimStart() else inner
            let endIndex = inner.IndexOfAny([| ']'; ' '; '\t'; '\r'; '\n' |])
            let paramName =
                if endIndex >= 0 then inner.Substring(0, endIndex).Trim()
                else inner.Trim()

            if paramName.Length > 0 && (System.Char.IsLetterOrDigit(paramName.[0]) || paramName.[0] = '_') then
                Some(paramName, negated)
            else
                None
        else
            None

    let private applyBracketConditionals (parameters: (string * string) list) (children: Child array) =
        let values =
            parameters
            |> Seq.choose (fun (key, value) ->
                let name = normalizeParameterKey key
                if String.IsNullOrWhiteSpace name then None else Some(name, value))
            |> Map.ofSeq

        let parameterAllowsBlock name negated =
            let value =
                values
                |> Map.tryFind name
                |> Option.map (fun v -> v.Trim())

            let presentAndEnabled =
                match value with
                | Some v when not (String.Equals(v, "no", StringComparison.OrdinalIgnoreCase)) -> true
                | _ -> false

            if negated then not presentAndEnabled else presentAndEnabled

        let isBracketClose =
            function
            | LeafValueC lv -> lv.ValueText.Trim() = "]"
            | _ -> false

        let valueHasGluedClose =
            function
            | Value.String s ->
                let str = s.GetString()
                str.Length > 1 && str.[str.Length - 1] = ']' && str.IndexOf '[' < 0
            | _ -> false

        let stripGluedClose =
            function
            | Value.String s ->
                let str = s.GetString()
                String(StringResource.stringManager.InternIdentifierToken(str.Substring(0, str.Length - 1)))
            | v -> v

        let childHasGluedClose =
            function
            | LeafC l -> valueHasGluedClose l.Value
            | LeafValueC lv -> valueHasGluedClose lv.Value
            | _ -> false

        let stripChildGluedClose =
            function
            | LeafC l -> l.Value <- stripGluedClose l.Value
            | LeafValueC lv -> lv.Value <- stripGluedClose lv.Value
            | _ -> ()

        let rec processChildren (items: Child array) =
            let rec findClose depth index =
                if index >= items.Length then
                    None
                else
                    match items.[index] with
                    | LeafValueC lv when bracketParameterName lv.ValueText |> Option.isSome ->
                        findClose (depth + 1) (index + 1)
                    | NodeC node when (node.KeyPrefix |> Option.bind bracketParameterName |> Option.isSome)
                                       || (bracketParameterName node.Key |> Option.isSome) ->
                        findClose (depth + 1) (index + 1)
                    | child when isBracketClose child ->
                        if depth = 1 then Some index else findClose (depth - 1) (index + 1)
                    | _ ->
                        findClose depth (index + 1)

            let rec findGluedClose index =
                if index >= items.Length then
                    None
                else
                    match items.[index] with
                    | LeafValueC lv when bracketParameterName lv.ValueText |> Option.isSome -> None
                    | NodeC node when (node.KeyPrefix |> Option.bind bracketParameterName |> Option.isSome)
                                       || (bracketParameterName node.Key |> Option.isSome) -> None
                    | child when childHasGluedClose child -> Some index
                    | _ -> findGluedClose (index + 1)

            let rec loop index acc =
                if index >= items.Length then
                    acc |> List.rev |> Array.ofList
                else
                    match items.[index] with
                    | LeafValueC lv ->
                        match bracketParameterName lv.ValueText with
                        | Some(name, negated) ->
                            match findClose 1 (index + 1) with
                            | Some closeIndex ->
                                let block =
                                    items.[index + 1 .. closeIndex - 1]
                                    |> processChildren
                                    |> Array.toList

                                if parameterAllowsBlock name negated then
                                    loop (closeIndex + 1) ((block |> List.rev) @ acc)
                                else
                                    loop (closeIndex + 1) acc
                            | None ->
                                match findGluedClose (index + 1) with
                                | Some gluedIndex ->
                                    stripChildGluedClose items.[gluedIndex]

                                    let block =
                                        items.[index + 1 .. gluedIndex]
                                        |> processChildren
                                        |> Array.toList

                                    if parameterAllowsBlock name negated then
                                        loop (gluedIndex + 1) ((block |> List.rev) @ acc)
                                    else
                                        loop (gluedIndex + 1) acc
                                | None ->
                                    loop (index + 1) (items.[index] :: acc)
                        | None ->
                            loop (index + 1) (items.[index] :: acc)
                    | NodeC node ->
                        match node.KeyPrefix |> Option.bind bracketParameterName with
                        | Some(name, negated) ->
                            if parameterAllowsBlock name negated then
                                node.KeyPrefix <- None
                                loop (index + 1) (NodeC node :: acc)
                            else
                                loop (index + 1) acc
                        | None ->
                            // Also check if the key itself starts with [[ (glued key case)
                            // e.g., [[ag_location]variable = { ... }]
                            match bracketParameterName node.Key with
                            | Some(name, negated) ->
                                // The real key follows after [[PARAM] — strip the conditional prefix
                                let prefixEnd = node.Key.IndexOf(']')
                                let realKey =
                                    if prefixEnd >= 0 && prefixEnd + 1 < node.Key.Length then
                                        node.Key.Substring(prefixEnd + 1)
                                    else
                                        node.Key
                                // Look for the closing ] in subsequent siblings
                                match findClose 1 (index + 1) with
                                | Some closeIndex ->
                                    if parameterAllowsBlock name negated then
                                        node.Key <- realKey
                                        let block =
                                            items.[index + 1 .. closeIndex - 1]
                                            |> processChildren
                                            |> Array.toList
                                        loop (closeIndex + 1) ((block |> List.rev) @ (NodeC node :: acc))
                                    else
                                        loop (closeIndex + 1) acc
                                | None ->
                                    match findGluedClose (index + 1) with
                                    | Some gluedIndex ->
                                        stripChildGluedClose items.[gluedIndex]
                                        if parameterAllowsBlock name negated then
                                            node.Key <- realKey
                                            let block =
                                                items.[index + 1 .. gluedIndex]
                                                |> processChildren
                                                |> Array.toList
                                            loop (gluedIndex + 1) ((block |> List.rev) @ (NodeC node :: acc))
                                        else
                                            loop (gluedIndex + 1) acc
                                    | None ->
                                        // No matching close found — check if this node itself
                                        // has the closing ] glued to its last value
                                        if parameterAllowsBlock name negated then
                                            node.Key <- realKey
                                            loop (index + 1) (NodeC node :: acc)
                                        else
                                            loop (index + 1) acc
                            | None ->
                                loop (index + 1) (items.[index] :: acc)
                    | _ ->
                        loop (index + 1) (items.[index] :: acc)

            loop 0 []

        processChildren children

    /// Resolve inline [[PARAM]content] conditional blocks within a string.
    /// Handles cases where [[PARAM]content] is embedded within a larger
    /// identifier token (e.g., "prefix[[PARAM]_suffix]"), which the AST-level
    /// applyBracketConditionals cannot reach because the parser treats the
    /// entire string as a single token.
    let rec private resolveInlineBracketConditionals (values: Map<string, string>) (text: string) =
        if text.IndexOf("[[") < 0 then
            text
        else
            let sb = System.Text.StringBuilder(text.Length)
            let mutable i = 0

            while i < text.Length do
                if i + 1 < text.Length && text.[i] = '[' && text.[i + 1] = '[' then
                    // Attempt to parse [[PARAM] or [[!PARAM]
                    let mutable j = i + 2
                    while j < text.Length && (text.[j] = ' ' || text.[j] = '\t') do
                        j <- j + 1
                    let negated = j < text.Length && text.[j] = '!'
                    if negated then j <- j + 1
                    while j < text.Length && (text.[j] = ' ' || text.[j] = '\t') do
                        j <- j + 1
                    let nameStart = j
                    while j < text.Length
                          && text.[j] <> ']'
                          && text.[j] <> ' '
                          && text.[j] <> '\t'
                          && text.[j] <> '\r'
                          && text.[j] <> '\n' do
                        j <- j + 1
                    let paramName = text.Substring(nameStart, j - nameStart)
                    while j < text.Length && (text.[j] = ' ' || text.[j] = '\t') do
                        j <- j + 1

                    if paramName.Length > 0
                       && (Char.IsLetterOrDigit(paramName.[0]) || paramName.[0] = '_')
                       && j < text.Length
                       && text.[j] = ']' then
                        // Valid [[PARAM] found — scan for matching closing ]
                        let contentStart = j + 1
                        let mutable depth = 1
                        let mutable k = contentStart

                        while k < text.Length && depth > 0 do
                            if k + 1 < text.Length && text.[k] = '[' && text.[k + 1] = '[' then
                                // Nested [[PARAM] — increase depth and skip past
                                // the inner param name + its closing ]
                                depth <- depth + 1
                                k <- k + 2
                                while k < text.Length && text.[k] <> ']' do
                                    k <- k + 1
                                if k < text.Length then
                                    k <- k + 1
                            elif text.[k] = ']' then
                                depth <- depth - 1
                                if depth > 0 then
                                    k <- k + 1
                            else
                                k <- k + 1

                        if depth = 0 then
                            let content = text.Substring(contentStart, k - contentStart)
                            let presentAndEnabled =
                                match values |> Map.tryFind paramName with
                                | Some v when not (String.Equals(v.Trim(), "no", StringComparison.OrdinalIgnoreCase)) -> true
                                | _ -> false
                            let includeContent = if negated then not presentAndEnabled else presentAndEnabled
                            if includeContent then
                                sb.Append(resolveInlineBracketConditionals values content) |> ignore
                            i <- k + 1
                        else
                            // Unmatched brackets — treat as literal text
                            sb.Append(text.[i]) |> ignore
                            i <- i + 1
                    else
                        // Not a valid [[PARAM] pattern — treat as literal
                        sb.Append(text.[i]) |> ignore
                        i <- i + 1
                else
                    sb.Append(text.[i]) |> ignore
                    i <- i + 1

            sb.ToString()

    let private replaceScriptedParameters (parameters: (string * string) seq) (text: string) =
        let values =
            parameters
            |> Seq.choose (fun (key, value) ->
                let name = normalizeParameterKey key
                if String.IsNullOrWhiteSpace name then None else Some(name, value))
            |> Map.ofSeq

        // First resolve inline [[PARAM]content] conditional blocks
        // (consistent with AST-level order: brackets first, then $PARAM$)
        let afterBrackets = resolveInlineBracketConditionals values text

        // Then replace $PARAM$ references
        scriptedParameterPattern.Replace(
            afterBrackets,
            MatchEvaluator(fun m ->
                let name = m.Groups.[1].Value
                match values |> Map.tryFind name with
                | Some value -> value
                | None when m.Groups.[2].Success -> m.Groups.[2].Value
                | None -> m.Value)
        )

    let private splitScriptValueParameterParts (text: string) =
        let parts = ResizeArray<string>()
        let current = System.Text.StringBuilder()
        let mutable insideScriptedParameter = false

        for c in text do
            match c with
            | '$' ->
                insideScriptedParameter <- not insideScriptedParameter
                current.Append(c) |> ignore
            | '|' when not insideScriptedParameter ->
                parts.Add(current.ToString())
                current.Clear() |> ignore
            | _ ->
                current.Append(c) |> ignore

        parts.Add(current.ToString())
        parts |> List.ofSeq

    let private scriptValueCallError (referenceDetails: ReferenceDetails) (message: string) =
        invManual
            (ErrorCodes.CustomError message Severity.Error)
            referenceDetails.position
            (referenceDetails.originalValue.GetString())
            None

    let private parseScriptValueCallParams (referenceDetails: ReferenceDetails) =
        let splitStringList =
            referenceDetails.originalValue.GetString()
            |> splitScriptValueParameterParts

        let parameterParts =
            if splitStringList.Length > 1 then
                let parts = List.tail splitStringList

                match List.rev parts with
                | last :: rest when String.IsNullOrWhiteSpace last -> List.rev rest
                | _ -> parts
            else
                []

        let rec loop parts replacementParams parameterNames errors =
            match parts with
            | key :: value :: rest ->
                let paramName = normalizeParameterKey key

                let replacementParams =
                    if String.IsNullOrWhiteSpace paramName || String.IsNullOrWhiteSpace value then
                        replacementParams
                    else
                        ($"${paramName}$", value) :: replacementParams

                let parameterNames =
                    if String.IsNullOrWhiteSpace paramName || String.IsNullOrWhiteSpace value then
                        parameterNames
                    else
                        paramName :: parameterNames

                let errors =
                    if String.IsNullOrWhiteSpace paramName then
                        scriptValueCallError referenceDetails "Script value call contains an empty parameter name"
                        :: errors
                    elif String.IsNullOrWhiteSpace value then
                        scriptValueCallError
                            referenceDetails
                            (sprintf "Script value parameter %s is missing a value" paramName)
                        :: errors
                    else
                        errors

                loop rest replacementParams parameterNames errors
            | [ key ] ->
                let paramName = normalizeParameterKey key
                let displayName =
                    if String.IsNullOrWhiteSpace paramName then
                        "<empty>"
                    else
                        paramName

                let error =
                    scriptValueCallError
                        referenceDetails
                        (sprintf "Script value parameter %s is missing a value" displayName)

                List.rev replacementParams, List.rev parameterNames, List.rev (error :: errors)
            | [] -> List.rev replacementParams, List.rev parameterNames, List.rev errors

        let replacementParams, parameterNames, errors = loop parameterParts [] [] []
        let replacementParams = if List.isEmpty replacementParams then None else Some replacementParams
        replacementParams, parameterNames, errors

    let validateMixedBlocks: StructureValidator<_> =
        fun _ es ->
            let fNode =
                (fun (x: Node) children ->
                    if
                        (x.LeafValues |> Seq.isEmpty |> not
                         && (x.Leaves |> Seq.isEmpty |> not || x.Nodes |> Seq.isEmpty |> not))
                        |> not
                    then
                        children
                    else
                        Invalid(System.Guid.NewGuid(), [ inv ErrorCodes.MixedBlock x ]) <&&> children)

            let fCombine = (<&&>)
            es.All <&!&> foldNode2 fNode fCombine OK

    let validateEU4NaiveNot: StructureValidator<_> =
        fun _ es ->
            let fNode =
                (fun (x: Node) children ->
                    if x.Key == "NOT" && (x.AllArray.Length - (x.Comments |> Seq.length)) > 1 then
                        Invalid(
                            System.Guid.NewGuid(),
                            [ inv (ErrorCodes.CustomError "Reminder: NOT does not mean NOT AND" Severity.Information) x ]
                        )
                    else
                        children)

            let fCombine = (<&&>)
            es.All <&!&> foldNode2 fNode fCombine OK

    let validateNOTMultiple: StructureValidator<_> =
        fun _ es ->
            let fNode =
                (fun (x: Node) children ->
                    if x.Key == "NOT" && (x.AllArray.Length - (x.Comments |> Seq.length)) > 1 then
                        inv ErrorCodes.IncorrectNotUsage x <&&&> children
                    else
                        children)

            let fCombine = (<&&>)

            (es.AllEffects <&!&> foldNode2 fNode fCombine OK)
            <&&> (es.AllTriggers <&!&> foldNode2 fNode fCombine OK)

    let validateIfWithNoEffect: StructureValidator<_> =
        fun _ es ->
            let keyID =
                CWTools.Utilities.StringResource.stringManager.InternIdentifierToken "limit"

            let keyIdIF =
                CWTools.Utilities.StringResource.stringManager.InternIdentifierToken "if"

            let keyIdelIF =
                CWTools.Utilities.StringResource.stringManager.InternIdentifierToken "else_if"

            let fNode =
                (fun (x: Node) children ->
                    if
                        (x.KeyId = keyIdIF || x.KeyId = keyIdelIF)
                        && (x.Leaves |> Seq.isEmpty)
                        && (x.Nodes |> Seq.exists (fun c -> c.KeyId <> keyID) |> not)
                    then
                        inv ErrorCodes.EmptyIf x <&&&> children
                    else
                        children)

            let fCombine = (<&&>)

            (es.AllEffects <&!&> foldNode2 fNode fCombine OK)
            <&&> (es.AllTriggers <&!&> foldNode2 fNode fCombine OK)


    let valUniqueTypes: LookupValidator<_> =
        (fun lu _ _ ->
            let types = lu.typeDefs |> List.filter (fun td -> td.unique)
            let zipped = types |> List.map (fun td -> td.name, lu.typeDefInfo.[td.name])

            let groupFun =
                Array.groupBy (fun (tdi: TypeDefInfo) -> tdi.id)
                >> Array.filter (fun (k, g) -> g.Length > 1)
                >> Array.collect snd

            let res =
                zipped
                |> Seq.collect (fun (tn, ts) -> (groupFun ts) |> Array.map (fun t -> tn, t))

            res
            <&!&> (fun (typename, tdi) ->
                Invalid(
                    System.Guid.NewGuid(),
                    [ invManual (ErrorCodes.DuplicateTypeDef typename tdi.id) tdi.range "" None ]
                ))
        //    |> List.map (fun td, ts -> )
        )

    // Common function to validate @variables after parameter substitution
    // Used by both valScriptedEffectParams and valScriptValueParams
    let validateVariablesInExpandedNode
        (currentFilePath: string)
        (n: Node)
        callSite
        (globalVars: (string * string) list)
        =
        try
            let globalVarNames = globalVars |> List.map fst |> Set.ofList

            let globalVarValues =
                globalVars
                |> Seq.distinctBy fst
                |> Map.ofSeq

            let rec collectVars (node: Node) acc =
                let acc =
                    if node.Key.StartsWith("@") && not (node.Key.StartsWith("@[")) && not (node.Key.StartsWith(@"@\[")) && not (node.Key.Contains("$")) then
                        (node.Key, node.Position) :: acc
                    else
                        acc
                let acc =
                    node.Leaves
                    |> Seq.fold (fun a leaf ->
                        let valText = leaf.Value.ToString()
                        if valText.StartsWith("@") && not (valText.StartsWith("@[")) && not (valText.StartsWith(@"@\[")) && not (valText.Contains("$")) then
                            (valText, leaf.Position) :: a
                        else
                            a) acc
                node.All
                |> Seq.choose (function
                    | NodeC child -> Some child
                    | _ -> None)
                |> Seq.fold (fun a child -> collectVars child a) acc
            let allVarsWithPos = collectVars n []
            allVarsWithPos
            |> List.choose (fun (v, pos) ->
                // Skip @[ array access syntax - this is not a scripted variable
                if v.StartsWith("@[") || v.StartsWith(@"@\[") then
                    None
                elif ScriptedVariableResolution.isKnownVariable globalVarNames globalVarValues v then
                    None
                else
                    Some(invManual (ErrorCodes.UndefinedVariable v) pos v None))
            |> (function
                | [] -> OK
                | errors -> Invalid(System.Guid.NewGuid(), errors))
        with ex ->
            // If validation fails, return OK to not break the entire validation pipeline
            OK

    let private isInsideLogicalOrBranch (root: Node) (target: range) =
        let rec loop insideOr (node: Node) =
            if not (rangeContainsRange node.Position target) then
                false
            else
                let insideOr = insideOr || node.Key == "OR"

                node.Nodes
                |> Seq.tryPick (fun child ->
                    if rangeContainsRange child.Position target then
                        Some(loop insideOr child)
                    else
                        None)
                |> Option.defaultValue insideOr

        loop false root

    let valScriptedEffectParams<'T when 'T :> ComputedData> : CWTools.Games.LookupFileValidator<'T> =
        (fun fileManager rulesValidator lu res es ->
            let res = res.AllEntities()

            let entityMap =
                res |> Seq.map (fun struct (e, d) -> e.filepath, struct (e, d)) |> Map.ofSeq

            let scriptedVariableValues = lu.scriptedVariables |> Map.ofList

            let findParams (pos: range) =
                match entityMap |> Map.tryFind pos.FileName with
                | Some struct (e, _) ->
                    let rec findChild (node: Node) =
                        if node.Position.Equals(pos) then
                            Some node
                        else
                            match node.Nodes |> Seq.tryFind (fun n -> rangeContainsRange n.Position pos) with
                            | Some c -> findChild c
                            | None -> None

                    findChild e.entity
                | None -> None
                //|> Option.map (fun s -> eprintfn "vsep %A %A" s.Key key; s)
                |> Option.map (fun s ->
                    s.Values
                    |> List.map (fun l ->
                        let rawValue = l.ValueText
                        let resolvedValue =
                            if rawValue.StartsWith("@", StringComparison.Ordinal)
                               && not (rawValue.StartsWith("@[", StringComparison.Ordinal))
                               && not (rawValue.StartsWith(@"@\[", StringComparison.Ordinal)) then
                                match scriptedVariableValues |> Map.tryFind rawValue with
                                | Some numericValue -> numericValue
                                | None -> rawValue
                            else rawValue
                        "$" + l.Key + "$", resolvedValue))

            let findSE (pos: range) =
                match entityMap |> Map.tryFind pos.FileName with
                | Some struct (e, _) ->
                    let rec findChild (node: Node) =
                        if node.Position.Equals pos then
                            Some node
                        else
                            match node.Nodes |> Seq.tryFind (fun n -> rangeContainsRange n.Position pos) with
                            | Some c -> findChild c
                            | None -> None

                    findChild e.entity
                | None -> None

            match rulesValidator with
            | Some rv ->
                let scriptedDefinitions =
                    [| "scripted_effect"; "scripted_trigger" |]
                    |> Array.collect (fun typeName ->
                        lu.typeDefInfo
                        |> Map.tryFind typeName
                        |> Option.defaultValue [||]
                        |> Array.map (fun se -> typeName, se))

                let allScriptedEffects =
                    scriptedDefinitions
                    |> Array.map (fun (scriptedType, se) -> scriptedType, se.id, se.range.FileName, findSE se.range)

                let getRefsFromRefTypes (referencedtypes: Map<string, ReferenceDetails list>) =
                    //eprintfn "grfrt %A" referencedtypes
                    [ "scripted_effect"; "scripted_trigger" ]
                    |> List.collect (fun scriptedType ->
                        referencedtypes
                        |> Map.tryFind scriptedType
                        |> Option.defaultValue []
                        |> List.map (fun ref -> scriptedType, ref))

                let allRefs =
                    es.AllWithData
                    |> List.collect (fun (n, d) ->
                        d.Force().Referencedtypes
                        |> Option.map getRefsFromRefTypes
                        |> Option.defaultValue [])
                    |> List.filter (fun (_, ref) -> ref.referenceType = ReferenceType.TypeDef)
                    |> List.map (fun (scriptedType, ref) ->
                        {| scriptedType = scriptedType
                           effectName = ref.name.GetString()
                           callSite = ref.position
                           seParams = findParams ref.position |})
                    |> List.groupBy (fun ref -> ref.scriptedType, ref.effectName)
                    |> Map.ofList
                // eprintfn "ar %A" allRefs
                let scriptedEffects =
                    allScriptedEffects
                    |> Array.map (fun (scriptedType, name, filename, node) ->
                        scriptedType,
                        name,
                        fileManager.ConvertPathToLogicalPath(filename),
                        node,
                        allRefs |> Map.tryFind (scriptedType, name) |> Option.defaultValue [])

                let stringReplace (seParams: (string * string) list) (key: string) =
                    replaceScriptedParameters seParams key

                let rec foldOverNode parameters stringReplacer (node: Node) =
                    // eprintfn "fov %A" node.Key
                    node.AllArray <- applyBracketConditionals parameters node.AllArray
                    node.Key <- stringReplacer node.Key

                    node.Leaves
                    |> Seq.iter (fun (l: Leaf) ->
                        l.Key <- stringReplacer l.Key

                        l.Value
                        |> (function
                        | Value.String s ->
                            l.Value <-
                                String(
                                    stringReplacer (s.GetString())
                                    |> StringResource.stringManager.InternIdentifierToken
                                )
                        | Value.QString s ->
                            l.Value <-
                                QString(
                                    stringReplacer (s.GetString())
                                    |> StringResource.stringManager.InternIdentifierToken
                                )
                        | _ -> ()))

                    node.LeafValues
                    |> Seq.iter (fun (l: LeafValue) ->
                        l.Value
                        |> (function
                        | Value.String s ->
                            l.Value <-
                                String(
                                    stringReplacer (s.GetString())
                                    |> StringResource.stringManager.InternIdentifierToken
                                )
                        | Value.QString s ->
                            l.Value <-
                                QString(
                                    stringReplacer (s.GetString())
                                    |> StringResource.stringManager.InternIdentifierToken
                                )
                        | _ -> ()))

                    node.Nodes |> Seq.iter (foldOverNode parameters stringReplacer)

                let validateSESpecific
                    (
                        scriptedType: string,
                        name: string,
                        logicalpath: string,
                        node: Node,
                        callSite: range,
                        seParams: (string * string) list option
                    ) =
                    let newNode = CWTools.Process.STLProcess.cloneNode node
                    let rootNode = Node("root")
                    rootNode.AllArray <- [| NodeC newNode |]

                    let seParams = seParams |> Option.defaultValue []
                    foldOverNode seParams (stringReplace seParams) newNode
                    // eprintfn "%A %A" (CKPrinter.api.prettyPrintStatements newNode.ToRaw) (seParams)
                    // Validate variables after parameter substitution
                    let varValidation = validateVariablesInExpandedNode logicalpath newNode callSite lu.scriptedVariables
                    let ruleRes = rv.ManualRuleValidate(logicalpath, rootNode)
                    // eprintfn "%A %A" logicalpath res
                    let scriptedKind =
                        match scriptedType with
                        | "scripted_trigger" -> "scripted trigger"
                        | _ -> "scripted effect"

                    let relocate (errs: CWError list) =
                        errs
                        |> List.map (fun e ->
                            { e with
                                range = callSite
                                keyLength = name.Length
                                message =
                                    sprintf "This call of %s %s results in an error: %s" scriptedKind name e.message
                                relatedErrors =
                                    Some
                                        [ { location = e.range
                                            message = sprintf "Related source: definition of %s %s" scriptedKind name } ] })

                    let definitionHint =
                        { code = "CW274D"
                          severity = Severity.Information
                          range = node.Position
                          keyLength = name.Length
                          message =
                            sprintf "This %s %s results in an error when expanded at a call site" scriptedKind name
                          data = None
                          relatedErrors = Some [ { location = callSite; message = sprintf "Call site of %s" name } ] }

                    let capTriggerOrBranchErrorsAtWarning (errs: CWError list) =
                        if scriptedType <> "scripted_trigger" then
                            errs
                        else
                            errs
                            |> List.map (fun e ->
                                if isInsideLogicalOrBranch newNode e.range then
                                    { e with severity = max e.severity Severity.Warning }
                                else
                                    e)

                    let combined =
                        match varValidation, ruleRes with
                        | OK, OK -> OK
                        | OK, Invalid(_, innerErrs) ->
                            Invalid(System.Guid.NewGuid(), definitionHint :: relocate (capTriggerOrBranchErrorsAtWarning innerErrs))
                        | Invalid(_, varInv), OK ->
                            Invalid(System.Guid.NewGuid(), definitionHint :: relocate (capTriggerOrBranchErrorsAtWarning varInv))
                        | Invalid(_, varInv), Invalid(_, resInv) ->
                            Invalid(System.Guid.NewGuid(), definitionHint :: relocate (capTriggerOrBranchErrorsAtWarning (varInv @ resInv)))

                    combined

                let memoizeValidation =
                    let keyFun =
                        (fun (scriptedType, _, _, node: Node, callSite, seParams) ->
                            (scriptedType, node.Position, callSite, seParams))
                    let memFun = validateSESpecific
                    memoize keyFun memFun

                let validateSE
                    (scriptedType: string)
                    (name: string)
                    (logicalpath: string)
                    (node: Node option)
                    (refs:
                        {| scriptedType: string
                           callSite: range
                           effectName: string
                           seParams: (string * string) list option |} list)
                    =
                    // eprintfn "vse %A %A %A" name node refs
                    let res =
                        match node with
                        | Some node ->
                            refs
                            <&!&> (fun ref -> memoizeValidation (scriptedType, name, logicalpath, node, ref.callSite, ref.seParams))
                        | None -> OK

                    res

                scriptedEffects
                <&!&> (fun (scriptedType, name, lp, node, refs) -> validateSE scriptedType name lp node refs)
            | _ -> OK)

    let valScriptValueParams<'T when 'T :> ComputedData> : CWTools.Games.LookupFileValidator<'T> =
        (fun fileManager rulesValidator lu res es ->
            let res = res.AllEntities()

            let entityMap =
                res |> Seq.map (fun struct (e, d) -> e.filepath, struct (e, d)) |> Map.ofSeq

            let findParams (referenceDetails: ReferenceDetails) =
                parseScriptValueCallParams referenceDetails

            let findScriptValue (pos: range) =
                match entityMap |> Map.tryFind pos.FileName with
                | Some struct (e, _) ->
                    let rec findChild (node: Node) =
                        if node.Position.Equals pos then
                            Some node
                        else
                            match node.Nodes |> Seq.tryFind (fun n -> rangeContainsRange n.Position pos) with
                            | Some c -> findChild c
                            | None -> None

                    findChild e.entity
                | None -> None

            match rulesValidator, lu.typeDefInfo |> Map.tryFind "script_value" with
            | Some rv, Some scriptValues ->
                //                logInfo (sprintf "vsvpa %A" scriptValues)
                let allScriptValues =
                    scriptValues
                    |> Array.map (fun se -> se.id, se.range.FileName, findScriptValue se.range)

                let getRefsFromRefTypes (referencedtypes: Map<string, ReferenceDetails list>) =
                    //eprintfn "grfrt %A" referencedtypes
                    referencedtypes
                    |> (fun refMap -> Map.tryFind "script_value" refMap)
                    |> Option.defaultValue []

                let allRefs =
                    es.AllWithData
                    |> List.collect (fun (n, d) ->
                        d.Force().Referencedtypes
                        |> Option.map getRefsFromRefTypes
                        |> Option.defaultValue [])
                    |> List.filter (fun ref -> ref.referenceType = ReferenceType.TypeDef)
                    |> List.map (fun ref ->
                        let seParams, parameterNames, parameterErrors = findParams ref

                        {| effectName = ref.name.GetString()
                           callSite = ref.position
                           seParams = seParams
                           parameterNames = parameterNames
                           parameterErrors = parameterErrors |})
                    |> List.groupBy (fun ref -> ref.effectName)
                    |> Map.ofList
                // eprintfn "ar %A" allRefs
                let scriptedEffects =
                    allScriptValues
                    |> Array.map (fun (name, filename, node) ->
                        name,
                        fileManager.ConvertPathToLogicalPath(filename),
                        node,
                        allRefs |> Map.tryFind name |> Option.defaultValue [])

                let stringReplace (seParams: (string * string) list) (key: string) =
                    replaceScriptedParameters seParams key

                let rec foldOverNode parameters stringReplacer (node: Node) =
                    // eprintfn "fov %A" node.Key
                    node.AllArray <- applyBracketConditionals parameters node.AllArray
                    node.Key <- stringReplacer node.Key

                    node.Leaves
                    |> Seq.iter (fun (l: Leaf) ->
                        l.Key <- stringReplacer l.Key

                        l.Value
                        |> (function
                        | Value.String s ->
                            l.Value <-
                                String(
                                    stringReplacer (s.GetString())
                                    |> StringResource.stringManager.InternIdentifierToken
                                )
                        | Value.QString s ->
                            l.Value <-
                                QString(
                                    stringReplacer (s.GetString())
                                    |> StringResource.stringManager.InternIdentifierToken
                                )
                        | _ -> ()))

                    node.LeafValues
                    |> Seq.iter (fun (l: LeafValue) ->
                        l.Value
                        |> (function
                        | Value.String s ->
                            l.Value <-
                                String(
                                    stringReplacer (s.GetString())
                                    |> StringResource.stringManager.InternIdentifierToken
                                )
                        | Value.QString s ->
                            l.Value <-
                                QString(
                                    stringReplacer (s.GetString())
                                    |> StringResource.stringManager.InternIdentifierToken
                                )
                        | _ -> ()))

                    node.Nodes |> Seq.iter (foldOverNode parameters stringReplacer)

                let validateSESpecific
                    (
                        name: string,
                        logicalpath: string,
                        node: Node,
                        callSite: range,
                        seParams: (string * string) list option
                    ) =
                    let newNode = CWTools.Process.STLProcess.cloneNode node
                    let rootNode = Node("root")
                    rootNode.AllArray <- [| NodeC newNode |]

                    let seParams = seParams |> Option.defaultValue []
                    foldOverNode seParams (stringReplace seParams) newNode

                    // Validate variables after parameter substitution
                    let varValidation = validateVariablesInExpandedNode logicalpath newNode callSite lu.scriptedVariables
                    //                    logInfo (sprintf "vsvp d %A %A" (CKPrinter.api.prettyPrintStatement newNode.ToRaw) (seParams))
                    let ruleRes = rv.ManualRuleValidate(logicalpath, rootNode)
                    // eprintfn "%A %A" logicalpath res
                    let relocate (errs: CWError list) =
                        errs
                        |> List.map (fun e ->
                            { e with
                                range = callSite
                                keyLength = name.Length
                                message =
                                    sprintf "This call of scripted value %s results in an error: %s" name e.message
                                relatedErrors =
                                    Some
                                        [ { location = e.range
                                            message = sprintf "Related source: definition of scripted value %s" name } ] })

                    let definitionHint =
                        { code = "CW274D"
                          severity = Severity.Information
                          range = node.Position
                          keyLength = name.Length
                          message =
                            sprintf "This scripted value %s results in an error when expanded at a call site" name
                          data = None
                          relatedErrors = Some [ { location = callSite; message = sprintf "Call site of %s" name } ] }

                    let combined =
                        match varValidation, ruleRes with
                        | OK, OK -> OK
                        | OK, Invalid(_, innerErrs) ->
                            Invalid(System.Guid.NewGuid(), definitionHint :: relocate innerErrs)
                        | Invalid(_, varInv), OK ->
                            Invalid(System.Guid.NewGuid(), definitionHint :: relocate varInv)
                        | Invalid(_, varInv), Invalid(_, resInv) ->
                            Invalid(System.Guid.NewGuid(), definitionHint :: relocate (varInv @ resInv))

                    combined
                //                            | Invalid (_, inv) -> Invalid (System.Guid.NewGuid(), inv |> List.map (fun e -> { e with relatedErrors = Some message })))
                let memoizeValidation =
                    let keyFun = (fun (_, _, node: Node, callSite, seParams) -> (node.Position, callSite, seParams))
                    let memFun = validateSESpecific
                    memoize keyFun memFun

                let validateCallParams name (node: Node) callSite parameterNames parameterErrors =
                    let expectedParams =
                        Compute.Jomini.getScriptValueParams node
                        |> List.map normalizeParameterKey
                        |> Set.ofList

                    let unknownParameterErrors =
                        parameterNames
                        |> List.distinct
                        |> List.filter (fun paramName -> not (expectedParams |> Set.contains paramName))
                        |> List.map (fun paramName ->
                            { invManual
                                  (ErrorCodes.CustomError
                                      (sprintf "Unknown parameter %s for scripted value %s" paramName name)
                                      Severity.Error)
                                  callSite
                                  paramName
                                  None with
                                relatedErrors =
                                    Some
                                        [ { location = node.Position
                                            message = sprintf "Related source: definition of scripted value %s" name } ] })

                    match parameterErrors @ unknownParameterErrors with
                    | [] -> OK
                    | errors -> Invalid(System.Guid.NewGuid(), errors)

                let validateSE
                    (name: string)
                    (logicalpath: string)
                    (node: Node option)
                    (refs:
                        {| callSite: range
                           effectName: string
                           seParams: (string * string) list option
                           parameterNames: string list
                           parameterErrors: CWError list |} list)
                    =
                    // eprintfn "vse %A %A %A" name node refs
                    let res =
                        match node with
                        | Some node ->
                            refs
                            <&!&> (fun ref ->
                                validateCallParams name node ref.callSite ref.parameterNames ref.parameterErrors
                                <&&> memoizeValidation (name, logicalpath, node, ref.callSite, ref.seParams))
                        | None -> OK

                    res

                scriptedEffects
                <&!&> (fun (name, lp, node, refs) -> validateSE name lp node refs)
            | _ -> OK)

    type BoolState =
        | AND = 1uy
        | OR = 2uy

    let validateRedundantANDWithNOR: StructureValidator<_> =
        fun _ es ->
            let effects = es.AllEffects
            let triggers = es.AllTriggers

            let fNode =
                fun (last: BoolState) (x: Node) ->
                    match last, x.Key with
                    | BoolState.AND, k when k == "AND" -> BoolState.AND, None
                    | BoolState.OR, k when k == "OR" -> BoolState.OR, Some(inv (ErrorCodes.UnnecessaryBoolean "OR") x)
                    | _, k when k == "OR" || k == "NOR" -> BoolState.OR, None
                    | _, _ -> BoolState.AND, None

            (effects @ triggers)
            <&!&> (foldNodeWithState fNode BoolState.AND >> (fun e -> Invalid(Guid.NewGuid(), e)))

    let validateRedundantANDWithNOT: StructureValidator<_> =
        fun _ es ->
            let effects = es.AllEffects
            let triggers = es.AllTriggers

            let fNode =
                fun (last: BoolState) (x: Node) ->
                    match last, x.Key with
                    | BoolState.AND, k when k == "AND" -> BoolState.AND, None
                    | BoolState.OR, k when k == "OR" -> BoolState.OR, Some(inv (ErrorCodes.UnnecessaryBoolean "OR") x)
                    | _, k when k == "OR" || k == "NOT" -> BoolState.OR, None
                    | _, _ -> BoolState.AND, None

            (effects @ triggers)
            <&!&> (foldNodeWithState fNode BoolState.AND >> (fun e -> Invalid(Guid.NewGuid(), e)))

    let validateUnusuedTypes: LookupValidator<_> =
        let merge (a: Map<'a, 'b>) (b: Map<'a, 'b>) (f: 'a -> 'b * 'b -> 'b) =
            Map.fold
                (fun s k v ->
                    match Map.tryFind k s with
                    | Some v' -> Map.add k (f k (v, v')) s
                    | None -> Map.add k v s)
                a
                b

        fun l os _ ->
            let typesToCheck =
                l.typeDefs
                |> List.filter (fun t -> t.shouldBeReferenced <> RefNotRequired)
                |> List.map (fun t -> t.name, t.shouldBeReferenced)
                |> Map.ofList

            let obsoleteKeysByType =
                l.typeDefs
                |> List.fold
                    (fun acc typeDef ->
                        if Map.isEmpty typeDef.obsoleteKeys then
                            acc
                        else
                            let obsoleteKeys =
                                typeDef.obsoleteKeys
                                |> Map.toSeq
                                |> Seq.map fst
                                |> Set.ofSeq

                            match Map.tryFind typeDef.name acc with
                            | Some existing -> Map.add typeDef.name (Set.union existing obsoleteKeys) acc
                            | None -> Map.add typeDef.name obsoleteKeys acc)
                    Map.empty

            let typeInfos =
                l.typeDefInfo
                |> Map.filter (fun typename _ -> typesToCheck |> Map.containsKey typename)
                |> Map.toList

            let allReferences =
                os.AllWithData
                |> List.choose (fun (_, lazydata) -> lazydata.Force().Referencedtypes)
                |> Seq.fold (fun a b -> merge a b (fun _ (l1, l2) -> l1 @ l2)) Map.empty

            let parameterisedFireEffects =
                l.effects
                |> List.choose (function
                    | :? ScriptedEffect as se when se.FiredOnActions |> List.exists (fun t -> t.Contains '$') ->
                        Some se
                    | _ -> None)

            let resolvedFireTargets =
                if parameterisedFireEffects.IsEmpty then
                    Set.empty
                else
                    let effectsByName =
                        parameterisedFireEffects |> List.map (fun se -> se.Name.lower, se) |> Map.ofList

                    let resolveCalls (root: Node) =
                        let fNode =
                            fun (x: Node) children ->
                                let nodeCalls =
                                    x.Nodes
                                    |> Seq.collect (fun n ->
                                        match Map.tryFind n.KeyId.lower effectsByName with
                                        | Some se ->
                                            let callParams =
                                                n.Values |> List.map (fun lf -> lf.Key, lf.ValueText)

                                            se.FiredOnActions
                                            |> List.map (replaceScriptedParameters callParams)
                                            |> List.filter (fun t -> not (t.Contains '$'))
                                        | None -> [])
                                    |> List.ofSeq

                                nodeCalls @ children

                        foldNode2 fNode (@) [] root

                    // Per-entity cached; the key carries the parameterised
                    // effect signatures so effect edits invalidate naturally.
                    let cacheKey =
                        "commonResolvedFireOnActions:"
                        + string (
                            parameterisedFireEffects
                            |> List.map (fun se -> se.Name.lower, se.FiredOnActions)
                            |> hash
                        )

                    os.AddOrGetCached cacheKey (fun e -> resolveCalls e.entity |> List.map box)
                    |> List.map (fun o -> (o :?> string).ToLowerInvariant())
                    |> Set.ofList

            let checkTypeDef
                (requirement: ReferenceRequirement)
                (typename: string)
                (exactRefs: Set<string>)
                (wildcardRefs: System.Text.RegularExpressions.Regex list)
                (typedef: TypeDefInfo)
                =
                let id = typedef.id.ToLowerInvariant()
                let obsoleteKeys = obsoleteKeysByType |> Map.tryFind typename |> Option.defaultValue Set.empty

                // unless_subtyped: instances matching a subtype are engine-invoked.
                if obsoleteKeys.Contains id then
                    None
                elif requirement = RefRequiredUnlessSubtyped && not (List.isEmpty typedef.subtypes) then
                    None
                elif exactRefs.Contains id then
                    None
                elif wildcardRefs |> List.exists (fun regex -> regex.IsMatch typedef.id) then
                    None
                else
                    let severity =
                        if requirement = RefRequiredUnlessSubtyped then
                            Severity.Information
                        else
                            Severity.Warning

                    Some(invManual (ErrorCodes.UnusedType typename typedef.id severity) typedef.range typedef.id None)

            let checkType (typename: string, typedefs: TypeDefInfo array) =
                let requirement =
                    typesToCheck |> Map.tryFind typename |> Option.defaultValue RefRequired

                let refs =
                    allReferences
                    |> Map.tryFind typename
                    |> Option.defaultValue []
                    |> List.filter (fun ref -> ref.referenceType = ReferenceType.TypeDef)
                    |> List.map (fun r -> r.name.GetString())

                let exactRefs, paramRefs =
                    refs |> List.partition (fun r -> not (r.Contains '$'))

                let exactSet =
                    let direct = exactRefs |> List.map _.ToLowerInvariant() |> Set.ofList
                    // Resolved parameterised fire targets are on_action references.
                    if typename == "on_action" then
                        Set.union direct resolvedFireTargets
                    else
                        direct

                let wildcardRefs =
                    paramRefs
                    |> List.distinct
                    |> List.choose (fun r ->
                        let escaped = System.Text.RegularExpressions.Regex.Escape r

                        let pattern =
                            System.Text.RegularExpressions.Regex.Replace(escaped, @"\\\$.*?\\\$", ".+")

                        // A reference that is nothing but parameters (e.g.
                        // on_action = $ACTION$) would match every instance and
                        // disable the check entirely; require some literal text.
                        if pattern.Replace(".+", "").Length = 0 then
                            None
                        else
                            Some(
                                System.Text.RegularExpressions.Regex(
                                    $"^{pattern}$",
                                    System.Text.RegularExpressions.RegexOptions.IgnoreCase
                                )
                            ))

                typedefs
                |> Seq.choose (checkTypeDef requirement typename exactSet wildcardRefs)
                |> Seq.toList

            match typeInfos |> List.collect checkType with
            | [] -> OK
            | errors -> Invalid(Guid.NewGuid(), errors)

    let validateUndefinedModifierTypes: LookupValidator<_> =
        let merge (a: Map<'a, 'b>) (b: Map<'a, 'b>) (f: 'a -> 'b * 'b -> 'b) =
            Map.fold
                (fun s k v ->
                    match Map.tryFind k s with
                    | Some v' -> Map.add k (f k (v, v')) s
                    | None -> Map.add k v s)
                a
                b

        fun l os _ ->
            // Check that all referenced modifiers have a defined modifier type
            let modifierReferences =
                os.AllWithData
                |> List.choose (fun (_, lazydata) -> lazydata.Force().Referencedtypes)
                |> Seq.collect (fun map -> map.Values)
                |> Seq.collect id
                |> Seq.filter (fun ref -> ref.associatedType.IsSome && ref.associatedType.Value = "modifier_type")

            match l.typeDefInfo.TryFind "modifier_type" with
            | Some modifierTypes ->
                modifierReferences
                <&!&> (fun ref ->
                    match ref.referenceType with
                    | ReferenceType.TypeDefFuzzy
                    | ReferenceType.TypeDef ->
                        match modifierTypes |> Array.tryFind (fun t -> t.id = ref.name.GetString()) with
                        | Some _ -> OK
                        | None ->
                            Invalid(
                                Guid.NewGuid(),
                                [ invManual
                                      (ErrorCodes.UndefinedModifierTypeForModifier(ref.name.GetString()))
                                      ref.position
                                      (ref.name.GetString())
                                      None ]
                            )
                    | _ -> OK)
            | _ -> OK



    let private intern x =
        (CWTools.Utilities.StringResource.stringManager.InternIdentifierToken x).lower

    let private retrieveString x =
        CWTools.Utilities.StringResource.stringManager.GetStringForID x

    let validateOptimisations =
        fun (settings: UtilityParser.ListMergeOptimisationDefinition list) ->
            let createItem (def: UtilityParser.ListMergeOptimisationDefinition) =
                intern def.StartingKey,
                ((def.ConnectingKeys |> List.map intern), (def.SupportedValues |> List.map intern), def.TargetKey)

            let startMap = settings |> List.map createItem |> Map.ofList

            let res: StructureValidator<_> =
                fun _ es ->
                    let triggers = es.AllTriggers @ es.AllEffects

                    let fNode =
                        fun (last: (StringLowerToken list * StringLowerToken list * string * Node) option) (x: Node) ->
                            match last, Map.tryFind x.KeyId.lower startMap with
                            | None, None -> None, None
                            | None, Some([ inner ], targets, merged) ->
                                match x.TagById inner with
                                | Some rhs ->
                                    if targets |> List.contains rhs.lower then
                                        None,
                                        Some(inv (ErrorCodes.OptimisationMergeList (retrieveString inner) merged) x)
                                    else
                                        None, None
                                | None -> Some([ inner ], targets, merged, x), None
                            | None, Some(inners, targets, merged) -> Some(inners, targets, merged, x), None
                            | Some([], _, _, _), _ -> None, None
                            | Some([ inner ], targets, merged, source), _ ->
                                if x.KeyId.lower = inner then
                                    None,
                                    Some(inv (ErrorCodes.OptimisationMergeList (retrieveString inner) merged) source)
                                else
                                    None, None
                            | Some([ inner; inner2 ], targets, merged, source), _ ->
                                if x.KeyId.lower = inner && x.HasById inner2 then
                                    None,
                                    Some(inv (ErrorCodes.OptimisationMergeList (retrieveString inner) merged) source)
                                else
                                    None, None
                            | Some(inner :: inners, targets, merged, source), _ ->
                                if x.KeyId.lower = inner then
                                    Some(inners, targets, merged, source), None
                                else
                                    None, None

                    triggers
                    <&!&> (foldNodeWithState fNode None >> (fun e -> Invalid(Guid.NewGuid(), e)))

            res

    let validateConfiguredOnActionEventTypes: LookupValidator<_> =
        fun l os _ ->
            let onActionConfigs = l.extendedConfigMetadata.onActions

            if Map.isEmpty onActionConfigs then
                OK
            else
                let typeExists typeName = l.typeDefInfo |> Map.containsKey typeName

                let expectedTypeNames eventType =
                    [ "event." + eventType
                      eventType + "_event"
                      eventType ]
                    |> List.filter typeExists

                let eventTypesById =
                    l.typeDefInfo
                    |> Map.toSeq
                    |> Seq.filter (fun (typeName, _) ->
                        typeName.Equals("event", StringComparison.OrdinalIgnoreCase)
                        || typeName.StartsWith("event.", StringComparison.OrdinalIgnoreCase)
                        || typeName.EndsWith("_event", StringComparison.OrdinalIgnoreCase))
                    |> Seq.collect (fun (typeName, infos) -> infos |> Seq.map (fun info -> info.id, typeName))
                    |> Seq.groupBy fst
                    |> Seq.map (fun (id, values) -> id, values |> Seq.map snd |> Set.ofSeq)
                    |> Map.ofSeq

                let eventContainerKeys =
                    set [ "events"; "random_events"; "first_valid"; "first_valid_on_action" ]

                let collectEvents (onAction: Node) =
                    let rec collect inEventContainer (node: Node) =
                        let nowInEventContainer = inEventContainer || eventContainerKeys.Contains(node.Key)

                        let own =
                            if nowInEventContainer then
                                seq {
                                    for leafValue in node.LeafValues do
                                        yield leafValue.ValueText, leafValue.Position

                                    for leaf in node.Leaves do
                                        yield leaf.ValueText, leaf.Position
                                }
                            else
                                Seq.empty

                        seq {
                            yield! own

                            for child in node.Nodes do
                                yield! collect nowInEventContainer child
                        }

                    collect false onAction
                    |> Seq.filter (fun (eventId, _) ->
                        not (String.IsNullOrWhiteSpace eventId)
                        && eventId.IndexOf('$') < 0
                        && eventId.IndexOf('@') < 0)

                let validateOnAction (onAction: Node) =
                    match onActionConfigs |> Map.tryFind onAction.Key with
                    | None -> Seq.empty
                    | Some config ->
                        let expected = expectedTypeNames config.eventType

                        if List.isEmpty expected then
                            Seq.empty
                        else
                            collectEvents onAction
                            |> Seq.choose (fun (eventId, pos) ->
                                let actualTypes =
                                    eventTypesById |> Map.tryFind eventId |> Option.defaultValue Set.empty

                                if expected |> List.exists actualTypes.Contains then
                                    None
                                else
                                    Some(
                                        invManual
                                            (ErrorCodes.CustomError
                                                $"On action %s{onAction.Key} expects %s{config.eventType} events, but %s{eventId} is not one."
                                                Severity.Warning)
                                            pos
                                            eventId
                                            None
                                    ))

                let errors =
                    os.AllOfTypeChildren STLConstants.EntityType.OnActions
                    |> Seq.collect validateOnAction
                    |> Seq.toList

                match errors with
                | [] -> OK
                | errors -> Invalid(Guid.NewGuid(), errors)

    let validateDefinitionInjections: LookupValidator<_> =
        fun l os _ ->
            let tryInjectionKey (key: string) =
                let index = key.IndexOf(':')

                if index <= 0 || index >= key.Length - 1 then
                    None
                else
                    let mode = key.Substring(0, index).ToUpperInvariant()
                    let target = key.Substring(index + 1)

                    match mode with
                    | "INJECT"
                    | "REPLACE"
                    | "TRY_INJECT"
                    | "TRY_REPLACE"
                    | "INJECT_OR_CREATE"
                    | "REPLACE_OR_CREATE" -> Some(mode, target)
                    | _ -> None

            let lenientModes =
                set [ "TRY_INJECT"; "TRY_REPLACE"; "INJECT_OR_CREATE"; "REPLACE_OR_CREATE" ]

            let knownTargets =
                l.typeDefInfo
                |> Map.toSeq
                |> Seq.collect (fun (_, infos) -> infos |> Seq.map (fun info -> info.id.ToLowerInvariant()))
                |> Set.ofSeq

            let errors =
                os.All
                |> Seq.collect (fun root ->
                    root.Nodes
                    |> Seq.choose (fun node ->
                        match tryInjectionKey node.Key with
                        | Some(mode, target) when
                            not (lenientModes.Contains mode)
                            && not (knownTargets.Contains(target.ToLowerInvariant()))
                            ->
                            Some(
                                invManual
                                    (ErrorCodes.CustomError
                                        $"Definition injection target %s{target} was not found for mode %s{mode}."
                                        Severity.Warning)
                                    node.Position
                                    node.Key
                                    None
                            )
                        | _ -> None))
                |> Seq.toList

            match errors with
            | [] -> OK
            | errors -> Invalid(Guid.NewGuid(), errors)

    let commonValidationRules =
        [ valUniqueTypes, "uniques"; validateUnusuedTypes, "requireds" ]
