namespace CWTools.Process

open System.Collections.Generic
open CSharpHelpers
open CWTools.Process.ProcessCore
open CWTools.Process
open System
open CWTools.Utilities
open CWTools.Utilities.Utils
open CWTools.Common

module STLProcess =

    [<Struct>]
    type private ScopeMask =
        val Bits0: uint64
        val Bits1: uint64
        val Bits2: uint64
        val Bits3: uint64

        new(bits0, bits1, bits2, bits3) =
            { Bits0 = bits0
              Bits1 = bits1
              Bits2 = bits2
              Bits3 = bits3 }

    let private emptyScopeMask = ScopeMask(0UL, 0UL, 0UL, 0UL)

    let private scopeMaskOfList (scopes: Scope list) =
        let mutable bits0 = 0UL
        let mutable bits1 = 0UL
        let mutable bits2 = 0UL
        let mutable bits3 = 0UL

        for scope in scopes do
            let tag = int scope.Tag
            let bit = 1UL <<< (tag &&& 63)

            match tag >>> 6 with
            | 0 -> bits0 <- bits0 ||| bit
            | 1 -> bits1 <- bits1 ||| bit
            | 2 -> bits2 <- bits2 ||| bit
            | _ -> bits3 <- bits3 ||| bit

        ScopeMask(bits0, bits1, bits2, bits3)

    let private intersectScopeMasks (left: ScopeMask) (right: ScopeMask) =
        ScopeMask(
            left.Bits0 &&& right.Bits0,
            left.Bits1 &&& right.Bits1,
            left.Bits2 &&& right.Bits2,
            left.Bits3 &&& right.Bits3
        )

    let private isEmptyScopeMask (mask: ScopeMask) =
        (mask.Bits0 ||| mask.Bits1 ||| mask.Bits2 ||| mask.Bits3) = 0UL

    let private scopeMaskContains (mask: ScopeMask) (scope: Scope) =
        let tag = int scope.Tag
        let bit = 1UL <<< (tag &&& 63)

        match tag >>> 6 with
        | 0 -> (mask.Bits0 &&& bit) <> 0UL
        | 1 -> (mask.Bits1 &&& bit) <> 0UL
        | 2 -> (mask.Bits2 &&& bit) <> 0UL
        | _ -> (mask.Bits3 &&& bit) <> 0UL

    let private isRecursiveScopeBlock (key: string) =
        key == "OR"
        || key == "AND"
        || key == "NOR"
        || key == "NAND"
        || key == "NOT"
        || key == "if"
        || key == "else"
        || key == "hidden_effect"
        || key == "limit"

    let private inferScriptedTriggerScopes
        (strict: bool)
        (vanillaTriggersAndEffects: Dictionary<StringToken, Scope list>)
        (newTriggersAndEffects: Map<StringToken, Scope list>)
        (scopedEffects: Map<StringToken, Scope list>)
        (root: string)
        (node: Node)
        =
        let allScopes = scopeManager.AllScopes
        let allScopesMask = scopeMaskOfList allScopes

        let normalizeMask mask =
            if isEmptyScopeMask mask && not strict then allScopesMask else mask

        let rec inferScopeMask (current: Node) =
            let mutable combined = allScopesMask

            let addScopes scopes =
                combined <- intersectScopeMasks combined (normalizeMask scopes)

            for child in current.Children do
                let childScopes =
                    if
                        child.Key = root
                        || child.Key.StartsWith("event_target:", StringComparison.OrdinalIgnoreCase)
                    then
                        allScopesMask
                    elif isRecursiveScopeBlock child.Key then
                        inferScopeMask child
                    else
                        Scopes.STL.sourceScope scopedEffects child.Key |> scopeMaskOfList

                addScopes childScopes

            for value in current.Values do
                let valueScopes =
                    if value.Key.StartsWith('@') || value.Key = root then
                        allScopesMask
                    else
                        match vanillaTriggersAndEffects.TryGetValue value.KeyId.normal with
                        | true, scopes -> scopeMaskOfList scopes
                        | false, _ ->
                            match Map.tryFind value.KeyId.normal newTriggersAndEffects with
                            | Some scopes -> scopeMaskOfList scopes
                            | None -> emptyScopeMask

                addScopes valueScopes

            combined

        // Scope implements the ordering used by the previous Set.toList result.
        inferScopeMask node
        |> fun mask -> allScopes |> List.filter (scopeMaskContains mask)
        |> List.sort

    // Kept as a Set-returning API for existing consumers outside the Stellaris lookup path.
    let scriptedTriggerScope
        (strict: bool)
        (vanillaTriggersAndEffects: Dictionary<StringToken, Scope list>)
        (newTriggersAndEffects: Map<StringToken, Scope list>)
        (scopedEffects: Map<StringToken, Scope list>)
        (root: string)
        (node: Node)
        =
        inferScriptedTriggerScopes strict vanillaTriggersAndEffects newTriggersAndEffects scopedEffects root node
        |> Set.ofList

    /// Substitute parameters in a string. Parameters are in the form $PARAM$ or $PARAM|default$
    let private parameterPattern =
        System.Text.RegularExpressions.Regex(@"\$([^$|]+)(?:\|([^$]*))?\$", System.Text.RegularExpressions.RegexOptions.Compiled)

    let private parameterName (text: string) =
        let pipeIndex = text.IndexOf('|')
        if pipeIndex >= 0 then text.Substring(0, pipeIndex) else text

    let private normalizeParameterKey (key: string) =
        key.Trim().Trim('$') |> parameterName

    let substituteParams (paramList: (string * string) list) (text: string) : string =
        let values =
            paramList
            |> List.choose (fun (param, value) ->
                let name = normalizeParameterKey param
                if String.IsNullOrWhiteSpace name then None else Some(name, value))
            |> Map.ofList

        parameterPattern.Replace(
            text,
            System.Text.RegularExpressions.MatchEvaluator(fun m ->
                let name = m.Groups.[1].Value
                match values |> Map.tryFind name with
                | Some value -> value
                | None when m.Groups.[2].Success -> m.Groups.[2].Value
                | None -> m.Value)
        )

    let private eventTargetName (value: string) =
        let prefix = "event_target:"
        let mutable raw = value.Trim()

        while raw.StartsWith(prefix, StringComparison.OrdinalIgnoreCase) do
            raw <- raw.Substring(prefix.Length)

        let atIndex = raw.IndexOf('@')
        let dotIndex = raw.IndexOf('.')

        let name =
            if atIndex >= 0 && (dotIndex < 0 || dotIndex > atIndex) then
                raw
            else if dotIndex >= 0 then
                raw.Substring(0, dotIndex)
            else
                raw

        if name.EndsWith('?') then name.Substring(0, name.Length - 1) else name

    let findAllUsedEventTargetsWithParams (parameters: (string * string) list) (event: Node) =
        let fNode =
            (fun (x: Node) (children: string list) ->
                let targetFromString (k: string) =
                    substituteParams parameters (eventTargetName k) |> eventTargetName

                let inner (leaf: Leaf) =
                    let value = leaf.Value.ToRawString()
                    if value.StartsWith("event_target:", StringComparison.OrdinalIgnoreCase) then
                        Some(value |> targetFromString)
                    else
                        None

                let leaves = (x.Leaves |> Seq.choose inner |> List.ofSeq)
                match x.Key with
                | k when k.StartsWith("event_target:", StringComparison.OrdinalIgnoreCase) ->
                    targetFromString k :: (leaves @ children)
                | _ -> (leaves @ children)

            )

        let fCombine = (@)
        event |> (foldNode2 fNode fCombine ([] : string list)) |> Set.ofList

    let findAllUsedEventTargets (event: Node) =
        findAllUsedEventTargetsWithParams [] event

    let findAllSavedEventTargetsWithParams (parameters: (string * string) list) (event: Node) =
        let fNode =
            (fun (x: Node) (children: string list) ->
                let inner (leaf: Leaf) =
                    if leaf.Key == "save_event_target_as" then
                        let value = leaf.Value.ToRawString()
                        Some(substituteParams parameters value)
                    else
                        None

                (x.Values |> List.choose inner) @ children)

        let fCombine = (@)
        event |> (foldNode2 fNode fCombine ([] : string list)) |> Set.ofList

    let findAllSavedEventTargets (event: Node) =
        findAllSavedEventTargetsWithParams [] event

    let findAllExistsEventTargetsWithParams (parameters: (string * string) list) (event: Node) =
        let fNode =
            (fun (x: Node) (children: string list) ->
                let inner (leaf: Leaf) =
                    let value = leaf.Value.ToRawString()
                    if
                        leaf.Key == "exists"
                        && value.StartsWith("event_target:", StringComparison.OrdinalIgnoreCase)
                    then
                        Some(substituteParams parameters (eventTargetName value) |> eventTargetName)
                    else
                        None

                (x.Values |> List.choose inner) @ children)

        let fCombine = (@)
        event |> (foldNode2 fNode fCombine ([] : string list)) |> Set.ofList

    let findAllExistsEventTargets (event: Node) =
        findAllExistsEventTargetsWithParams [] event

    let findAllSavedGlobalEventTargets (event: Node) =
        let fNode =
            (fun (x: Node) children ->
                let inner (leaf: Leaf) =
                    if leaf.Key == "save_global_event_target_as" then
                        Some(leaf.Value.ToRawString())
                    else
                        None

                (x.Values |> List.choose inner) @ children)

        let fCombine = (@)
        event |> (foldNode2 fNode fCombine []) |> Set.ofList

    /// Raw fire_on_action targets in an effect body. May contain $PARAM$
    /// placeholders, resolved to concrete on_action names at call sites.
    let findAllFiredOnActions (event: Node) =
        let fNode =
            (fun (x: Node) children ->
                let inner (leaf: Leaf) =
                    if x.Key == "fire_on_action" && leaf.Key == "on_action" then
                        Some(leaf.Value.ToRawString())
                    else
                        None

                (x.Values |> List.choose inner) @ children)

        event |> (foldNode2 fNode (@) []) |> Set.ofList

    let getScriptedTriggerScope
        (firstRun: bool)
        (effectType: EffectType)
        (scopedEffects: Map<StringLowerToken, Scope list>)
        (vanillaTriggerAndEffectDict: Dictionary<StringToken, Scope list>)
        (newTriggerAndEffectMap: Map<StringToken, Scope list>)
        ((node, comments): Node * string list)
        =
        let scopes =
            inferScriptedTriggerScopes
                (not firstRun)
                vanillaTriggerAndEffectDict
                newTriggerAndEffectMap
                scopedEffects
                node.Key
                node

        let commentString = comments |> List.truncate 5 |> String.concat ("\n")
        let globals = findAllSavedGlobalEventTargets node
        let savetargets = findAllSavedEventTargets node
        let usedtargets = findAllUsedEventTargets node
        let firedonactions = findAllFiredOnActions node

        ScriptedEffect(
            node.KeyId,
            scopes,
            effectType,
            commentString,
            globals |> Set.toList,
            savetargets |> Set.toList,
            usedtargets |> Set.toList,
            firedonactions |> Set.toList
        )

    /// Propagates saved/used/global event targets through nested scripted-effect
    /// them in turn.
    let addNestedEventTargetsToEffects (rawEffects: (Node * string list) list) (effects: Effect list) : Effect list =
        let scripted =
            effects
            |> List.choose (function
                | :? ScriptedEffect as e -> Some e
                | _ -> None)

        if List.isEmpty scripted then
            effects
        else
            let effectNames = scripted |> List.map (fun e -> e.Name.lower) |> Set.ofList

            let extractCallParams (callNode: Node) =
                callNode.Values |> List.map (fun l -> ("$" + l.Key + "$", l.ValueText))

            // Calls to other scripted effects inside a body: leaf calls
            // (`some_effect = yes`) carry no params, node calls carry their values.
            let findNestedCalls (node: Node) =
                let fNode =
                    (fun (x: Node) children ->
                        let leafCalls =
                            x.Values
                            |> List.choose (fun l ->
                                if Set.contains l.KeyId.lower effectNames then
                                    Some(l.KeyId.lower, [])
                                else
                                    None)

                        let nodeCalls =
                            x.Nodes
                            |> Seq.choose (fun n ->
                                if Set.contains n.KeyId.lower effectNames then
                                    Some(n.KeyId.lower, extractCallParams n)
                                else
                                    None)
                            |> List.ofSeq

                        leafCalls @ nodeCalls @ children)

                foldNode2 fNode (@) [] node

            let callsByName =
                rawEffects
                |> List.choose (fun (node, _) ->
                    if Set.contains node.KeyId.lower effectNames then
                        match findNestedCalls node with
                        | [] -> None
                        | calls -> Some(node.KeyId.lower, calls)
                    else
                        None)
                |> Map.ofList

            let mutable current =
                scripted
                |> List.map (fun e ->
                    e.Name.lower,
                    (Set.ofList e.SavedEventTargets, Set.ofList e.UsedEventTargets, Set.ofList e.GlobalEventTargets))
                |> Map.ofList

            let step () =
                let updated =
                    current
                    |> Map.map (fun name (saved, used, globals) ->
                        match Map.tryFind name callsByName with
                        | None -> (saved, used, globals)
                        | Some calls ->
                            calls
                            |> List.fold
                                (fun (s, u, g) (callee, callParams) ->
                                    match Map.tryFind callee current with
                                    | None -> (s, u, g)
                                    | Some(cs, cu, cg) ->
                                        let sub = Set.map (substituteParams callParams)
                                        let subUsed =
                                            Set.map
                                                (fun target -> substituteParams callParams target |> eventTargetName)
                                                cu

                                        (Set.union s (sub cs), Set.union u subUsed, Set.union g (sub cg)))
                                (saved, used, globals))

                let changed = updated <> current
                current <- updated
                changed

            let mutable i = 0

            while step () && i < 10 do
                i <- i + 1

            effects
            |> List.map (fun e ->
                match e with
                | :? ScriptedEffect as se ->
                    match Map.tryFind se.Name.lower current with
                    | Some(saved, used, globals) ->
                        ScriptedEffect(
                            se.Name,
                            se.Scopes,
                            se.Type,
                            se.Comments,
                            globals |> Set.toList,
                            saved |> Set.toList,
                            used |> Set.toList,
                            se.FiredOnActions
                        )
                        :> Effect
                    | None -> e
                | _ -> e)

    let rec cloneNode (source: Node) =
        let rec mapChild =
            function
            | NodeC n ->
                let newNode = Node(n.Key, n.Position)
                newNode.Trivia <- n.Trivia
                newNode.AllArray <- n.AllArray |> Array.map mapChild
                NodeC newNode
            | LeafC l ->
                let newLeaf = Leaf(l.Key, l.Value, l.Position, l.Operator)
                newLeaf.Trivia <- l.Trivia
                LeafC newLeaf
            | LeafValueC lv ->
                let newLeafValue = LeafValue(lv.Value, lv.Position)
                newLeafValue.Trivia <- lv.Trivia
                LeafValueC newLeafValue
            | ValueClauseC vc ->
                let newVC = ValueClause([||], vc.Position)
                newVC.Trivia <- vc.Trivia
                newVC.AllArray <- vc.AllArray |> Array.map mapChild
                newVC.Keys <- vc.Keys
                ValueClauseC newVC
            | CommentC c -> CommentC c

        let newNode = Node(source.Key, source.Position)
        newNode.Trivia <- source.Trivia
        newNode.AllArray <- source.AllArray |> Array.map mapChild
        newNode

    let shipProcess = BaseProcess()
    let simpleProcess = BaseProcess()

    let staticModifierCategory (modifiers: System.Linq.ILookup<string, ModifierCategory>) (node: Node) =
        node.Leaves
        |> Seq.filter (fun v -> v.Key <> "icon" && v.Key <> "icon_frame")
        |> Seq.filter (fun v -> modifiers.Contains v.Key)
        |> Seq.collect (fun v -> modifiers[v.Key])
        |> Seq.distinct

    let getStaticModifierCategory modifierMap (node: Node) =
        let categories = staticModifierCategory modifierMap node |> List.ofSeq

        { tag = node.Key
          categories = categories }
