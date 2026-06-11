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

    //TODO remove all this
    let rec scriptedTriggerScope
        (strict: bool)
        (vanillaTriggersAndEffects: Dictionary<StringToken, Scope list>)
        (newTriggersAndEffects: Map<StringToken, Scope list>)
        (scopedEffects: Map<StringToken, Scope list>)
        (root: string)
        (node: Node)
        =
        let anyBlockKeys =
            [ "OR"; "AND"; "NOR"; "NAND"; "NOT"; "if"; "else"; "hidden_effect" ]

        let nodeScopes =
            node.Children
            |> List.map (function
                | x when x.Key = root -> scopeManager.AllScopes |> Set.ofList
                | x when x.Key.StartsWith("event_target:", StringComparison.OrdinalIgnoreCase) ->
                    scopeManager.AllScopes |> Set.ofList
                // | x when targetKeys |> List.exists (fun y -> y == x.Key) ->
                //     allScopes
                | x when anyBlockKeys |> List.exists (fun y -> y == x.Key) ->
                    scriptedTriggerScope strict vanillaTriggersAndEffects newTriggersAndEffects scopedEffects root x
                | x when x.Key == "limit" ->
                    scriptedTriggerScope strict vanillaTriggersAndEffects newTriggersAndEffects scopedEffects root x
                | x -> Scopes.STL.sourceScope scopedEffects x.Key |> Set.ofList
            // match STLScopes.sourceScope x.Key with
            // | Some v -> v
            // | None -> effects |> List.filter (fun (n, _) -> n = x.Key) |> List.map (fun (_, ss) -> ss) |> List.collect id
            )

        let valueScopes =
            node.Values
            //|> List.filter (fun v -> v.Key.StartsWith("@"))
            |> List.map (function
                | x when x.Key.StartsWith('@') -> scopeManager.AllScopes |> Set.ofList
                | x when x.Key = root -> scopeManager.AllScopes |> Set.ofList
                | x ->
                    match vanillaTriggersAndEffects.TryGetValue x.KeyId.normal with
                    | true, scopeSet -> scopeSet |> Set.ofList
                    | false, _ ->
                        (Map.tryFind x.KeyId.normal newTriggersAndEffects)
                        |> Option.map Set.ofList
                        |> Option.defaultValue Set.empty)
        // |> Seq.tryFind (fun e -> e.Name.normal = x.KeyId.normal)
        // |> (function
        // | Some e -> e.ScopesSet
        // | None -> Set.empty))

        let combinedScopes =
            nodeScopes @ valueScopes
            |> List.map (function
                | x when Set.isEmpty x ->
                    (if strict then
                         Set.empty
                     else
                         scopeManager.AllScopes |> Set.ofList)
                | x -> x)

        combinedScopes |> List.fold Set.intersect (scopeManager.AllScopes |> Set.ofList)
    //combinedScopes |> List.fold (fun a b -> Set.intersect (Set.ofList a) (Set.ofList b) |> Set.toList) allScopes

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
        let raw = value.Substring(13)
        let atIndex = raw.IndexOf('@')
        let dotIndex = raw.IndexOf('.')

        if atIndex >= 0 && (dotIndex < 0 || dotIndex > atIndex) then
            raw
        else if dotIndex >= 0 then
            raw.Substring(0, dotIndex)
        else
            raw

    let findAllUsedEventTargetsWithParams (parameters: (string * string) list) (event: Node) =
        let fNode =
            (fun (x: Node) (children: string list) ->
                let targetFromString (k: string) =
                    substituteParams parameters (eventTargetName k)

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
                        Some(substituteParams parameters (eventTargetName value))
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

    let getScriptedTriggerScope
        (firstRun: bool)
        (effectType: EffectType)
        (scopedEffects: Map<StringLowerToken, Scope list>)
        (vanillaTriggerAndEffectDict: Dictionary<StringToken, Scope list>)
        (newTriggerAndEffectMap: Map<StringToken, Scope list>)
        ((node, comments): Node * string list)
        =
        let scopes =
            scriptedTriggerScope
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

        ScriptedEffect(
            node.KeyId,
            scopes |> Set.toList,
            effectType,
            commentString,
            globals |> Set.toList,
            savetargets |> Set.toList,
            usedtargets |> Set.toList
        )

    /// Propagates saved/used/global event targets through nested scripted-effect
    /// calls with parameter substitution: if effect A contains `B = { TARGET = foo }`
    /// and B contains `save_event_target_as = $TARGET$` (or the global variant),
    /// then A is credited with saving `foo`. Iterates to a fixpoint so chains of
    /// nested calls resolve. Targets still containing `$param$` placeholders are
    /// kept so an outer call site (another effect or an event) can substitute
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
                                        (Set.union s (sub cs), Set.union u (sub cu), Set.union g (sub cg)))
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
                            used |> Set.toList
                        )
                        :> Effect
                    | None -> e
                | _ -> e)

    let rec cloneNode (source: Node) =
        let rec mapChild =
            function
            | NodeC n ->
                let newNode = Node(n.Key, n.Position)
                newNode.AllArray <- n.AllArray |> Array.map mapChild
                NodeC newNode
            | LeafC l -> LeafC(Leaf(l.Key, l.Value, l.Position, l.Operator))
            | LeafValueC lv -> LeafValueC(LeafValue(lv.Value, lv.Position))
            | ValueClauseC vc ->
                let newVC = ValueClause([||], vc.Position)
                newVC.AllArray <- vc.AllArray |> Array.map mapChild
                newVC.Keys <- vc.Keys
                ValueClauseC newVC
            | CommentC c -> CommentC c

        let newNode = Node(source.Key, source.Position)
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
