namespace CWTools.Validation.Stellaris

open CWTools.Validation
open CWTools.Validation.ValidationCore
open CWTools.Process
open CWTools.Process.ProcessCore
open CWTools.Utilities.Utils
open System
open QuickGraph
open CWTools.Common

module STLEventValidation =
    type 'a Node = 'a * 'a list
    type 'a Edge = 'a * 'a

    type 'a Graph = 'a list * 'a Edge list

    type 'a AdjacencyGraph = 'a Node list

    type Vertex<'a> = { string: 'a }

    let connectedComponents (g: 'a Graph) =
        match g with
        | _, [] -> []
        | _, es ->
            let edges =
                List.map ((fun x -> ({ string = fst x }, { string = snd x })) >> Edge<Vertex<'a>>) es

            let undirGraph = edges.ToUndirectedGraph()

            let algo =
                QuickGraph.Algorithms.ConnectedComponents.ConnectedComponentsAlgorithm(undirGraph)

            algo.Compute()

            let res =
                algo.Components
                |> Seq.groupBy (fun kv -> kv.Value)
                |> Seq.map (fun (_, vertices) -> vertices |> Seq.map (fun kv -> kv.Key) |> List.ofSeq)
                |> List.ofSeq

            res |> List.map (fun vs -> vs |> List.map (fun v -> v.string))

    let findAllReferencedEvents (projects: (Node * string) list) (event: Node) =
        let eventEffectKeys =
            [ "ship_event"
              "pop_event"
              "fleet_event"
              "pop_faction_event"
              "country_event"
              "planet_event" ]

        let fNode =
            (fun (x: Node) children ->
                match x.Key with
                | k when eventEffectKeys |> List.exists (fun f -> f == k) -> x.TagText "id" :: children
                | _ -> children)

        let fpNode =
            (fun (x: Node) children ->
                match x.Key with
                | "enable_special_project" -> [ x.TagText "name" ]
                | _ -> children)

        let directCalls = event.Children |> List.collect (foldNode7 fNode) // |> List.fold (@) []
        let referencedProjects = event.Children |> List.collect (foldNode7 fpNode)
        //log "%s projs %A" (event.ID) referencedProjects
        let projectKeys =
            [ "on_success"
              "on_fail"
              "on_start"
              "on_progress_25"
              "on_progress_50"
              "on_progress_75" ]

        let getProjectTarget (n: Node) =
            n.Children
            |> List.filter (fun c -> List.contains c.Key projectKeys)
            |> List.collect (foldNode7 fNode)

        let projectTargets =
            projects
            |> List.filter (fun (_, pk) -> List.contains pk referencedProjects)
            |> List.collect (fun (p, _) -> getProjectTarget p)
        //log "%s proj targets %A" (event.ID) projectTargets
        directCalls @ projectTargets

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
                    substituteParams parameters (eventTargetName k)

                let inner (children: string list) (leaf: Leaf) =
                    let value = leaf.Value.ToRawString()

                    if value.StartsWith("event_target:", StringComparison.OrdinalIgnoreCase) then
                        (value |> targetFromString) :: children
                    else
                        children

                let innerValues = x.Leaves |> Seq.fold inner children

                match x.Key with
                | k when k.StartsWith("event_target:", StringComparison.OrdinalIgnoreCase) ->
                    (targetFromString k) :: innerValues
                | _ -> innerValues
            )
        event |> (foldNode7 fNode) |> Set.ofList

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

    /// Local and global event targets saved by scripted-effect calls inside an
    /// arbitrary effect block, with call-site parameters substituted (e.g.
    /// `hire_effect = { GLOBAL_EVENT_TARGET = ganthuata }` where the callee does
    /// `save_global_event_target_as = $GLOBAL_EVENT_TARGET$`). Unresolved
    /// `$param$` placeholders are dropped.
    let findSubstitutedCallSaves (effectsByName: Map<_, ScriptedEffect>) (node: Node) =
        let substitutedSaves (callParams: (string * string) list) (effect: ScriptedEffect) =
            effect.SavedEventTargets @ effect.GlobalEventTargets
            |> List.map (substituteParams callParams)
            |> List.filter (fun target -> not (target.Contains("$")))

        let fNode =
            (fun (x: Node) children ->
                let leafCalls =
                    x.Values
                    |> List.collect (fun l ->
                        match Map.tryFind l.KeyId.lower effectsByName with
                        | Some e -> substitutedSaves [] e
                        | None -> [])

                let nodeCalls =
                    x.Nodes
                    |> Seq.collect (fun n ->
                        match Map.tryFind n.KeyId.lower effectsByName with
                        | Some e ->
                            let callParams =
                                n.Values |> List.map (fun l -> ("$" + l.Key + "$", l.ValueText))

                            substitutedSaves callParams e
                        | None -> [])
                    |> List.ofSeq

                leafCalls @ nodeCalls @ children)

        node |> (foldNode2 fNode (@) []) |> Set.ofList

    let addScriptedEffectTargets
        (effects: ScriptedEffect list)
        (((eid, e), s, u, r, x): (string * Node) * Set<string> * Set<string> * string list * Set<string>)
        =
        // Helper to extract params from a scripted effect call node
        let extractCallParams (callNode: Node) =
            callNode.Values
            |> List.map (fun l -> ("$" + l.Key + "$", l.ValueText))

        let getScriptedEffectTargets (callParams: (string * string) list) (effect: ScriptedEffect) =
            let substituteAndFilter targets =
                targets
                |> List.map (substituteParams callParams)
                |> List.filter (fun target -> not (target.Contains("$")))
                |> Set.ofList

            substituteAndFilter effect.SavedEventTargets, substituteAndFilter effect.UsedEventTargets

        let fNode =
            (fun (x: Node) (s, u) ->
                let inner (leaf: Leaf) =
                    effects
                    |> List.tryFind (fun e -> leaf.KeyId.lower = e.Name.lower)
                    |> Option.map (fun e ->
                        let callParams =
                            x.Nodes
                            |> Seq.tryFind (fun n -> n.KeyId.lower = leaf.KeyId.lower)
                            |> Option.map extractCallParams
                            |> Option.defaultValue []

                        getScriptedEffectTargets callParams e)

                let leafTargets =
                    x.Values
                    |> List.choose inner

                let nodeTargets =
                    effects
                    |> List.tryFind (fun e -> x.KeyId.lower = e.Name.lower)
                    |> Option.map (getScriptedEffectTargets (extractCallParams x))
                    |> Option.toList

                (leafTargets @ nodeTargets)
                |> List.fold (fun (s, u) (s2, u2) ->
                    Set.union s s2, Set.union u u2) (s, u))

        let fCombine = (fun (s, u) (s2, u2) -> Set.union s s2, Set.union u u2)
        let s2, u2 = foldNode2 fNode fCombine (s, u) e
        ((eid, e), s2, u2, r, x)

    let addSystemInitializer
        (sinits: Node list)
        (((eid, e), s, u, r, x): (string * Node) * Set<string> * Set<string> * string list * Set<string>)
        =
        let fNode =
            (fun (x: Node) (s, u) ->
                match x.Key with
                | "spawn_system" ->
                    let initializer = x.TagText "initializer"

                    match sinits |> List.tryFind (fun f -> f.Key == initializer) with
                    | None -> s, u
                    | Some sys ->
                        (findAllSavedEventTargets sys |> Set.toList) @ s,
                        (findAllUsedEventTargets sys |> Set.toList) @ u
                | _ -> s, u)

        let fCombine = (fun (s, u) (s2, u2) -> s @ s2, u @ u2)
        let s2, u2 = foldNode2 fNode fCombine (s |> Set.toList, u |> Set.toList) e
        ((eid, e), s2 |> Set.ofList, u2 |> Set.ofList, r, x)

    let checkEventChain
        (effects: ScriptedEffect list)
        (sinits: Node list)
        (projects: (Node * string) list)
        (globals: Set<string>)
        (events: Node list)
        =
        let filterParams = Set.filter (fun (s: string) -> not (s.Contains("$")))
        let mutable current =
            events
            |> List.map (fun e ->
                ((e.TagText "id", e),
                 findAllSavedEventTargets e |> filterParams,
                 findAllUsedEventTargets e |> filterParams,
                 findAllReferencedEvents projects e,
                 findAllExistsEventTargets e |> filterParams))
            //|> List.map (fun (e, s, u, r, x) -> log "%s %A %A %A %A" e.ID s u r x; (e, s, u, r, x))
            //|> (fun f -> log "%A" f; f)
            |> List.map (addScriptedEffectTargets effects)
            |> List.map (addSystemInitializer sinits)
            //|> List.map (fun (e, s, u, r, x) -> log "%s %A %A %A %A" e.ID s u r x; (e, s, u, r, x))
            |> List.map (fun (e, s, u, r, x) -> e, s, s, Set.difference u s, r, x, x)

        let getRequiredTargets (ids: string list) =
            if List.isEmpty ids then
                Set.empty
            else
                let ret =
                    ids
                    |> List.choose (fun x ->
                        current
                        |> List.tryPick (fun ((e2id, e2), _, _, u2, _, _, _) ->
                            if e2id = x then Some(Set.toList u2) else None))
                    |> List.collect id
                    |> Set.ofList
                // log "%A" ret
                ret

        let getExistsTargets currentx (ids: string list) =
            let inter =
                ids
                |> List.choose (fun x ->
                    current
                    |> List.tryPick (fun ((e2id, e2), _, _, u2, _, _, x2) -> if e2id = x then Some(u2, x2) else None))

            let all =
                inter |> List.fold (fun xs (u, x) -> Set.union (Set.union u x) xs) currentx

            let ret =
                inter
                |> List.fold
                    (fun xs (u, x) ->
                        xs
                        |> Set.toList
                        |> List.fold
                            (fun nxs nx ->
                                if Set.contains nx u && not (Set.contains nx x) then
                                    nxs
                                else
                                    nx :: nxs)
                            []
                        |> Set.ofList)
                    all
            // log "%A" ret
            ret

        let update (e, os, s, u, r, ox, x) =
            e, os, s, Set.difference (Set.union u (getRequiredTargets r)) os, r, ox, Set.union x (getExistsTargets x r)

        let mutable i = 0

        let step es =
            //log "%A" current
            i <- i + 1
            let before = current
            current <- es |> List.map update
            current = before || i > 100

        while not (step current) do
            ()
        //current |> List.iter (fun (e, s, u, r) -> log "event %s has %A and needs %A" (e.ID) s u)

        // let getSourceSetTargets (ids : string list) =
        //     let inner = (fun (x : string) -> current |> List.pick (fun (e2, s2, _, _) -> if e2.ID = x then Some (s2) else None))
        //     match ids with
        //     |[] -> Set.empty
        //     | xs -> xs |> List.map inner |> List.reduce (Set.intersect)
        let getSourceSetTargets (id: string) =
            let inner =
                (fun (x: string) ->
                    current
                    |> List.choose (fun ((e2id, e2), _, s2, _, r2, _, _) ->
                        if List.contains x r2 && e2id <> x then Some s2 else None))

            inner id

        let getSourceExistsTargets (id: string) =
            let inner =
                (fun (x: string) ->
                    current
                    |> List.choose (fun ((e2id, e2), _, _, _, r2, _, x2) ->
                        if List.contains x r2 && e2id <> x then Some x2 else None))

            inner id

        let downOptimistic ((eid, e): string * Node, os, s, u, r, ox, x) =
            (eid, e),
            os,
            Set.union
                os
                (getSourceSetTargets eid
                 |> (fun f ->
                     if List.isEmpty f then
                         Set.empty
                     else
                         List.reduce Set.union f)),
            u,
            r,
            ox,
            //x
            Set.union
                x
                (getSourceExistsTargets eid
                 |> (fun f ->
                     if List.isEmpty f then
                         Set.empty
                     else
                         List.reduce Set.union f))

        let mutable i = 0

        let step es =
            //log "%A" current
            i <- i + 1
            let before = current
            current <- es |> List.map downOptimistic
            current = before || i > 100

        while not (step current) do
            ()

        let downPessimistic ((eid, e): string * Node, os, s, u, r, ox, x) =
            (eid, e),
            os,
            Set.union
                os
                (getSourceSetTargets eid
                 |> (fun f ->
                     if List.isEmpty f then
                         Set.empty
                     else
                         List.reduce Set.intersect f)),
            u,
            r,
            ox,
            //x
            Set.union
                x
                (getSourceExistsTargets eid
                 |> (fun f ->
                     if List.isEmpty f then
                         Set.empty
                     else
                         List.reduce Set.intersect f))

        let mutable i = 0

        let step es =
            //log "%A" i
            i <- i + 1
            let before = current
            current <- es |> List.map downPessimistic
            current = before || i > 100

        while not (step current) do
            ()
        //current |> List.iter (fun (e, s, u, r) -> log "event %s has %A and needs %A" (e.ID) s u)
        // current |> List.iter (fun (e, s, u, r) -> log "event %s is missing %A" (e.ID) (Set.difference u s))
        // current |> List.iter (fun (e, os, s, u, r, ox, x) -> log "%s %A %A %A %A" e.ID s u r x;)

        let computeUnresolved (expected: Set<string>) (u: Set<string>) =
            let dynamicPrefixes = CWTools.Utilities.Utils2.PrefixOptimisedStringSet()
            expected |> Set.iter (fun (t: string) ->
                let parts = t.Split('@', 2)
                if parts.Length > 1 && parts.[0].Length > 0 then
                    dynamicPrefixes.Add(parts.[0])
            )
            u |> Set.filter (fun usedTarget ->
                if expected.Contains(usedTarget) then false
                else
                    let matched = dynamicPrefixes.LongestPrefixMatch(usedTarget.AsSpan())
                    String.IsNullOrEmpty(matched) || usedTarget.Length = matched.Length
            )

        let missing =
            current
            |> List.filter (fun (e, os, s, u, r, ox, x) ->
                let expected = Set.union (Set.union s x) globals
                not (computeUnresolved expected u |> Set.isEmpty))

        let maybeMissing =
            current
            |> List.filter (fun (e, os, s, u, r, ox, x) ->
                let expectedLocal = Set.union s globals
                let expectedGlobal = Set.union (Set.union s x) globals
                not (computeUnresolved expectedLocal u |> Set.isEmpty)
                && (computeUnresolved expectedGlobal u |> Set.isEmpty))

        let createError ((eid, e): string * Node, os, s, u, _, _, x) =
            let expected = Set.union (Set.union s x) globals
            let needed = computeUnresolved expected u |> Set.toList |> String.concat ", "
            Invalid(Guid.NewGuid(), [ inv (ErrorCodes.UnsavedEventTarget eid needed) e ])

        let createWarning ((eid, e): string * Node, os, s, u, _, _, _) =
            let expected = Set.union s globals
            let needed = computeUnresolved expected u |> Set.toList |> String.concat ", "
            Invalid(Guid.NewGuid(), [ inv (ErrorCodes.MaybeUnsavedEventTarget eid needed) e ])

        missing <&!&> createError <&&> (maybeMissing <&!&> createWarning)



    let getEventChains: LookupValidator<_> =
        fun lu os es ->
            let reffects = lu.effects
            // 过滤掉 inline_scripts 目录中的文件，因为这些模板文件包含未替换的参数（如 $CURRENT$）
            // 它们会在被调用者展开时进行参数替换，不应作为独立事件进行验证
            let events =
                es.GlobMatchChildren("**/events/*.txt")
                |> List.filter (fun e ->
                    let pos = e.Position
                    not (pos.FileName.Contains("inline_scripts")))
            let eids = events |> List.map (fun e -> e.TagText "id", e) |> Map.ofList

            let projects =
                os.GlobMatchChildren("**/common/special_projects/*.txt")
                @ es.GlobMatchChildren("**/common/special_projects/*.txt")

            let projectsWithTags = projects |> List.map (fun p -> p, p.TagText("key"))

            let eventIds =
                events |> List.map (fun f -> f.TagText "id")

            let chainIds =
                events
                |> List.collect (fun event ->
                    findAllReferencedEvents projectsWithTags event
                    |> List.map (fun f -> event.TagText "id", f))
                |> List.filter (fun (_, f) -> Map.containsKey f eids)
                //|> (fun f -> log "%A" f; f)
                |> List.collect (fun (s, t) -> [ s, t; t, s ])
                //|> (fun f -> log "%A" f; f)
                //|> (fun es -> (graph2AdjacencyGraph (eventIds, es)))
                |> (fun es -> (eventIds, es))
                |> connectedComponents
                //|> (fun f -> log "%A" f; f)

            let idsInChains =
                chainIds |> List.collect id |> Set.ofList

            let singletonChainIds =
                eventIds
                |> List.filter (fun eventId -> not (idsInChains.Contains eventId))
                |> List.map (fun eventId -> [ eventId ])

            let chains =
                (chainIds @ singletonChainIds)
                |> List.map (fun set -> set |> List.map (fun event -> eids.[event]))

            if chains |> List.isEmpty then
                OK
            else
                let seffects =
                    reffects
                    |> List.choose (function
                        | :? ScriptedEffect as e -> Some e
                        | _ -> None)

                let effects = os.AllEffects @ es.AllEffects

                let globalScriptedEffects =
                    seffects |> List.collect (fun se -> se.GlobalEventTargets) |> Set.ofList

                // Global targets are workspace-wide once saved anywhere; scan raw mod trees too,
                // not just EffectBlocks, so saves under scope guards (owner? = { ... }) aren't missed.
                let globalSaveSources =
                    effects
                    @ events
                    @ es.GlobMatchChildren("**/common/**/*.txt")

                let globalSavedTargets =
                    globalSaveSources
                    |> List.map findAllSavedGlobalEventTargets
                    |> List.fold Set.union Set.empty

                // Also collect ALL save_event_target_as from all effect blocks in the workspace.
                // This prevents false positives when targets are set in on_actions, decisions,
                // scripted effects, or events outside the current chain.
                let allSavedTargets =
                    effects
                    |> List.map findAllSavedEventTargets
                    |> List.fold Set.union Set.empty

                // Saves performed through parameterised scripted-effect calls anywhere
                // in the workspace (local and global), substituted with each call
                // site's arguments — e.g. `hire_effect = { GLOBAL_EVENT_TARGET = x }`
                // where the callee does `save_global_event_target_as = $GLOBAL_EVENT_TARGET$`.
                let effectsByName =
                    seffects |> List.map (fun se -> se.Name.lower, se) |> Map.ofList

                let substitutedCallSaves =
                    effects
                    |> List.map (findSubstitutedCallSaves effectsByName)
                    |> List.fold Set.union Set.empty

                let globals =
                    Set.union globalScriptedEffects globalSavedTargets
                    |> Set.union allSavedTargets
                    |> Set.union substitutedCallSaves

                let sinits =
                    os.GlobMatchChildren("**\\common\\solar_system_initializers\\**\\*.txt")
                    @ es.GlobMatchChildren("**\\common\\solar_system_initializers\\**\\*.txt")
                //log "%s" (globals |> Set.toList |> String.concat ", ")
                let filteredChains =
                    chains |> List.choose (fun c -> if c.Length > 500 then None else Some c)

                filteredChains <&!!&> checkEventChain seffects sinits projectsWithTags globals
