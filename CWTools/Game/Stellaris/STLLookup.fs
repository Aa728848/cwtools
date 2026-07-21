namespace CWTools.Games.Stellaris

open System.Collections.Generic
open CWTools.Process
open CWTools.Games
open CWTools.Common
open CWTools.Utilities
open FSharp.Collections.ParallelSeq
open System

module STLLookup =
    let getChildrenWithComments (root: Node) =
        let firstCommentsByKey = Dictionary<string, string list>(StringComparer.Ordinal)
        let result = ResizeArray<Node * string list>()
        let mutable pendingComments = []

        for child in root.AllArray do
            match child with
            | CommentC comment -> pendingComments <- comment.Comment :: pendingComments
            | NodeC node ->
                let comments =
                    match firstCommentsByKey.TryGetValue node.Key with
                    | true, existing -> existing
                    | false, _ ->
                        firstCommentsByKey.Add(node.Key, pendingComments)
                        pendingComments

                result.Add(node, comments)
                pendingComments <- []
            | _ -> pendingComments <- []

        List.ofSeq result

    let private isExplicitCountComparison (node: Node) =
        node.Values
        |> Seq.exists (fun leaf ->
            leaf.Key.Equals("count", StringComparison.OrdinalIgnoreCase)
            || leaf.Key.Equals("value", StringComparison.OrdinalIgnoreCase)
            || leaf.Key.Equals("percentage", StringComparison.OrdinalIgnoreCase))

    let private isScriptedValueTrigger (node: Node) =
        let childNodes = node.Nodes |> Seq.toList
        let hasOnlyOneChild =
            childNodes.Length = 1
            && Seq.isEmpty node.Values
            && Seq.isEmpty node.LeafValues
            && Seq.isEmpty node.ValueClauses

        match childNodes with
        | [ child ] when hasOnlyOneChild ->
            not (isExplicitCountComparison child)
            && child.Key.StartsWith("count_", StringComparison.OrdinalIgnoreCase)
        | _ -> false

    let updateScriptedTriggers (resources: IResourceAPI<STLComputedData>) (vanillaTriggers: Effect list) =
        let rawTriggers =
            resources.AllEntities()
            |> Seq.choose (function
                | struct (f, _) when f.filepath.Contains("scripted_triggers") -> Some f.entity
                | _ -> None)
            |> Seq.collect getChildrenWithComments

        let scopedEffects =
            vanillaTriggers
            |> Seq.choose (function
                | :? ScopedEffect as e -> Some e
                | _ -> None)
            |> Seq.map (fun x -> (x.Name.lower, x.Scopes))
            |> Map.ofSeq

        let vanillaTriggerDictionary = Dictionary<StringToken, Scope list>()

        vanillaTriggers
        |> Seq.iter (fun x -> vanillaTriggerDictionary[x.Name.normal] <- x.Scopes)

        // let vanillaTriggerMap =
        // vanillaTriggers
        // |> Seq.map (fun e -> (e.Name.normal, e.ScopesSet))
        let mutable final: Effect list = List.empty
        let mutable i = 0
        let mutable first = true

        let ff () =
            i <- i + 1
            let before = final
            // let vanillaAndFinal = Seq.append vanillaTriggers final
            // |> Array.ofSeq
            let triggerAndEffectMap =
                final
                // Seq.append effectsInput triggersInput
                |> Seq.map (fun e -> (e.Name.normal, e.Scopes))
                |> Map.ofSeq

            // let mergedTriggers =
            final <-
                rawTriggers
                |> PSeq.map (fun t ->
                    let effectType =
                        if isScriptedValueTrigger (fst t) then
                            EffectType.ValueTrigger
                        else
                            EffectType.Trigger

                    (STLProcess.getScriptedTriggerScope
                        first
                        effectType
                        scopedEffects
                        vanillaTriggerDictionary
                        triggerAndEffectMap
                        t)
                    :> Effect)
                |> List.ofSeq

            first <- false
            before = final || i > 10

        while (not (ff ())) do
            ()

        final, vanillaTriggers

    let updateScriptedEffects
        (resources: IResourceAPI<STLComputedData>)
        (vanillaEffects: Effect list)
        (scriptedTriggers: Effect list)
        =
        let rawEffects =
            resources.AllEntities()
            |> Seq.choose (function
                | struct (f, _) when f.filepath.Contains("scripted_effects") -> Some f.entity
                | _ -> None)
            |> Seq.collect getChildrenWithComments
            |> List.ofSeq

        let scopedEffects =
            vanillaEffects
            |> Seq.choose (function
                | :? ScopedEffect as e -> Some e
                | _ -> None)
            |> Seq.map (fun x -> (x.Name.lower, x.Scopes))
            |> Map.ofSeq

        let vanillaBothDictionary = Dictionary<StringToken, Scope list>()

        Seq.append vanillaEffects scriptedTriggers
        |> Seq.iter (fun x -> vanillaBothDictionary[x.Name.normal] <- x.Scopes)
        // let vanillaBothMap =
        // |> Seq.map (fun e -> (e.Name.normal, e.ScopesSet))
        // |> Map.ofSeq
        let mutable final: Effect list = List.empty
        let mutable i = 0
        let mutable first = true

        let ff () =
            i <- i + 1
            let before = final
            // let vanillaAndFinal = Seq.append final
            // |> Array.ofSeq

            // let effectsInput = vanillaAndFinal
            // let triggersInput = scriptedTriggers

            let newFoundMap = final |> Seq.map (fun e -> (e.Name.normal, e.Scopes)) |> Map.ofSeq

            final <-
                rawEffects
                |> PSeq.map (fun e ->
                    (STLProcess.getScriptedTriggerScope
                        first
                        EffectType.Effect
                        scopedEffects
                        vanillaBothDictionary
                        newFoundMap
                        e)
                    :> Effect)
                |> List.ofSeq

            first <- false
            before = final || i > 10

        while (not (ff ())) do
            ()

        STLProcess.addNestedEventTargetsToEffects rawEffects final, vanillaEffects
