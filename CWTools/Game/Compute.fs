module CWTools.Games.Compute

open CWTools.Games
open System
open CWTools.Rules

let computeData (infoService: unit -> InfoService option) (e: Entity) =
    let withRulesData = infoService().IsSome

    let res =
        (if infoService().IsSome then
             Some(infoService().Value.BatchFolds(e))
         else
             None)

    let referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
        match res with
        | Some(r, d, (e, _), (t, _), et) -> (Some r, Some d, Some e, Some t, Some et)
        | None -> (None, None, None, None, None)

    let referencedtypes =
        referencedtypes
        |> Option.map (fun r ->
            r
            |> Seq.fold (fun acc kv -> acc |> (Map.add kv.Key (kv.Value |> List.ofSeq))) Map.empty)

    ComputedData(referencedtypes, definedvariable, withRulesData, effectBlocks, triggersBlocks, savedEventTargets)

let computeDataUpdate (infoService: unit -> InfoService option) (e: Entity) (data: ComputedData) =
    let withRulesData = infoService().IsSome

    let res =
        (if infoService().IsSome then
             Some(infoService().Value.BatchFolds(e))
         else
             None)

    let referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
        match res with
        | Some(r, d, (e, _), (t, _), et) -> (Some r, Some d, Some e, Some t, Some et)
        | None -> (None, None, None, None, None)

    let referencedtypes =
        referencedtypes
        |> Option.map (fun r ->
            r
            |> Seq.fold (fun acc kv -> acc |> (Map.add kv.Key (kv.Value |> List.ofSeq))) Map.empty)

    data.Referencedtypes <- referencedtypes
    data.Definedvariables <- definedvariable
    data.SavedEventTargets <- savedEventTargets
    data.EffectBlocks <- effectBlocks
    data.TriggerBlocks <- triggersBlocks
    data.WithRulesData <- withRulesData

let computeCK2Data = computeData
let computeCK2DataUpdate = computeDataUpdate
let computeHOI4Data = computeData
let computeHOI4DataUpdate = computeDataUpdate
let computeVIC2Data = computeData
let computeVIC2DataUpdate = computeDataUpdate

module EU4 =
    open CWTools.Process
    open CWTools.Process.ProcessCore

    let private parameterName (s: string) =
        let pipeIndex = s.IndexOf('|')
        if pipeIndex >= 0 then s.Substring(0, pipeIndex) else s

    let private bracketParameterName (s: string) =
        let text = s.TrimStart()

        if text.StartsWith("[[") then
            let inner = text.Substring(2).TrimStart()
            let inner =
                if inner.StartsWith("!") then inner.Substring(1).TrimStart()
                else inner

            let endIndex = inner.IndexOfAny([| ']'; ' '; '\t'; '\r'; '\n' |])
            let paramName =
                if endIndex >= 0 then inner.Substring(0, endIndex).Trim()
                else inner.Trim()

            if paramName.Length > 0 && (System.Char.IsLetterOrDigit(paramName.[0]) || paramName.[0] = '_') then
                Some paramName
            else
                None
        else
            None

    let getScriptedEffectParams (node: Node) =
        let getDollarText (s: string) acc =
            s.Split('$')
            |> Array.mapi (fun i s -> i, s)
            |> Array.fold (fun acc (i, s) ->
                if i % 2 = 1 then
                    parameterName s :: acc
                else acc) acc
        // 提取 [[PARAM] 和 [[!PARAM] 条件块中的参数名
        let getBracketText (s: string) acc =
            match bracketParameterName s with
            | Some paramName -> paramName :: acc
            | None -> acc
        let extractText (s: string) acc = getDollarText s (getBracketText s acc)
        let fNode =
            (fun (x: Node) acc ->
                let nodeRes =
                    let acc = extractText x.Key acc
                    let acc = x.KeyPrefix |> Option.map (fun prefix -> extractText prefix acc) |> Option.defaultValue acc
                    x.ValuePrefix |> Option.map (fun prefix -> extractText prefix acc) |> Option.defaultValue acc

                let leafRes =
                    x.Leaves
                    |> Seq.fold (fun a n -> extractText n.Key (extractText (n.Value.ToRawString()) a)) nodeRes

                x.LeafValues
                |> Seq.fold (fun a n -> extractText (n.ValueText) a) leafRes)

        node |> (foldNode7 fNode) |> List.ofSeq

    // 提取 script_values 中的参数（与 scripted_effect 相同逻辑）
    let getScriptValueParams (node: Node) =
        let getDollarText (s: string) acc =
            s.Split('$')
            |> Array.mapi (fun i s -> i, s)
            |> Array.fold (fun acc (i, s) ->
                if i % 2 = 1 then
                    parameterName s :: acc
                else acc) acc
        let getBracketText (s: string) acc =
            match bracketParameterName s with
            | Some paramName -> paramName :: acc
            | None -> acc
        let extractText (s: string) acc = getDollarText s (getBracketText s acc)
        let fNode =
            (fun (x: Node) acc ->
                let nodeRes =
                    let acc = extractText x.Key acc
                    let acc = x.KeyPrefix |> Option.map (fun prefix -> extractText prefix acc) |> Option.defaultValue acc
                    x.ValuePrefix |> Option.map (fun prefix -> extractText prefix acc) |> Option.defaultValue acc

                let leafRes =
                    x.Leaves
                    |> Seq.fold (fun a n -> extractText n.Key (extractText (n.Value.ToRawString()) a)) nodeRes

                x.LeafValues
                |> Seq.fold (fun a n -> extractText (n.ValueText) a) leafRes)

        node |> (foldNode7 fNode) |> List.ofSeq

    let getScriptedEffectParamsEntity (e: Entity) =
        if
            (e.logicalpath.StartsWith("common/scripted_effects", StringComparison.OrdinalIgnoreCase)
             || e.logicalpath.StartsWith("common/scripted_triggers", StringComparison.OrdinalIgnoreCase))
        then
            getScriptedEffectParams e.rawEntity
        else
            []

    let computeEU4Data (infoService: unit -> InfoService option) (e: Entity) =
        let withRulesData = infoService().IsSome

        let res =
            (if infoService().IsSome then
                 Some(infoService().Value.BatchFolds(e))
             else
                 None)

        let referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            match res with
            | Some(r, d, (e, _), (t, _), et) -> (Some r, Some d, Some e, Some t, Some et)
            | None -> (None, None, None, None, None)
        // let hastechs = getAllTechPrereqs e
        let scriptedeffectparams = Some(getScriptedEffectParamsEntity e)

        let referencedtypes =
            referencedtypes
            |> Option.map (fun r ->
                r
                |> Seq.fold (fun acc kv -> acc |> (Map.add kv.Key (kv.Value |> List.ofSeq))) Map.empty)

        EU4ComputedData(
            referencedtypes,
            definedvariable,
            scriptedeffectparams,
            withRulesData,
            effectBlocks,
            triggersBlocks,
            savedEventTargets
        )

    let computeEU4DataUpdate (infoService: unit -> InfoService option) (e: Entity) (data: EU4ComputedData) =
        let withRulesData = infoService().IsSome

        let res =
            (if infoService().IsSome then
                 Some(infoService().Value.BatchFolds(e))
             else
                 None)

        let referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            match res with
            | Some(r, d, (e, _), (t, _), et) -> (Some r, Some d, Some e, Some t, Some et)
            | None -> (None, None, None, None, None)

        let referencedtypes =
            referencedtypes
            |> Option.map (fun r ->
                r
                |> Seq.fold (fun acc kv -> acc |> (Map.add kv.Key (kv.Value |> List.ofSeq))) Map.empty)

        data.Referencedtypes <- referencedtypes
        data.Definedvariables <- definedvariable
        data.SavedEventTargets <- savedEventTargets
        data.EffectBlocks <- effectBlocks
        data.TriggerBlocks <- triggersBlocks
        data.WithRulesData <- withRulesData

module STL =
    open CWTools.Process
    open CWTools.Process.ProcessCore
    open CWTools.Utilities.Utils

    let getAllTechPrereqs (e: Entity) =
        let fNode =
            (fun (x: Node) acc ->
                match x with
                | _ -> acc)

        let nodes = e.entity.Children |> List.collect (foldNode7 fNode)

        let fNode =
            fun (t: Node) children ->
                let inner ls (l: Leaf) =
                    if l.Key == "has_technology" then
                        l.Value.ToRawString() :: ls
                    else
                        ls

                t.Leaves |> Seq.fold inner children

        (nodes |> List.collect (foldNode7 fNode))

    let computeSTLData (infoService: unit -> InfoService option) (e: Entity) =
        // eprintfn "csd %s" e.logicalpath
        let withRulesData = infoService().IsSome

        // let eventIds = if e.entityType = EntityType.Events then e.entity.Children |> List.choose (function | :? Event as e -> Some e.ID |_ -> None) else []
        let res =
            (if infoService().IsSome then
                 Some(infoService().Value.BatchFolds(e))
             else
                 None)

        let referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            match res with
            | Some(r, d, (e, _), (t, _), et) -> (Some r, Some d, Some e, Some t, Some et)
            | None -> (None, None, None, None, None)
        // let referencedtypes = (if infoService().IsSome then Some ((infoService().Value.GetReferencedTypes )(e)) else None)
        // let definedvariable = (if infoService().IsSome then Some ((infoService().Value.GetDefinedVariables )(e)) else None)
        // let effectBlocks, triggersBlocks = (if infoService().IsSome then let (e, t) = ((infoService().Value.GetEffectBlocks )(e)) in Some e, Some t else None, None)
        let scriptedeffectparams = Some(EU4.getScriptedEffectParamsEntity e)

        let referencedtypes =
            referencedtypes
            |> Option.map (fun r ->
                r
                |> List.ofSeq
                |> List.fold (fun acc kv -> acc |> (Map.add kv.Key kv.Value)) Map.empty)

        let referencedtypes =
            referencedtypes
            |> Option.map (fun r -> r |> Map.map (fun _ v -> (v |> List.ofSeq)))

        STLComputedData(
            referencedtypes,
            definedvariable,
            scriptedeffectparams,
            withRulesData,
            effectBlocks,
            triggersBlocks,
            savedEventTargets
        )

    let computeSTLDataUpdate (infoService: unit -> InfoService option) (e: Entity) (data: STLComputedData) =
        let withRulesData = infoService().IsSome

        let res =
            (if infoService().IsSome then
                 Some(infoService().Value.BatchFolds(e))
             else
                 None)

        let referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            match res with
            | Some(r, d, (e, _), (t, _), et) -> (Some r, Some d, Some e, Some t, Some et)
            | None -> (None, None, None, None, None)

        let referencedtypes =
            referencedtypes
            |> Option.map (fun r ->
                r
                |> Seq.fold (fun acc kv -> acc |> (Map.add kv.Key (kv.Value |> List.ofSeq))) Map.empty)

        data.Referencedtypes <- referencedtypes
        data.Definedvariables <- definedvariable
        data.SavedEventTargets <- savedEventTargets
        // let effectBlocks, triggersBlocks = (if infoService().IsSome then let (e, t) = ((infoService().Value.GetEffectBlocks )(e)) in Some e, Some t else None, None)
        data.EffectBlocks <- effectBlocks
        data.TriggerBlocks <- triggersBlocks
        data.WithRulesData <- withRulesData

module Jomini =
    open CWTools.Process
    open CWTools.Process.ProcessCore

    let private parameterName (s: string) =
        let pipeIndex = s.IndexOf('|')
        if pipeIndex >= 0 then s.Substring(0, pipeIndex) else s

    let private bracketParameterName (s: string) =
        let text = s.TrimStart()

        if text.StartsWith("[[") then
            let inner = text.Substring(2).TrimStart()
            let inner =
                if inner.StartsWith("!") then inner.Substring(1).TrimStart()
                else inner

            let endIndex = inner.IndexOfAny([| ']'; ' '; '\t'; '\r'; '\n' |])
            let paramName =
                if endIndex >= 0 then inner.Substring(0, endIndex).Trim()
                else inner.Trim()

            if paramName.Length > 0 && (System.Char.IsLetterOrDigit(paramName.[0]) || paramName.[0] = '_') then
                Some paramName
            else
                None
        else
            None

    let getScriptedEffectParams (node: Node) =
        let getDollarText (s: string) acc =
            s.Split('$')
            |> Array.mapi (fun i s -> i, s)
            |> Array.fold (fun acc (i, s) ->
                if i % 2 = 1 then
                    parameterName s :: acc
                else acc) acc
        // 提取 [[PARAM] 和 [[!PARAM] 条件块中的参数名
        let getBracketText (s: string) acc =
            match bracketParameterName s with
            | Some paramName -> paramName :: acc
            | None -> acc
        let extractText (s: string) acc = getDollarText s (getBracketText s acc)
        let fNode =
            (fun (x: Node) acc ->
                let nodeRes =
                    let acc = extractText x.Key acc
                    let acc = x.KeyPrefix |> Option.map (fun prefix -> extractText prefix acc) |> Option.defaultValue acc
                    x.ValuePrefix |> Option.map (fun prefix -> extractText prefix acc) |> Option.defaultValue acc

                let leafRes =
                    x.Leaves
                    |> Seq.fold (fun a n -> extractText n.Key (extractText (n.Value.ToRawString()) a)) nodeRes

                x.LeafValues
                |> Seq.fold (fun a n -> extractText (n.ValueText) a) leafRes)

        node |> (foldNode7 fNode) |> List.ofSeq

    // 提取 script_values 中的参数（与 scripted_effect 相同逻辑）
    let getScriptValueParams (node: Node) =
        let getDollarText (s: string) acc =
            s.Split('$')
            |> Array.mapi (fun i s -> i, s)
            |> Array.fold (fun acc (i, s) ->
                if i % 2 = 1 then
                    parameterName s :: acc
                else acc) acc
        let getBracketText (s: string) acc =
            match bracketParameterName s with
            | Some paramName -> paramName :: acc
            | None -> acc
        let extractText (s: string) acc = getDollarText s (getBracketText s acc)
        let fNode =
            (fun (x: Node) acc ->
                let nodeRes =
                    let acc = extractText x.Key acc
                    let acc = x.KeyPrefix |> Option.map (fun prefix -> extractText prefix acc) |> Option.defaultValue acc
                    x.ValuePrefix |> Option.map (fun prefix -> extractText prefix acc) |> Option.defaultValue acc

                let leafRes =
                    x.Leaves
                    |> Seq.fold (fun a n -> extractText n.Key (extractText (n.Value.ToRawString()) a)) nodeRes

                x.LeafValues
                |> Seq.fold (fun a n -> extractText (n.ValueText) a) leafRes)

        node |> (foldNode7 fNode) |> List.ofSeq

    let getScriptedEffectParamsEntity (e: Entity) =
        if
            (e.logicalpath.StartsWith("common/scripted_effects", StringComparison.OrdinalIgnoreCase)
             || e.logicalpath.StartsWith("common/scripted_triggers", StringComparison.OrdinalIgnoreCase))
        then
            getScriptedEffectParams e.rawEntity
        else
            []

    let getScriptValueParamsEntity (e: Entity) =
        if
            (e.logicalpath.StartsWith("common/script_values", StringComparison.OrdinalIgnoreCase))
        then
            getScriptValueParams e.rawEntity
        else
            []

    let computeJominiData (infoService: unit -> InfoService option) (e: Entity) =
        let withRulesData = infoService().IsSome

        let res =
            (if infoService().IsSome then
                 Some(infoService().Value.BatchFolds(e))
             else
                 None)

        let referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            match res with
            | Some(r, d, (e, _), (t, _), et) -> (Some r, Some d, Some e, Some t, Some et)
            | None -> (None, None, None, None, None)
        // let hastechs = getAllTechPrereqs e
        let scriptedeffectparams = Some(getScriptedEffectParamsEntity e)
        let scriptvalueparams = Some(getScriptValueParamsEntity e)

        let referencedtypes =
            referencedtypes
            |> Option.map (fun r ->
                r
                |> Seq.fold (fun acc kv -> acc |> (Map.add kv.Key (kv.Value |> List.ofSeq))) Map.empty)

        let computedData =
            JominiComputedData(
                referencedtypes,
                definedvariable,
                scriptedeffectparams,
                withRulesData,
                effectBlocks,
                triggersBlocks,
                savedEventTargets
            )
        
        computedData.ScriptValueParams <- scriptvalueparams
        computedData

    let computeJominiDataUpdate (infoService: unit -> InfoService option) (e: Entity) (data: JominiComputedData) =
        let withRulesData = infoService().IsSome

        let res =
            (if infoService().IsSome then
                 Some(infoService().Value.BatchFolds(e))
             else
                 None)

        let referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            match res with
            | Some(r, d, (e, _), (t, _), et) -> (Some r, Some d, Some e, Some t, Some et)
            | None -> (None, None, None, None, None)

        let referencedtypes =
            referencedtypes
            |> Option.map (fun r ->
                r
                |> Seq.fold (fun acc kv -> acc |> (Map.add kv.Key (kv.Value |> List.ofSeq))) Map.empty)

        data.Referencedtypes <- referencedtypes
        data.Definedvariables <- definedvariable
        data.SavedEventTargets <- savedEventTargets
        data.EffectBlocks <- effectBlocks
        data.TriggerBlocks <- triggersBlocks
        data.WithRulesData <- withRulesData
        data.ScriptValueParams <- Some(getScriptValueParamsEntity e)
