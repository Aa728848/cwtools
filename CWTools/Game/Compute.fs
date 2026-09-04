module CWTools.Games.Compute

open CWTools.Games
open System
open CWTools.Process
open CWTools.Process.ProcessCore
open CWTools.Rules
open CWTools.Utilities.Utils

let computeCoreEntityData (infoService: unit -> InfoService option) (e: Entity) =
    let withRulesData = infoService().IsSome

    let res =
        if infoService().IsSome then
            Some(infoService().Value.BatchFolds(e))
        else
            None

    let referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
        match res with
        | Some(r, d, (e, _), (t, _), et) -> (Some r, Some d, Some e, Some t, Some et)
        | None -> (None, None, None, None, None)

    let referencedtypes =
        referencedtypes
        |> Option.map (fun r ->
            r
            |> Seq.fold (fun acc kv -> acc |> (Map.add kv.Key (kv.Value |> List.ofSeq))) Map.empty)

    (withRulesData, referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets)

let extractNodeParameters (node: Node) : string list =
    let getDollarText (s: string) acc =
        s.Split('$')
        |> Array.mapi (fun i s -> i, s)
        |> Array.fold (fun acc (i, s) ->
            if i % 2 = 1 then
                parameterName s :: acc
            else acc) acc
    // 提取 [[PARAM] 和 [[!PARAM] 条件块中的参数名（扫描字符串中所有 [[ 出现位置）
    let getBracketText (s: string) acc =
        let mutable acc = acc
        let mutable idx = s.IndexOf("[[")
        while idx >= 0 do
            match bracketParameterNameOnly (s.Substring(idx)) with
            | Some paramName -> acc <- paramName :: acc
            | None -> ()
            idx <- s.IndexOf("[[", idx + 2)
        acc
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

let extractEntityParameters (prefixes: string list) (extractParams: Node -> string list) (e: Entity) =
    if prefixes |> List.exists (fun prefix -> e.logicalpath.StartsWith(prefix, StringComparison.OrdinalIgnoreCase)) then
        let fromRaw = extractParams e.rawEntity
        if System.Object.ReferenceEquals(e.entity, e.rawEntity) then
            fromRaw
        else
            fromRaw @ extractParams e.entity |> List.distinct
    else
        []

let computeData (infoService: unit -> InfoService option) (e: Entity) =
    let withRulesData, referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
        computeCoreEntityData infoService e
    ComputedData(referencedtypes, definedvariable, withRulesData, effectBlocks, triggersBlocks, savedEventTargets)

let computeDataUpdate (infoService: unit -> InfoService option) (e: Entity) (data: ComputedData) =
    let withRulesData, referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
        computeCoreEntityData infoService e
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
    let getScriptedEffectParams = extractNodeParameters
    let getScriptValueParams = extractNodeParameters
    let getScriptedEffectParamsEntity =
        extractEntityParameters [ "common/scripted_effects"; "common/scripted_triggers" ] extractNodeParameters

    let computeEU4Data (infoService: unit -> InfoService option) (e: Entity) =
        let withRulesData, referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            computeCoreEntityData infoService e
        let scriptedeffectparams = Some(getScriptedEffectParamsEntity e)

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
        let withRulesData, referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            computeCoreEntityData infoService e
        data.Referencedtypes <- referencedtypes
        data.Definedvariables <- definedvariable
        data.SavedEventTargets <- savedEventTargets
        data.EffectBlocks <- effectBlocks
        data.TriggerBlocks <- triggersBlocks
        data.WithRulesData <- withRulesData
        data.ScriptedEffectParams <- Some(getScriptedEffectParamsEntity e)

module STL =
    let computeSTLData (infoService: unit -> InfoService option) (e: Entity) =
        let withRulesData, referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            computeCoreEntityData infoService e
        let scriptedeffectparams = Some(EU4.getScriptedEffectParamsEntity e)

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
        let withRulesData, referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            computeCoreEntityData infoService e
        data.Referencedtypes <- referencedtypes
        data.Definedvariables <- definedvariable
        data.SavedEventTargets <- savedEventTargets
        data.EffectBlocks <- effectBlocks
        data.TriggerBlocks <- triggersBlocks
        data.WithRulesData <- withRulesData
        data.ScriptedEffectParams <- Some(EU4.getScriptedEffectParamsEntity e)

module Jomini =
    let getScriptedEffectParams = extractNodeParameters
    let getScriptValueParams = extractNodeParameters
    let getScriptedEffectParamsEntity =
        extractEntityParameters [ "common/scripted_effects"; "common/scripted_triggers" ] extractNodeParameters
    let getScriptValueParamsEntity =
        extractEntityParameters [ "common/script_values" ] extractNodeParameters

    let computeJominiData (infoService: unit -> InfoService option) (e: Entity) =
        let withRulesData, referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            computeCoreEntityData infoService e
        let scriptedeffectparams = Some(getScriptedEffectParamsEntity e)
        let scriptvalueparams = Some(getScriptValueParamsEntity e)

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
        let withRulesData, referencedtypes, definedvariable, effectBlocks, triggersBlocks, savedEventTargets =
            computeCoreEntityData infoService e
        data.Referencedtypes <- referencedtypes
        data.Definedvariables <- definedvariable
        data.SavedEventTargets <- savedEventTargets
        data.EffectBlocks <- effectBlocks
        data.TriggerBlocks <- triggersBlocks
        data.WithRulesData <- withRulesData
        data.ScriptedEffectParams <- Some(getScriptedEffectParamsEntity e)
        data.ScriptValueParams <- Some(getScriptValueParamsEntity e)
