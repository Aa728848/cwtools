module CWTools.Rules.RulesMemoize

open System
open System.Collections.Generic
open System.Collections.Frozen
open CWTools.Utilities.Utils
open CWTools.Process
open CWTools.Rules.RulesWrapper
open CWTools.Utilities
open CWTools.Utilities.Utils2
open CWTools.Utilities.StringResource

/// Shared memoized rules decomposition used by RuleValidationService and
/// InfoService. The only per-service difference is how SubtypeRule entries are
/// filtered by the active subtypes; callers supply that via subtypedRulesOf.
let memoizeRulesWith
    (rootRules: RulesWrapper)
    (subtypedRulesOf: NewRule array -> string list -> NewRule array)
    =
    let monitor = new Object()

    let memoizeRulesInner memFunction =
        let dict =
            new System.Collections.Concurrent.ConcurrentDictionary<_, Dictionary<_, _>>()

        fun (rules: NewRule array) (subtypes: string list) ->
            match dict.TryGetValue(rules) with
            | true, v ->
                match v.TryGetValue(subtypes) with
                | true, v2 -> v2
                | _ ->
                    let temp = memFunction rules subtypes

                    lock monitor (fun () ->
                        if v.ContainsKey(subtypes) then
                            ()
                        else
                            v.Add(subtypes, temp))

                    temp
            | _ ->
                let temp = memFunction rules subtypes
                let innerDict = new Dictionary<_, _>()

                lock monitor (fun () ->
                    innerDict.Add(subtypes, temp)

                    match dict.TryGetValue(rules) with
                    | true, v2 -> ()
                    | _ -> dict.TryAdd(rules, innerDict) |> ignore)

                temp

    let memFunction =
        fun rules subtypes ->
            let subtypedrules = subtypedRulesOf rules subtypes

            let expandedbaserules =
                rules
                |> Array.collect (function
                    | LeafRule(AliasField a, _), _ -> (rootRules.Aliases.TryFind a |> Option.defaultValue [||])
                    | NodeRule(AliasField a, _), _ -> (rootRules.Aliases.TryFind a |> Option.defaultValue [||])
                    | x -> [||])

            let expandedsubtypedrules =
                subtypedrules
                |> Array.collect (function
                    | LeafRule(AliasField a, _), _ -> (rootRules.Aliases.TryFind a |> Option.defaultValue [||])
                    | NodeRule(AliasField a, _), _ -> (rootRules.Aliases.TryFind a |> Option.defaultValue [||])
                    | x -> [||])
            let noderules = new ResizeArray<_>()
            let leafrules = new ResizeArray<_>()
            let leafvaluerules = new ResizeArray<_>()
            let valueclauserules = new ResizeArray<_>()
            let nodeSpecificMap = new Dictionary<_, _>()
            let leafSpecificMap = new Dictionary<_, _>()

            let inner =
                (fun r ->
                    match r with
                    | NodeRule(SpecificField(SpecificValue v), rs), o as x ->
                        let found, res = nodeSpecificMap.TryGetValue(v.lower)

                        if found then
                            nodeSpecificMap.[v.lower] <- x :: res
                        else
                            nodeSpecificMap.[v.lower] <- [ x ]
                    | NodeRule(l, rs), o as x -> noderules.Add(x)
                    | LeafRule(SpecificField(SpecificValue v), r), o as x ->
                        let found, res = leafSpecificMap.TryGetValue(v.lower)

                        if found then
                            leafSpecificMap.[v.lower] <- x :: res
                        else
                            leafSpecificMap.[v.lower] <- [ x ]
                    | LeafRule(l, r), o as x -> leafrules.Add(x)
                    | LeafValueRule lv, o as x -> leafvaluerules.Add(x)
                    | ValueClauseRule rs, o as x -> valueclauserules.Add(x)
                    | _ -> ())
            expandedsubtypedrules |> Seq.iter inner
            subtypedrules |> Seq.iter inner
            rules |> Seq.iter inner
            expandedbaserules |> Seq.iter inner
            noderules, leafrules, leafvaluerules, valueclauserules, nodeSpecificMap, leafSpecificMap

    memoizeRulesInner memFunction
/// Completion values for a rule; shared by RuleValidationService, InfoService,
/// CompletionService and computeAliasKeyMap (previously four identical copies).
let ruleToCompletionListHelper
    (types: FrozenDictionary<string, PrefixOptimisedStringSet>)
    (enums: FrozenDictionary<string, string * PrefixOptimisedStringSet>)
    =
    function
    | LeafRule(SpecificField(SpecificValue x), _), _ -> seq { yield x.lower }
    | NodeRule(SpecificField(SpecificValue x), _), _ -> seq { yield x.lower }
    | LeafRule(NewField.TypeField(TypeType.Simple t), _), _
    | NodeRule(NewField.TypeField(TypeType.Simple t), _), _ ->
        match types.TryGetValue t with
        | true, s -> s.IdValues |> Seq.map _.lower
        | _ -> Seq.empty
    | LeafRule(NewField.TypeField(TypeType.Complex(p, t, suff)), _), _
    | NodeRule(NewField.TypeField(TypeType.Complex(p, t, suff)), _), _ ->
        match types.TryGetValue t with
        | true, s ->
            s.IdValues
            |> Seq.map (fun i ->
                let s = StringResource.stringManager.GetStringForID i.normal
                StringResource.stringManager.InternIdentifierToken(p + s + suff).lower)
        | _ -> Seq.empty
    | LeafRule(NewField.ValueField(Enum e), _), _
    | NodeRule(NewField.ValueField(Enum e), _), _ ->
        match enums.TryGetValue e with
        | true, (_, s) -> s.IdValues |> Seq.map _.lower
        | _ -> Seq.empty
    | _ -> Seq.empty
