namespace CWTools.Rules

open System.Collections.Generic
open System.IO
open CSharpHelpers
open CWTools.Common
open CWTools.Rules.RulesWrapper
open CWTools.Utilities.Utils2
open CWTools.Utilities.Utils
open CWTools.Process.Localisation
open CWTools.Process
open CWTools.Process.Scopes
open CWTools.Process.ProcessCore
open CWTools.Utilities
open System
open CWTools.Games
open CWTools.Utilities.Position
open CWTools.Utilities.StringResource
open System.Collections.Frozen
open System.Linq

type CompletionContext =
    | NodeLHS
    | NodeRHS
    | LeafLHS
    | LeafRHS
    | LeafValueRHS


type private CompletionScopeOutput =
    | Variable
    | Value
    | Scope of scope: Scope
    | Nothing

type private CompletionScopeExpectation =
    | VariableOrValue
    | Scopes of scopes: Scope list
    | Nothing

type private CompletionLinkItem =
    { key: string
      requiredScopes: Scope list
      outputScope: CompletionScopeOutput
      desc: string option
      kind: CompletionCategory }

/// Materialized type id lists keyed by trie instance. Incremental commits reuse unchanged
/// tries, so cached lists survive service rebuilds and only changed types re-materialize —
/// keeping the first completion after a save off the slow path. Weak table: entries die
/// with their tries.
module private CompletionValueListCache =
    open System.Runtime.CompilerServices

    let private listsByTrie =
        ConditionalWeakTable<PrefixOptimisedStringSet, string list>()

    let private factory =
        ConditionalWeakTable<PrefixOptimisedStringSet, string list>.CreateValueCallback(fun set ->
            set.StringValues |> List.ofSeq)

    let getOrAdd (set: PrefixOptimisedStringSet) : string list = listsByTrie.GetValue(set, factory)


type CompletionService
    (
        rootRules: RulesWrapper,
        typedefs: TypeDefinition list,
        types: FrozenDictionary<string, PrefixOptimisedStringSet>,
        enums: FrozenDictionary<string, string * PrefixOptimisedStringSet>,
        varMap: FrozenDictionary<string, PrefixOptimisedStringSet>,
        localisation: (Lang * Collections.Set<string>) array,
        files: FrozenSet<string>,
        links: EffectMap,
        valueTriggers: EffectMap,
        globalScriptVariables: string list,
        changeScope: ChangeScope,
        defaultContext: ScopeContext,
        anyScope,
        oneToOneScopes,
        defaultLang,
        dataTypes: CWTools.Parser.DataTypeParser.JominiLocDataTypes,
        processLocalisation:
            Lang * Collections.Map<string, CWTools.Localisation.Entry> -> Lang * Collections.Map<string, LocEntry>,
        validateLocalisation: LocEntry -> ScopeContext -> CWTools.Validation.ValidationResult,
        ?extendedConfigMetadata: ExtendedConfigMetadata,
        ?aliasKeyMapOverride: Map<string, HashSet<StringToken>>
    ) =

    let extendedConfigMetadata = defaultArg extendedConfigMetadata ExtendedConfigMetadata.empty

    let typesMap = types //|> Map.toSeq |> PSeq.map (fun (k, s) -> k, StringSet.Create(InsensitiveStringComparer(), (s |> List.map fst))) |> Map.ofSeq

    //let typesMap = types |> (Map.map (fun _ s -> StringSet.Create(InsensitiveStringComparer(), (s |> List.map fst))))
    let enumsMap = enums // |> Map.toSeq |> PSeq.map (fun (k, s) -> k, StringSet.Create(InsensitiveStringComparer(), s)) |> Map.ofSeq

    // Materialize a type's id list on first use instead of copying every type's values at
    // construction time; the shared trie-keyed cache keeps unchanged types' lists warm
    // across the per-save service rebuilds.
    let tryFindTypeValueList (t: string) : string list option =
        match typesMap.TryFind t with
        | Some set -> Some(CompletionValueListCache.getOrAdd set)
        | None -> None

    let defaultKeys =
        localisation
        |> Array.choose (fun (l, ks) -> if l = defaultLang then Some ks else None)
        |> Array.tryHead
        |> Option.defaultValue Set.empty

    let localisationKeys =
        localisation
        |> Array.choose (fun (l, ks) -> if l = defaultLang then None else Some(l, ks))

    let ruleToCompletionListHelper =
        function
        | LeafRule(SpecificField(SpecificValue x), _), _ -> seq { yield x.lower }
        | NodeRule(SpecificField(SpecificValue x), _), _ -> seq { yield x.lower }
        | LeafRule(NewField.TypeField(TypeType.Simple t), _), _
        | NodeRule(NewField.TypeField(TypeType.Simple t), _), _ ->
            typesMap.TryFind(t)
            |> Option.map (fun s -> s.IdValues |> Seq.map _.lower)
            |> Option.defaultValue (Seq.empty)
        | LeafRule(NewField.TypeField(TypeType.Complex(p, t, suff)), _), _
        | NodeRule(NewField.TypeField(TypeType.Complex(p, t, suff)), _), _ ->
            typesMap.TryFind(t)
            |> Option.map (fun s ->
                s.IdValues
                |> Seq.map (fun i ->
                    let s = stringManager.GetStringForID i.normal
                    stringManager.InternIdentifierToken(p + s + suff).lower))
            |> Option.defaultValue Seq.empty
        | LeafRule(NewField.ValueField(Enum e), _), _
        | NodeRule(NewField.ValueField(Enum e), _), _ ->
            enums.TryFind(e)
            |> Option.map (fun (_, s) -> s.IdValues |> Seq.map _.lower)
            |> Option.defaultValue Seq.empty
        | _ -> Seq.empty



    let aliasKeyMap =
        match aliasKeyMapOverride with
        | Some precomputed -> precomputed
        | None ->
            rootRules.Aliases
            |> Map.toList
            |> List.map (fun (key, rules) -> key, (rules |> Seq.collect ruleToCompletionListHelper |> HashSet<StringToken>))
            |> Map.ofList

    let aliasParamMarkers =
        let rec collectRule ((ruleType, _): NewRule) =
            seq {
                match ruleType with
                | LeafValueRule(AliasParamsField(aliasName, selectorField)) -> yield aliasName, selectorField
                | LeafRule(AliasParamsField(aliasName, selectorField), _)
                | LeafRule(_, AliasParamsField(aliasName, selectorField))
                | NodeRule(AliasParamsField(aliasName, selectorField), _) ->
                    yield aliasName, selectorField
                | NodeRule(_, rules)
                | ValueClauseRule rules
                | SubtypeRule(_, _, rules) ->
                    yield! rules |> Seq.collect collectRule
                | _ -> ()
            }

        seq {
            for _, rules in rootRules.Aliases |> Map.toSeq do
                yield! rules |> Seq.collect collectRule

            for _, rule in rootRules.TypeRules do
                yield! collectRule rule
        }
        |> Seq.distinct
        |> Array.ofSeq

    let isAliasParameterComparisonValueRule ((ruleType, _): NewRule) =
        let isComparisonKey (key: StringTokens) =
            match stringManager.GetStringForID key.normal with
            | "percentage"
            | "amount"
            | "count"
            | "steps"
            | "value" -> true
            | _ -> false

        match ruleType with
        | LeafRule(SpecificField(SpecificValue key), _)
        | NodeRule(SpecificField(SpecificValue key), _) -> isComparisonKey key
        | _ -> false

    let trySelectedAliasRules aliasName selectedAlias =
        rootRules.Aliases.TryFind aliasName
        |> Option.bind (fun rules ->
            let selectedRules =
                rules
                |> Array.choose (function
                    | NodeRule(SpecificField(SpecificValue key), rules), _ when
                        String.Equals(stringManager.GetStringForID key.normal, selectedAlias, StringComparison.OrdinalIgnoreCase)
                        ->
                        Some rules
                    | _ -> None)
                |> Array.collect id
                |> Array.filter (isAliasParameterComparisonValueRule >> not)

            if selectedRules.Length = 0 then None else Some selectedRules)

    let linkMap = links

    let wildCardLinks =
        linkMap.Values
        |> Seq.choose (function
            | :? ScopedEffect as e when e.IsWildCard -> Some e
            | _ -> None)
        |> Seq.toList

    let valueTriggerMap = valueTriggers

    let varSet =
        varMap.TryFind "variable" |> Option.defaultValue (PrefixOptimisedStringSet())

    // Cached result of getAllKeysInFile to avoid repeated full-AST traversals.
    // The cache is keyed by reference identity of the root Node object.
    let mutable cachedAllKeysRoot: Node = Unchecked.defaultof<Node>
    let mutable cachedAllKeysResult: string list = []

    let getAllKeysInFile (root: Node) =
        if Object.ReferenceEquals(root, cachedAllKeysRoot) then
            cachedAllKeysResult
        else
            let fNode =
                (fun (x: Node) acc ->
                    let withValues =
                        x.Leaves |> Seq.fold (fun a leaf -> leaf.Key :: leaf.ValueText :: a) acc

                    let withBoth =
                        x.LeafValues
                        |> Seq.fold (fun a leafvalue -> leafvalue.ValueText :: a) withValues

                    x.Key :: withBoth)

            let result = foldNode7 fNode root
            cachedAllKeysRoot <- root
            cachedAllKeysResult <- result
            result

    let fieldToCompletionList (field: NewField) =
        match field with
        | ValueField(Enum e) ->
            enums.TryFind(e)
            |> Option.bind (fun (_, s) ->
                if s.IdCount = 0 then
                    None
                else
                    Some(s.StringValues |> Seq.head))
            |> Option.defaultValue "x"
        | ValueField v ->
            FieldValidators.getValidValues v
            |> Option.bind Array.tryHead
            |> Option.defaultValue "x"
        | TypeField(TypeType.Simple t) -> tryFindTypeValueList t |> Option.bind List.tryHead |> Option.defaultValue "x"
        | TypeField(TypeType.Complex(p, t, s)) ->
            tryFindTypeValueList t
            |> Option.bind List.tryHead
            |> Option.map (fun n -> p + n + s)
            |> Option.defaultValue "x"
        | FilenameField _ -> files |> Seq.tryHead |> Option.map Path.GetFileName |> Option.defaultValue "x"
        | AbsoluteFilepathField -> "C:/path/to/file"
        | ScopeField _ -> "THIS"
        | _ -> "x"
    //TODO: Expand

    let checkIconField (folder: string) =
        files
        |> Seq.filter _.StartsWith(folder, StringComparison.OrdinalIgnoreCase)
        |> Seq.map _.Replace(".dds", "")
        |> Seq.toArray

    let promotes = dataTypes.promotes.Keys |> Seq.toArray
    let functions = dataTypes.functions.Keys |> Seq.toArray

    let dataTypeFunctions =
        dataTypes.dataTypes.Values |> Seq.collect _.Keys |> Seq.toArray

    let allPossibles = Array.concat [| promotes; functions; dataTypeFunctions |]

    let locCompleteInner (textBeforeCursor: string) =
        if textBeforeCursor.LastIndexOf '[' > textBeforeCursor.LastIndexOf ']' then
            (allPossibles |> Array.map CompletionResponse.CreateSimple)
        else
            [||]

    let locComplete (pos: pos) (filetext: string) =
        let split = filetext.Split('\n')
        let targetLine = split.[pos.Line - 1]
        let textBeforeCursor = targetLine.Remove pos.Column
        locCompleteInner textBeforeCursor
    //// Normal complete
    ///
    ///

    let valueFieldAll, valueFieldNonGlobal, scopeFieldAll, scopeFieldNonGlobal, variableFieldAll, variableFieldNonGlobal =
        let evs =
            varMap.TryFind "event_target"
            |> Option.map (fun l -> l.StringValues |> List.ofSeq)
            |> Option.defaultValue []
            |> List.map (fun s ->
                { key = "event_target:" + s
                  requiredScopes = [ anyScope ]
                  outputScope = Scope anyScope
                  desc = None
                  kind = CompletionCategory.Global })

        let gevs =
            varMap.TryFind "global_event_target"
            |> Option.map (fun l -> l.StringValues |> List.ofSeq)
            |> Option.defaultValue []
            |> List.map (fun s ->
                { key = "event_target:" + s
                  requiredScopes = [ anyScope ]
                  outputScope = Scope anyScope
                  desc = None
                  kind = CompletionCategory.Global })

        let vars =
            varMap.TryFind "variable"
            |> Option.map (fun l -> l.StringValues |> List.ofSeq)
            |> Option.defaultValue []
            |> List.map (fun s ->
                { key = s
                  requiredScopes = [ anyScope ]
                  outputScope = CompletionScopeOutput.Variable
                  desc = None
                  kind = CompletionCategory.Variable })
        //        linkMap.ToList() |> List.iter (fun x -> log (sprintf "iop %A" x))
        let scopedEffectsExtra =
            [ "this"
              "root"
              "prev"
              "prevprev"
              "prevprevprev"
              "prevprevprevprev"
              "from"
              "fromfrom"
              "fromfromfrom"
              "fromfromfromfrom" ]
            |> List.map (fun s ->
                { key = s
                  requiredScopes = [ anyScope ]
                  outputScope = Scope anyScope
                  desc = None
                  kind = CompletionCategory.Link })

        let scopedEffects =
            linkMap.Values
            |> Seq.choose (fun s ->
                s
                |> function
                    | :? ScopedEffect as x when x.Type = EffectType.Link && x.Target.IsSome ->
                        Some
                            { key = x.Name.GetString()
                              requiredScopes = x.Scopes
                              outputScope = Scope x.Target.Value
                              desc = Some x.Desc
                              kind = CompletionCategory.Link }
                    | :? ScopedEffect as x when x.Type = EffectType.Link && x.Target.IsNone ->
                        Some
                            { key = x.Name.GetString()
                              requiredScopes = x.Scopes
                              outputScope = CompletionScopeOutput.Nothing
                              desc = Some x.Desc
                              kind = CompletionCategory.Link }
                    | _ -> None)
            |> Seq.toList

        let valueTriggers =
            valueTriggerMap.Values
            |> Seq.choose (fun s ->
                s
                |> function
                    | :? DocEffect as x when x.Type = EffectType.ValueTrigger ->
                        Some
                            { key = x.Name.GetString()
                              requiredScopes = x.Scopes
                              outputScope = CompletionScopeOutput.Value
                              desc = Some x.Desc
                              kind = CompletionCategory.Value }
                    | _ -> None)
            |> Seq.toList
        //        let scopedEffects = scopedEffects @ valueTriggers
        let scopedEffects = scopedEffects @ scopedEffectsExtra
        let valueFieldAll = evs @ gevs @ scopedEffects @ vars @ valueTriggers
        let valueFieldNonGlobal = scopedEffects @ vars @ valueTriggers
        let scopeFieldAll = evs @ gevs @ scopedEffects
        let scopeFieldNonGlobal = scopedEffects
        let variableFieldAll = evs @ gevs @ scopedEffects @ vars
        let variableFieldNonGlobal = scopedEffects @ vars
        valueFieldAll, valueFieldNonGlobal, scopeFieldAll, scopeFieldNonGlobal, variableFieldAll, variableFieldNonGlobal

    // The snippet body depends only on the rule set, not on the key being inserted;
    // enumerating a type with thousands of ids previously rebuilt the identical body per id.
    // Keyed by rule-array reference; rule arrays are stable for a service's lifetime.
    let snippetBodyCache =
        System.Collections.Concurrent.ConcurrentDictionary<NewRule array, string>(HashIdentity.Reference)

    let snippetBodyForRules (rules: NewRule array) =
        let build (rules: NewRule array) =
            let filterToCompletion =
                function
                | LeafRule(SpecificField(SpecificValue _), _) -> true
                | NodeRule(SpecificField(SpecificValue _), _) -> true
                | _ -> false

            let ruleToDistinctKey =
                function
                | LeafRule(SpecificField(SpecificValue s), _) -> StringResource.stringManager.GetStringForID s.normal
                | NodeRule(SpecificField(SpecificValue s), _) -> StringResource.stringManager.GetStringForID s.normal
                | _ -> ""

            let rulePrint (i: int) =
                function
                | LeafRule(SpecificField(SpecificValue s), r) ->
                    $"\t%s{StringResource.stringManager.GetStringForID s.normal} = ${{%i{i + 1}:%s{fieldToCompletionList r}}}\n"
                | NodeRule(SpecificField(SpecificValue s), _) ->
                    sprintf "\t%s = ${%i:%s}\n" (StringResource.stringManager.GetStringForID s.normal) (i + 1) "{ }"
                | _ -> ""

            let requiredRules =
                rules
                |> Seq.filter (fun (f, o) -> o.min >= 1 && filterToCompletion f)
                |> Seq.distinctBy (fun (f, _) -> ruleToDistinctKey f)
                |> Seq.mapi (fun i (f, _) -> rulePrint i f)
                |> String.concat ""

            if requiredRules = "" then "\t${0}\n" else requiredRules
        // Callers pass fresh [||] literals in a few places; keying those would grow the
        // cache by one dead entry per completion item.
        if rules.Length = 0 then
            "\t${0}\n"
        else
            snippetBodyCache.GetOrAdd(rules, build)

    let createSnippetForClause
        (scoreFunction: string -> int)
        (rules: NewRule array)
        (description: string option)
        (key: string)
        =
        let score = scoreFunction key

        CompletionResponse.Snippet(
            key,
            $"%s{key} = {{\n%s{snippetBodyForRules rules}}}",
            description,
            Some score,
            CompletionCategory.Other
        )


    // | LeafValue
    /// Binary search helper: find the element in a sorted-by-position array
    /// whose range contains the given position. Returns None if not found.
    let tryFindByPosBinary (pos: pos) (arr: 'a array) (getRange: 'a -> range) =
        if arr.Length = 0 then None
        else
            // Binary search: find the last element whose StartLine <= pos.Line
            let mutable lo = 0
            let mutable hi = arr.Length - 1
            let mutable result = -1
            while lo <= hi do
                let mid = lo + (hi - lo) / 2
                let r = getRange arr.[mid]
                if r.StartLine <= pos.Line then
                    result <- mid
                    lo <- mid + 1
                else
                    hi <- mid - 1
            // Check the candidate and its neighbors (to handle same-line elements)
            if result >= 0 then
                // Check result and a few neighbors to handle elements on the same line
                let startIdx = max 0 (result - 1)
                let endIdx = min (arr.Length - 1) (result + 1)
                let mutable found = None
                for i = startIdx to endIdx do
                    if found.IsNone then
                        let r = getRange arr.[i]
                        if rangeContainsPos r pos then
                            found <- Some arr.[i]
                found
            else None

    let rec getRulePath
        (pos: pos)
        (stack: (string * int * string option * CompletionContext * string option) list)
        (node: IClause)
        =
        let countChildren (n2: IClause) (key: string) =
            n2.Nodes |> Seq.sumBy (fun c -> if c.Key == key then 1 else 0)

        // Use array + binary search instead of Seq.tryFind for O(log n) lookup
        let nodesArr = node.AllArray
        let nodeChildren =
            nodesArr |> Array.choose (function | NodeC n -> Some n | _ -> None)
        match tryFindByPosBinary pos nodeChildren (fun c -> c.Position) with
        | Some c ->
            match
                (c.Position.StartLine = pos.Line)
                && ((c.Position.StartColumn + c.Key.Length + 1) > pos.Column)
            with
            | true -> getRulePath pos ((c.Key, countChildren node c.Key, None, NodeLHS, c.KeyPrefix) :: stack) c
            | false -> getRulePath pos ((c.Key, countChildren node c.Key, None, NodeRHS, c.KeyPrefix) :: stack) c
        | None ->
            let leafChildren =
                nodesArr |> Array.choose (function | LeafC l -> Some l | _ -> None)
            match tryFindByPosBinary pos leafChildren (fun l -> l.Position) with
            | Some l ->
                match l.Position.StartColumn + l.Key.Length + 1 > pos.Column with
                | true -> (l.Key, countChildren node l.Key, Some l.Key, LeafLHS, None) :: stack
                | false -> (l.Key, countChildren node l.Key, Some l.ValueText, LeafRHS, None) :: stack
            | None ->
                let leafValueChildren =
                    nodesArr |> Array.choose (function | LeafValueC lv -> Some lv | _ -> None)
                match tryFindByPosBinary pos leafValueChildren (fun lv -> lv.Position) with
                | Some lv -> (lv.Key, 0, Some lv.ValueText, LeafValueRHS, None) :: stack
                | None ->
                    let clauseChildren =
                        nodesArr |> Array.choose (function
                            | ValueClauseC vc -> Some (vc :> IClause)
                            | NodeC n -> Some (n :> IClause)
                            | _ -> None)
                    match tryFindByPosBinary pos clauseChildren (fun c -> c.Position) with
                    | Some vc ->
                        match
                            (vc.Position.StartLine = pos.Line)
                            && ((vc.Position.StartColumn + vc.Key.Length + 1) > pos.Column)
                        with
                        | true -> getRulePath pos ((vc.Key, countChildren node vc.Key, None, NodeLHS, None) :: stack) vc
                        | false -> getRulePath pos ((vc.Key, countChildren node vc.Key, None, NodeRHS, None) :: stack) vc
                    | None -> stack

    and getCompletionFromPath
        (scoreFunction: ScopeContext -> _ list -> CompletionScopeOutput -> CompletionScopeExpectation -> string -> int)
        (rules: NewRule array)
        (stack: (string * int * string option * CompletionContext * string option) list)
        scopeContext
        =
        // log (sprintf "%A" stack)

        let completionDotChainInner (key: string) (startingContext: ScopeContext) =
            if key.Contains('.') then
                let splitKey = key.Split('.')

                let changeScopeRes =
                    let substringBefore =
                        splitKey |> Array.takeWhile (fun x -> x.Contains magicCharString |> not)

                    match substringBefore.Length = 0 with
                    | true -> None
                    | false ->
                        substringBefore
                        |> String.concat "."
                        |> (fun next ->
                            changeScope.Invoke(
                                false,
                                true,
                                linkMap,
                                valueTriggerMap,
                                wildCardLinks,
                                varSet,
                                next,
                                startingContext
                            ))
                        |> Some
                changeScopeRes
            else
                None

        let inline convertScopeResToList
            startingContext
            (targetScopes: CompletionScopeExpectation)
            linkList
            terminalLinkList
            createSnippetFun
            (scopeRes: ScopeResult option)
            =

            let defaultRes =
                linkList
                |> List.map (fun x ->
                    createSnippetFun startingContext x.requiredScopes x.outputScope targetScopes x.key x.desc x.kind)

            let defaultResNonGlobal =
                terminalLinkList
                |> List.map (fun x ->
                    createSnippetFun startingContext x.requiredScopes x.outputScope targetScopes x.key x.desc x.kind)

            match scopeRes with
            | None -> defaultRes
            | Some(NewScope(newscope, _, _)) ->
                //                log (sprintf "%A %A" key newscope)
                // The magic char probably breaks any scope matches, so we'll never be on the first item here
                terminalLinkList
                |> List.map (fun x ->
                    createSnippetFun newscope x.requiredScopes x.outputScope targetScopes x.key x.desc x.kind)
            | Some(ValueFound _)
            | Some VarFound
            | Some(VarNotFound _)
            | Some(WrongScope _)
            | Some NotFound -> defaultResNonGlobal

        let completionForScopeDotChain
            (key: string)
            (startingContext: ScopeContext)
            innerRules
            (description: string option)
            (targetScopes: CompletionScopeExpectation)
            =
            let createSnippetForClauseWithCustomScopeReq scopeContext i o r key desc kind =
                createSnippetForClause (scoreFunction scopeContext i o r) innerRules description key

            completionDotChainInner key startingContext
            |> convertScopeResToList
                startingContext
                targetScopes
                scopeFieldAll
                scopeFieldNonGlobal
                createSnippetForClauseWithCustomScopeReq

        let completionForRHSScopeChain
            (key: string)
            (startingContext: ScopeContext)
            (targetScopes: CompletionScopeExpectation)
            =
            let createSnippetWithScore scopeContext =
                (fun i o r key desc kind -> Detailed(key, desc, Some(scoreFunction scopeContext i o r key), kind))

            completionDotChainInner key startingContext
            |> convertScopeResToList
                startingContext
                targetScopes
                scopeFieldAll
                scopeFieldNonGlobal
                createSnippetWithScore

        let completionForRHSValueChain (key: string) (startingContext: ScopeContext) =
            let createSnippetWithScore scopeContext =
                (fun i o r key desc kind -> Detailed(key, desc, Some(scoreFunction scopeContext i o r key), kind))

            completionDotChainInner key startingContext
            |> convertScopeResToList
                startingContext
                CompletionScopeExpectation.VariableOrValue
                valueFieldAll
                valueFieldNonGlobal
                createSnippetWithScore

        let completionForRHSVariableChain (key: string) (startingContext: ScopeContext) =
            let createSnippetWithScore scopeContext =
                (fun i o r key desc kind -> Detailed(key, desc, Some(scoreFunction scopeContext i o r key), kind))

            completionDotChainInner key startingContext
            |> convertScopeResToList
                startingContext
                CompletionScopeExpectation.VariableOrValue
                variableFieldAll
                variableFieldNonGlobal
                createSnippetWithScore

        let rec convRuleToCompletion (key: string) (count: int) (context: ScopeContext) (rule: NewRule) =
            //            eprintfn "crtc %A %A %A" key count rule
            let r, o = rule

            let scoreFunctioni =
                scoreFunction context o.requiredScopes CompletionScopeOutput.Nothing CompletionScopeExpectation.Nothing

            let createSnippetForClausei = createSnippetForClause scoreFunctioni

            let createSnippetForClauseWithCustomScopeReq =
                (fun r ->
                    createSnippetForClause (
                        scoreFunction context r CompletionScopeOutput.Nothing CompletionScopeExpectation.Nothing
                    ))

            let enough = o.max < count

            if enough then
                [||]
            else
                let keyvalue (inner: string) =
                    CompletionResponse.Snippet(
                        inner,
                        $"%s{inner} = $0",
                        o.description,
                        Some(scoreFunctioni inner),
                        CompletionCategory.Other
                    )

                let keyvalueWithCustomScopeReq r (inner: string) =
                    CompletionResponse.Snippet(
                        inner,
                        $"%s{inner} = $0",
                        o.description,
                        Some(
                            (scoreFunction context r CompletionScopeOutput.Nothing CompletionScopeExpectation.Nothing)
                                inner
                        ),
                        CompletionCategory.Other
                    )

                match r with
                | NodeRule(SpecificField(SpecificValue s), innerRules) ->
                    [| createSnippetForClausei
                           innerRules
                           o.description
                           (StringResource.stringManager.GetStringForID s.normal) |]
                | NodeRule(ValueField(ValueType.Enum e), innerRules) ->
                    enums.TryFind(e)
                    |> Option.map (fun (_, es) ->
                        es.StringValues
                        |> Array.ofSeq
                        |> Array.map (fun e -> createSnippetForClausei innerRules o.description e))
                    |> Option.defaultValue [||]
                | NodeRule(ValueField _, _) -> [||]
                | NodeRule(AliasField _, _) -> [||]
                | NodeRule(FilepathField _, _) -> [||]
                | NodeRule(IconField(folder), innerRules) ->
                    checkIconField folder
                    |> Array.map (fun e -> createSnippetForClausei innerRules o.description e)
                | NodeRule(LocalisationField _, _) -> [||]
                | NodeRule(ScopeField(x), innerRules) ->
                    (completionForScopeDotChain
                        key
                        context
                        innerRules
                        o.description
                        (CompletionScopeExpectation.Scopes x))
                    |> List.toArray
                //TODO: Scopes better
                | NodeRule(SubtypeField _, _) -> [||]
                | NodeRule(TypeField(TypeType.Simple t), innerRules) ->
                    tryFindTypeValueList t
                    |> Option.map (fun ts ->
                        ts
                        |> Seq.map (fun e -> createSnippetForClausei innerRules o.description e)
                        |> Seq.toArray)
                    |> Option.defaultValue [||]
                | NodeRule(TypeField(TypeType.Complex(p, t, s)), innerRules) ->
                    tryFindTypeValueList t
                    |> Option.map (fun ts ->
                        ts
                        |> Seq.map (fun e -> createSnippetForClausei innerRules o.description (p + e + s))
                        |> Seq.toArray)
                    |> Option.defaultValue [||]
                | NodeRule(VariableGetField v, innerRules) ->
                    varMap.TryFind(v)
                    |> Option.map (fun ss ->
                        ss.StringValues
                        |> List.ofSeq
                        |> List.map (fun e -> createSnippetForClausei innerRules o.description e)
                        |> List.toArray)
                    |> Option.defaultValue [||]

                | LeafRule(SpecificField(SpecificValue s), _) ->
                    [| keyvalue (StringResource.stringManager.GetStringForID s.normal) |]
                | LeafRule(ValueField(ValueType.Enum e), _) ->
                    enums.TryFind(e)
                    |> Option.map (fun (_, es) -> es.StringValues |> Array.ofSeq |> Array.map (fun e -> keyvalue e))
                    |> Option.defaultValue [||]
                | LeafRule(ValueField _, _) -> [||]
                | LeafRule(AliasField _, _) -> [||]
                | LeafRule(FilepathField _, _) -> [||]
                | LeafRule(IconField(folder), _) -> checkIconField folder |> Array.map keyvalue
                | LeafRule(LocalisationField _, _) -> [||]
                | LeafRule(ScopeField _, _) ->
                    scopeFieldAll
                    |> Seq.map (fun x -> keyvalueWithCustomScopeReq x.requiredScopes x.key)
                    |> Seq.toArray
                //TODO: Scopes
                | LeafRule(SubtypeField _, _) -> [||]
                | LeafRule(TypeField(TypeType.Simple t), _) ->
                    tryFindTypeValueList t
                    |> Option.map (fun ts -> ts |> Seq.map keyvalue |> Seq.toArray)
                    |> Option.defaultValue [||]
                | LeafRule(TypeField(TypeType.Complex(p, t, s)), _) ->
                    tryFindTypeValueList t
                    |> Option.map (fun ts -> ts |> Seq.map (fun e -> keyvalue (p + e + s)) |> Seq.toArray)
                    |> Option.defaultValue [||]
                | LeafRule(VariableGetField v, _) ->
                    varMap.TryFind(v)
                    |> Option.map (fun ss -> ss.StringValues |> Array.ofSeq |> Array.map keyvalue)
                    |> Option.defaultValue [||]
                | LeafRule(VariableSetField v, _) ->
                    varMap.TryFind(v)
                    |> Option.map (fun ss -> ss.StringValues |> Array.ofSeq |> Array.map keyvalue)
                    |> Option.defaultValue [||]

                | LeafValueRule lv ->
                    match lv with
                    | NewField.TypeField(TypeType.Simple t) ->
                        tryFindTypeValueList t
                        |> Option.defaultValue []
                        |> Seq.map CompletionResponse.CreateSimple
                        |> Seq.toArray
                    | NewField.TypeField(TypeType.Complex(p, t, s)) ->
                        tryFindTypeValueList t
                        |> Option.map (fun ns -> List.map (fun n -> p + n + s) ns)
                        |> Option.defaultValue []
                        |> Seq.map CompletionResponse.CreateSimple
                        |> Seq.toArray
                    | NewField.ValueField(Enum e) ->
                        enums.TryFind(e)
                        |> Option.map (fun (_, s) -> s.StringValues |> List.ofSeq)
                        |> Option.defaultValue []
                        |> Seq.map CompletionResponse.CreateSimple
                        |> Seq.toArray
                    | NewField.VariableGetField v ->
                        varMap.TryFind(v)
                        |> Option.map (fun s -> s.StringValues |> List.ofSeq)
                        |> Option.defaultValue []
                        |> Seq.map CompletionResponse.CreateSimple
                        |> Seq.toArray
                    | NewField.VariableSetField v ->
                        varMap.TryFind(v)
                        |> Option.map (fun s -> s.StringValues |> List.ofSeq)
                        |> Option.defaultValue []
                        |> Seq.map CompletionResponse.CreateSimple
                        |> Seq.toArray
                    | _ -> [||]
                | SubtypeRule _ -> [||]
                | _ -> [||]
        //TODO: Add leafvalue
        let typeCompletionItems (typeName: string) (suffixPatterns: string list) =
            let values = tryFindTypeValueList typeName |> Option.defaultValue []

            Seq.append values (FieldValidators.typeSuffixPatternBaseValues values suffixPatterns)
            |> Seq.distinctBy (fun value -> value.ToLowerInvariant())
            |> Seq.map CompletionResponse.CreateSimple
            |> Seq.toArray

        let normaliseFileExtension (extension: string) =
            extension.Trim().TrimStart('.').ToLowerInvariant()

        let fileCompletionItems prefix extension (options: Options) =
            let allowedExtensions =
                options.fileExtensions
                |> List.map normaliseFileExtension
                |> List.filter (String.IsNullOrWhiteSpace >> not)
                |> List.distinct

            let matchesPrefix (file: string) =
                match prefix with
                | Some p when p <> "" ->
                    file.Replace('\\', '/').StartsWith(p.Replace('\\', '/'), StringComparison.OrdinalIgnoreCase)
                | _ -> true

            let matchesExtension (file: string) =
                let fileExtension =
                    Path.GetExtension(file) |> normaliseFileExtension

                match extension, allowedExtensions with
                | Some ext, _ -> fileExtension = normaliseFileExtension ext
                | None, [] -> true
                | None, allowed -> allowed |> List.contains fileExtension

            files
            |> Seq.filter (fun file -> matchesPrefix file && matchesExtension file)
            |> Seq.map CompletionResponse.CreateSimple
            |> Seq.toArray

        let filenameCompletionItems prefix =
            let matchesPrefix (file: string) =
                match prefix with
                | Some p when p <> "" ->
                    file.Replace('\\', '/').StartsWith(p.Replace('\\', '/'), StringComparison.OrdinalIgnoreCase)
                | _ -> true

            files
            |> Seq.filter matchesPrefix
            |> Seq.map (fun file -> Path.GetFileName(file.Replace('\\', '/')))
            |> Seq.filter (String.IsNullOrWhiteSpace >> not)
            |> Seq.distinctBy (fun file -> file.ToLowerInvariant())
            |> Seq.map CompletionResponse.CreateSimple
            |> Seq.toArray

        let databaseObjectCompletionItems (value: string) =
            let configuredTypes = extendedConfigMetadata.databaseObjectTypes

            if Map.isEmpty configuredTypes then
                [||]
            else
                let raw = value.Trim().Trim('"')

                let typedValues typeName =
                    tryFindTypeValueList typeName |> Option.defaultValue []

                let localisationValues prefix =
                    defaultKeys
                    |> Seq.filter (fun key ->
                        String.IsNullOrWhiteSpace prefix
                        || key.StartsWith(prefix, StringComparison.OrdinalIgnoreCase))
                    |> Seq.toList

                let objectValues (config: DatabaseObjectTypeConfig) =
                    match config.objectType, config.localisationPrefix with
                    | Some typeName, _ -> typedValues typeName
                    | None, Some prefix -> localisationValues prefix
                    | None, None -> []

                let completions =
                    if not (raw.Contains ':') then
                        configuredTypes
                        |> Map.toSeq
                        |> Seq.map (fun (name, _) -> name + ":")
                    else
                        let parts = raw.Split([| ':' |], StringSplitOptions.None)
                        let prefix = parts.[0]

                        match configuredTypes |> Map.tryFind prefix with
                        | None -> Seq.empty
                        | Some config when parts.Length <= 2 ->
                            objectValues config
                            |> Seq.map (fun id -> prefix + ":" + id)
                        | Some config ->
                            match config.swapType with
                            | Some swapType ->
                                typedValues swapType
                                |> Seq.map (fun id -> prefix + ":" + parts.[1] + ":" + id)
                            | None -> Seq.empty

                completions
                |> Seq.distinctBy (fun value -> value.ToLowerInvariant())
                |> Seq.map CompletionResponse.CreateSimple
                |> Seq.toArray

        let splitPrefixedValue (value: string) =
            let value = value.Trim().Trim('"')
            let colonIndex = value.IndexOf(':')

            if colonIndex > 0 then
                value.Substring(0, colonIndex + 1), value.Substring(colonIndex + 1)
            else
                "", value

        let rec fieldToRules (field: NewField) (value: string) (scopeContext: ScopeContext) (options: Options) =
            //            log (sprintf "%A %A" field value)
            //            eprintfn "%A" value
            match options.completionType with
            | Some typeName -> typeCompletionItems typeName options.typeSuffixPatterns
            | None ->
                match field with
                | NewField.ValueField(Enum e) ->
                    enums.TryFind(e)
                    |> Option.map (fun (_, s) -> s.StringValues |> Array.ofSeq)
                    |> Option.defaultValue [||]
                    |> Array.map CompletionResponse.CreateSimple
                | NewField.ValueField v ->
                    FieldValidators.getValidValues v
                    |> Option.defaultValue [||]
                    |> Seq.map CompletionResponse.CreateSimple
                    |> Seq.toArray
                | NewField.TypeField(TypeType.Simple t) ->
                    typeCompletionItems t options.typeSuffixPatterns
                | NewField.TypeField(TypeType.Complex(p, t, s)) ->
                    tryFindTypeValueList t
                    |> Option.map (fun ns -> List.map (fun n -> p + n + s) ns)
                    |> Option.defaultValue []
                    |> Seq.map CompletionResponse.CreateSimple
                    |> Seq.toArray
                | NewField.LocalisationField(s, _) ->
                    match s, value.Contains '[' with
                    | false, true -> (allPossibles |> Array.map CompletionResponse.CreateSimple)
                    | true, _ ->
                        localisation
                        |> Array.tryFind (fun (lang, _) -> lang = (STL STLLang.Default))
                        |> Option.map (snd >> Set.toArray)
                        |> Option.defaultValue [||]
                        |> Array.map CompletionResponse.CreateSimple
                    | false, _ ->
                        localisation
                        |> Array.tryFind (fun (lang, _) -> lang <> (STL STLLang.Default))
                        |> Option.map (snd >> Set.toArray)
                        |> Option.defaultValue [||]
                        |> Array.map CompletionResponse.CreateSimple
                | NewField.PrefixedField inner ->
                    let _, innerValue = splitPrefixedValue value
                    fieldToRules inner innerValue scopeContext options
                | NewField.FilepathField(prefix, extension) -> fileCompletionItems prefix extension options
                | NewField.FilenameField prefix -> filenameCompletionItems prefix
                | NewField.ScopeField x ->
                    completionForRHSScopeChain value scopeContext (CompletionScopeExpectation.Scopes x)
                    |> List.toArray
                | NewField.VariableGetField v ->
                    varMap.TryFind v
                    |> Option.map (fun ss -> ss.StringValues |> Array.ofSeq)
                    |> Option.defaultValue [||]
                    |> Array.map CompletionResponse.CreateSimple
                | NewField.VariableSetField v ->
                    varMap.TryFind v
                    |> Option.map (fun ss -> ss.StringValues |> Array.ofSeq)
                    |> Option.defaultValue [||]
                    |> Array.map CompletionResponse.CreateSimple
                | NewField.DynamicValueField v ->
                    varMap.TryFind v
                    |> Option.map (fun ss -> ss.StringValues |> Array.ofSeq)
                    |> Option.defaultValue [||]
                    |> Array.map CompletionResponse.CreateSimple
                | NewField.TagsField(v, _) ->
                    varMap.TryFind v
                    |> Option.map (fun ss -> ss.StringValues |> Array.ofSeq)
                    |> Option.defaultValue [||]
                    |> Array.map CompletionResponse.CreateSimple
                | NewField.DatabaseObjectField -> databaseObjectCompletionItems value
                | NewField.AliasValueKeysField aliasKey ->
                    aliasKeyMap
                    |> Map.tryFind aliasKey
                    |> Option.map (fun values ->
                        values
                        |> Seq.map stringManager.GetStringForID
                        |> Seq.toArray)
                    |> Option.defaultValue [||]
                    |> Array.map CompletionResponse.CreateSimple
                | NewField.VariableField _ -> (completionForRHSVariableChain value scopeContext) |> List.toArray
                | NewField.ValueScopeField _ ->
                    (completionForRHSValueChain value scopeContext)
                        .Concat(
                            enums.TryFind("static_values")
                            |> Option.map (fun (_, s) -> s.StringValues |> List.ofSeq)
                            |> Option.defaultValue []
                            |> List.map CompletionResponse.CreateSimple
                        )
                        .ToArray()
                | _ -> [||]

        let p =
            { varMap = varMap
              enumsMap = enumsMap
              typesMap = typesMap
              databaseObjectTypes = extendedConfigMetadata.databaseObjectTypes
              linkMap = linkMap
              valueTriggerMap = valueTriggerMap
              varSet = varSet
              localisation = localisationKeys
              defaultLocalisation = defaultKeys
              files = files
              changeScope = changeScope
              anyScope = anyScope
              defaultLang = defaultLang
              wildcardLinks = wildCardLinks
              aliasKeys = aliasKeyMap
              processLocalisation = processLocalisation
              validateLocalisation = validateLocalisation }

        let ctx =
            { subtypes = []
              scopes = defaultContext
              warningOnly = false }

        let severity = Severity.Error

        let rec findRule
            (rules: NewRule array)
            (stack: (string * int * string option * CompletionContext) list)
            scopeContext
            =
            let subtypedRules =
                rules
                |> Array.collect (function
                    | SubtypeRule(_, _, cfs), _ -> cfs
                    | x -> [| x |])

            let expandedRules =
                subtypedRules
                |> Array.collect (function
                    | LeafRule(AliasField a, _), o ->
                        (rootRules.Aliases.TryFind a |> Option.defaultValue [||])
                        |> Array.map (fun (r, oi) -> (r, { oi with min = o.min; max = oi.max }))
                    | NodeRule(AliasField a, _), o ->
                        (rootRules.Aliases.TryFind a |> Option.defaultValue [||])
                        |> Array.map (fun (r, oi) -> (r, { oi with min = o.min; max = oi.max }))
                    | x -> [| x |])
            //eprintfn "fr %A %A" stack (expandedRules |> List.truncate 10)
            match stack with
            | [] -> expandedRules |> Array.collect (convRuleToCompletion "" 0 scopeContext)
            | [ (key, count, None, NodeLHS) ] ->
                expandedRules |> Array.collect (convRuleToCompletion key count scopeContext)
            | [ (key, count, None, NodeRHS) ] ->
                match
                    expandedRules
                    |> Array.choose (function
                        | NodeRule(l, rs), o when
                            FieldValidators.checkFieldByKey
                                p
                                severity
                                ctx
                                l
                                (StringResource.stringManager.InternIdentifierToken key)
                            ->
                            Some(l, rs, o)
                        | _ -> None)
                with
                | [||] -> expandedRules |> Array.collect (convRuleToCompletion key count scopeContext)
                | fs ->
                    fs
                    |> Array.collect (fun (_, innerRules, _) -> findRule innerRules [] scopeContext)
            | [ (key, count, Some _, LeafLHS) ] ->
                expandedRules |> Array.collect (convRuleToCompletion key count scopeContext)
            | [ (key, count, Some value, LeafRHS) ] ->
                match
                    expandedRules
                    |> Array.choose (function
                        | LeafRule(l, r), o when
                            FieldValidators.checkFieldByKey
                                p
                                severity
                                ctx
                                l
                                (StringResource.stringManager.InternIdentifierToken key)
                            ->
                            Some(l, r, o)
                        | _ -> None)
                with
                | [||] -> expandedRules |> Array.collect (convRuleToCompletion key count scopeContext)
                | fs ->
                    //log "%s %A" key fs
                    let res = fs |> Array.collect (fun (_, f, o) -> fieldToRules f value scopeContext o)
                    //log "res %A" res
                    res
            | [ (_, _, Some value, LeafValueRHS) ] ->
                match
                    expandedRules
                    |> Array.choose (function
                        | LeafValueRule f, o -> Some(f, o)
                        | _ -> None)
                with
                | [||] -> expandedRules |> Array.collect (convRuleToCompletion value 0 scopeContext)
                | fs ->
                    let hasPrefix =
                        let value = value.Trim().Trim('"')
                        value.IndexOf(':') > 0

                    let prefixedFields =
                        fs
                        |> Array.filter (fun (field, _) ->
                            match field with
                            | PrefixedField _ -> true
                            | _ -> false)

                    let fs =
                        if hasPrefix && prefixedFields.Length > 0 then
                            prefixedFields
                        else
                            fs

                    fs |> Array.collect (fun (f, o) -> fieldToRules f value scopeContext o)
            | (key, count, _, NodeRHS) :: rest ->
                match
                    expandedRules
                    |> Array.choose (function
                        | NodeRule(l, rs), o when
                            FieldValidators.checkFieldByKey
                                p
                                severity
                                ctx
                                l
                                (StringResource.stringManager.InternIdentifierToken key)
                            ->
                            Some(l, rs, o)
                        | _ -> None)
                with
                | [||] -> expandedRules |> Array.collect (convRuleToCompletion key count scopeContext)
                | fs ->
                    fs
                    |> Array.collect (fun (_, innerRules, _) -> findRule innerRules rest scopeContext)
            | (key, count, _, t) :: rest ->
                log $"Completion error %A{key} %A{t}"
                expandedRules |> Array.collect (convRuleToCompletion key count scopeContext)

        let stack = stack |> List.map (fun (a, b, c, d, e) -> (a, b, c, d))
        let res = findRule rules stack scopeContext |> Array.distinct
        //log "res2 %A" res
        res

    let scoreFunction
        (allUsedKeys: Collections.Set<string>)
        (startingContext: ScopeContext)
        (inputScopes: Scope list)
        (outputScope: CompletionScopeOutput)
        (expectedScope: CompletionScopeExpectation)
        (key: string)
        =

        let validInputScopeScore =
            match inputScopes with
            | [] -> 0 // This item doesn't care what scope it's in
            | [ x ] when x = anyScope -> 10 // It supports any scope, so, non-specific
            | xs -> // This item expects these scopes
                match startingContext.CurrentScope with
                | x when x = anyScope -> 20 // We're in any scope, so non-specific
                | s ->
                    if List.exists s.IsOfScope xs then
                        50 // It supports the scope we're in
                    else
                        0 // It doesn't support the scope we're in

        let validOutputScopeScore =
            match expectedScope, outputScope with
            | VariableOrValue, CompletionScopeOutput.Value -> 25
            | VariableOrValue, CompletionScopeOutput.Variable -> 20
            | Nothing, CompletionScopeOutput.Nothing -> 25
            | Scopes expectedScopes, CompletionScopeOutput.Scope scope ->
                match expectedScopes, scope with
                | [ x ], _ when x = anyScope -> 5 // The context expects any scope, so, non-specific
                | [], _ -> 0 // The context doesn't want a scope
                | xs, y when y = anyScope -> 15 // We're in any scope, so, non-specific
                | xs, y ->
                    if List.exists y.IsOfScope xs then
                        25 // It expects the scope we'll output
                    else
                        0
            | _ -> 0

        let usedKeyBonus = if Set.contains key allUsedKeys then 10 else 0
        let score = validInputScopeScore + validOutputScopeScore + usedKeyBonus
        max score 1

    let complete (pos: pos) (entity: Entity) (scopeContext: ScopeContext option) (extraGlobalVars: string list option) =
        let scopeContext = Option.defaultValue defaultContext scopeContext
        let path = getRulePath pos [] entity.entity |> List.rev

        let tryFindNodePathAtPos (pos: pos) (root: Node) =
            let rec loop path (node: Node) =
                match node.Nodes |> Seq.tryFind (fun child -> rangeContainsPos child.Position pos) with
                | Some child -> loop (node :: path) child
                | None -> Some(List.rev (node :: path))

            loop [] root

        let tryFindParameterOwner (path: Node list) =
            path
            |> List.mapi (fun i node -> i, node)
            |> List.rev
            |> List.tryPick (fun (i, node) ->
                if i > 0 && String.Equals(node.Key, "parameters", StringComparison.OrdinalIgnoreCase) then
                    Some path.[i - 1]
                else
                    None)

        let tryPathAfterParameters path =
            path
            |> List.mapi (fun i (key, _, _, _, _) -> i, key)
            |> List.rev
            |> List.tryPick (fun (i, key) ->
                if String.Equals(key, "parameters", StringComparison.OrdinalIgnoreCase) then
                    Some(path |> List.skip (i + 1))
                else
                    None)
        
        // Combine initialization-time globalScriptVariables with runtime-provided extraGlobalVars
        let effectiveGlobalVars = 
            match extraGlobalVars with
            | Some vars -> vars @ globalScriptVariables
            | None -> globalScriptVariables
        
        //        log (sprintf "%A" path)

        // log "%A" typedefs
        // log "%A" pos
        // log "%A" entity.logicalpath
        // log  (sprintf "tb %A" pathDir)
        let skiprootkey (skipRootKey: SkipRootKey) (s: string) =
            match skipRootKey with
            | SpecificKey key -> s == key
            | AnyKey -> true
            | MultipleKeys(keys, shouldMatch) -> (keys |> List.exists ((==) s)) <> (not shouldMatch)

        let pathFilteredTypes =
            typedefs
            |> List.filter (fun t -> FieldValidatorsHelper.CheckPathDir(t.pathOptions, entity.logicalpath))

        let allUsedKeys =
            getAllKeysInFile entity.entity @ effectiveGlobalVars |> Set.ofList

        let scoreFunction = scoreFunction allUsedKeys

        let tryAliasParameterCompletions () =
            match aliasParamMarkers.Length, tryPathAfterParameters path, tryFindNodePathAtPos pos entity.entity with
            | 0, _, _
            | _, None, _
            | _, _, None -> None
            | _, Some parameterPath, Some nodePath ->
                match tryFindParameterOwner nodePath with
                | None -> None
                | Some owner ->
                    aliasParamMarkers
                    |> Seq.tryPick (fun (aliasName, selectorField) ->
                        let selectedAlias = owner.TagText selectorField

                        match String.IsNullOrWhiteSpace selectedAlias, trySelectedAliasRules aliasName selectedAlias with
                        | true, _
                        | _, None -> None
                        | false, Some rules ->
                            let completions =
                                getCompletionFromPath scoreFunction rules parameterPath scopeContext
                                |> Array.distinct

                            if completions.Length = 0 then
                                None
                            else
                                Some(completions |> Array.toList))

        let rec validateTypeSkipRoot
            (t: TypeDefinition)
            (skipRootKeyStack: SkipRootKey list)
            (path: (string * int * string option * CompletionContext * string option) list)
            =
            let typerules =
                rootRules.TypeRules
                |> Seq.choose (function
                    | name, typerule when name == t.name -> Some typerule
                    | _ -> None)
                |> Seq.toArray

            match skipRootKeyStack, t.type_per_file, path with
            | _, false, [] -> getCompletionFromPath scoreFunction typerules [] scopeContext
            | _, true, (head, c, b, nt, keyprefix) :: tail ->
                // getCompletionFromPath scoreFunction typerules ((head, c, b, nt)::tail) scopeContext
                getCompletionFromPath
                    scoreFunction
                    typerules
                    ((t.name, 1, None, NodeRHS, None) :: (head, c, b, nt, keyprefix) :: tail)
                    scopeContext
            | _, true, [] ->
                getCompletionFromPath scoreFunction typerules [ t.name, 1, None, NodeRHS, None ] scopeContext
            | [], false, (head, c, _, _, keyprefix) :: tail ->
                //TODO: Handle key prefix
                if FieldValidators.typekeyfilter t head keyprefix then
                    getCompletionFromPath
                        scoreFunction
                        typerules
                        ((t.name, c, None, NodeRHS, None) :: tail)
                        scopeContext
                else
                    [||]
            | head :: tail, false, (pathhead, _, _, _, _) :: pathtail ->
                if skiprootkey head pathhead then
                    validateTypeSkipRoot t tail pathtail
                else
                    [||]

        let items =
            match path |> List.tryLast, path.Length with
            // The cursor (magic char) sits inside a value token starting with '@': offer the
            // scripted-variable list. Matching any partially typed token (not just a bare '@')
            // mirrors validation, which accepts an '@' value for every ValueField.
            | Some(_, count, Some x, _, _), _ when
                x.Length > 0 && x.StartsWith "@" && x.Contains magicCharString
                ->
                let localVars =
                    CWTools.Validation.Stellaris.STLValidation.getDefinedVariables entity.entity
                    |> List.filter (fun v -> not (v.StartsWith("@[")) && not (v.StartsWith(@"@\[")))  // 过滤掉表达式

                let allVars = effectiveGlobalVars @ localVars
                allVars |> List.distinct |> List.map (fun s -> CompletionResponse.CreateSimple s)
            | Some(_, _, _, CompletionContext.NodeLHS, _), 1 -> []
            | _ ->
                match tryAliasParameterCompletions () with
                | Some items -> items
                | None ->
                    pathFilteredTypes
                    |> Seq.collect (fun t -> validateTypeSkipRoot t t.skipRootKey path)
                    |> Seq.toList
        //TODO: Expand this to use a snippet not just the name of the type
        let createSnippetForType (typeDef: TypeDefinition) =
            let subtypeSnippets =
                typeDef.subtypes
                |> List.choose (fun st ->
                    if st.typeKeyField.IsSome then
                        Some st.typeKeyField.Value
                    else
                        None)

            let rootSnippets =
                if typeDef.rootCompletionFromSubtypes then
                    []
                else
                    match typeDef.typeKeyFilter with
                    | Some(keys: string list, false) -> keys
                    | _ -> [ typeDef.name ]

            rootSnippets @ subtypeSnippets
            |> List.map (fun s -> createSnippetForClause (fun _ -> 1) [||] None s)

        let rootTypeItems =
            match path with
            | [ (_, _, _, CompletionContext.NodeLHS, _) ] -> pathFilteredTypes |> List.collect createSnippetForType
            | y when y.Length = 0 -> pathFilteredTypes |> List.collect createSnippetForType
            | _ -> []
        // eprintfn "%A" path
        // eprintfn "%A" rootTypeItems
        let scoreForLabel (label: string) =
            if allUsedKeys |> Set.contains label then 10 else 1

        (items @ rootTypeItems)
        |> List.map (function
            | Simple(label, None, kind) -> Simple(label, Some(scoreForLabel label), kind)
            | Detailed(label, desc, None, kind) -> Detailed(label, desc, Some(scoreForLabel label), kind)
            | Snippet(label, snippet, desc, None, kind) ->
                Snippet(label, snippet, desc, Some(scoreForLabel label), kind)
            | x -> x)



    member _.Complete(pos: pos, entity: Entity, scopeContext, extraGlobalVars) = complete pos entity scopeContext extraGlobalVars
    member _.LocalisationComplete(pos: pos, filetext: string) = locComplete pos filetext
    /// Expose the AST rule-path computation for external callers (e.g. inline_script caller-path)
    member _.GetRulePath(pos: pos, node: IClause) = getRulePath pos [] node |> List.rev

    /// Complete for inline_script files: uses the inline entity's AST path but prepends the caller's path prefix
    /// so that type rules match correctly. callerRulePath is the structural path from the caller entity root
    /// down to (but not including) the inline_script call site, used to anchor completions at the correct depth
    /// (e.g. inside "immediate" for effect-level completions).
    member _.CompleteInlineScript
        (pos: pos, inlineEntity: Entity, callerEntity: Entity, scopeContext: ScopeContext option, extraGlobalVars: string list option, callerRulePath: (string * int * string option * CompletionContext * string option) list)
        =
        let scopeContext = Option.defaultValue defaultContext scopeContext
        let effectiveGlobalVars =
            match extraGlobalVars with
            | Some vars -> vars @ globalScriptVariables
            | None -> globalScriptVariables

        // Get the path within the inline_script file at the current cursor position
        let inlinePath = getRulePath pos [] inlineEntity.entity |> List.rev

        // Filter types by the caller's logicalpath
        let pathFilteredTypes =
            typedefs
            |> List.filter (fun t -> FieldValidatorsHelper.CheckPathDir(t.pathOptions, callerEntity.logicalpath))

        let allUsedKeys =
            getAllKeysInFile inlineEntity.entity @ effectiveGlobalVars |> Set.ofList

        let scoreFunction = scoreFunction allUsedKeys

        let skiprootkey (skipRootKey: SkipRootKey) (s: string) =
            match skipRootKey with
            | SpecificKey key -> s == key
            | AnyKey -> true
            | MultipleKeys(keys, shouldMatch) -> (keys |> List.exists ((==) s)) <> (not shouldMatch)

        // Strip inline_script/script leaves from callerRulePath. The first remaining
        // element is the caller's type instance/subtype key; getCompletionFromPath
        // expects the canonical type rule key instead, so we keep only the caller's
        // path below that root. Keep track of whether such a caller root existed:
        // an inline script called from inside a type root treats its own top-level
        // keys as fields, while an inline script with no caller context treats its
        // first top-level key as a type instance.
        //
        // BEST-OF-BOTH STRATEGY: For control-flow caller paths, compute TWO paths:
        //   1. fullCallerPath   = all intermediate elements (e.g. [desc, trigger])
        //   2. minimalCallerPath = only the first element (e.g. [desc])
        // Then try both and use whichever returns MORE completions.
        //
        // WHY: Some intermediate elements are scope-DEFINING (desc > trigger changes context
        // from desc-content to trigger-content) and MUST be kept. Others are transparent
        // control-flow (switch, if) whose dynamic children can't be resolved by
        // getCompletionFromPath, returning few wrong intermediate-level results.
        // The "more results" heuristic works for transparent control-flow because:
        //   - Correct deep resolution returns many content-level completions (200+ effects/triggers)
        //   - Wrong intermediate-level resolution returns few structural fields (1-5 items)
        // For concrete data blocks (icon/layer, resources/upkeep, etc.) a smaller
        // completion list can be the precise one, so keep the full path there.
        let rawCallerPath =
            callerRulePath
            |> List.filter (fun (key, _, _, _, _) ->
                not (key = "inline_script" || key = "script"))

        let callerHasTypeRoot = not rawCallerPath.IsEmpty

        let fullCallerPath =
            match rawCallerPath with
            | _ :: rest -> rest
            | [] -> []

        let minimalCallerPath =
            match fullCallerPath with
            | first :: _ -> [first]
            | [] -> []

        let isTransparentCallerKey (key: string) =
            let key = key.ToLowerInvariant()
            key = "if"
            || key = "else"
            || key = "else_if"
            || key = "switch"
            || key = "random"
            || key = "random_list"
            || key = "while"
            || key.StartsWith("every_")
            || key.StartsWith("random_")
            || key.StartsWith("ordered_")

        let shouldTryMinimalCallerPath =
            fullCallerPath
            |> List.exists (fun (key, _, _, _, _) -> isTransparentCallerKey key)

        // Used for rootTypeItems suppression: any non-empty caller path means we're inside a block
        let intermediateCallerPath = fullCallerPath

        // Helper: try a path through getCompletionFromPath
        let tryPath scoreFunction typerules typeRoot callerPath suffix scopeContext =
            let fullPath = typeRoot :: (callerPath @ suffix)
            getCompletionFromPath scoreFunction typerules fullPath scopeContext

        // Try both full and minimal caller paths, return the one with more results.
        let bestOfBoth scoreFunction typerules typeRoot suffix scopeContext =
            let fullResult = tryPath scoreFunction typerules typeRoot fullCallerPath suffix scopeContext
            if fullCallerPath = minimalCallerPath || not shouldTryMinimalCallerPath then
                // Same path (0 or 1 elements), no need to try twice
                fullResult
            else
                let minimalResult = tryPath scoreFunction typerules typeRoot minimalCallerPath suffix scopeContext
                if fullResult.Length >= minimalResult.Length then fullResult
                else minimalResult

        let rec validateTypeSkipRootInline
            (t: TypeDefinition)
            (skipRootKeyStack: SkipRootKey list)
            (path: (string * int * string option * CompletionContext * string option) list)
            =
            let typerules =
                rootRules.TypeRules
                |> Seq.choose (function
                    | name, typerule when name == t.name -> Some typerule
                    | _ -> None)
                |> Seq.toArray

            let typeRoot = (t.name, 1, None, NodeRHS, None)

            match skipRootKeyStack, t.type_per_file, path with
            | _, false, [] ->
                // At root of inline_script = inside the caller's block.
                bestOfBoth scoreFunction typerules typeRoot [] scopeContext
            | _, true, _ ->
                // type_per_file: prepend type name + caller path
                bestOfBoth scoreFunction typerules typeRoot path scopeContext
            | [], false, (head, c, _, _, keyprefix) :: tail ->
                if fullCallerPath.IsEmpty && not callerHasTypeRoot then
                    // Inline scripts called at the file root should behave like
                    // normal files in the caller's folder: the first key is the
                    // type instance name, not an extra child under the type root.
                    if FieldValidators.typekeyfilter t head keyprefix then
                        let typedRoot = (t.name, c, None, NodeRHS, None)
                        bestOfBoth scoreFunction typerules typedRoot tail scopeContext
                    else
                        [||]
                else
                    // Inline scripts called inside a parent block are pasted into
                    // that block, so keep the inline path as fields under callerPath.
                    let suffix = (head, c, None, NodeRHS, keyprefix) :: tail
                    bestOfBoth scoreFunction typerules typeRoot suffix scopeContext
            | head :: rest, false, (pathhead, _, _, _, _) :: pathtail ->
                if skiprootkey head pathhead then
                    validateTypeSkipRootInline t rest pathtail
                else
                    [||]

        let items =
            match inlinePath |> List.tryLast, inlinePath.Length with
            // Same as the non-inline path: any '@'-prefixed token with the cursor inside it
            // gets the scripted-variable list, mirroring validation.
            | Some(_, count, Some x, _, _), _ when
                x.Length > 0 && x.StartsWith "@" && x.Contains magicCharString
                ->
                let localVars = CWTools.Validation.Stellaris.STLValidation.getDefinedVariables inlineEntity.entity
                                |> List.filter (fun v -> not (v.StartsWith("@[")) && not (v.StartsWith(@"@\[")))  // 过滤掉表达式
                let allVars = effectiveGlobalVars @ localVars
                allVars |> List.distinct |> List.map (fun s -> CompletionResponse.CreateSimple s)
            | Some(_, _, _, CompletionContext.NodeLHS, _), 1 -> []
            | _ ->
                pathFilteredTypes
                |> Seq.collect (fun t -> validateTypeSkipRootInline t t.skipRootKey inlinePath)
                |> Seq.toList

        let createSnippetForType (typeDef: TypeDefinition) =
            let subtypeSnippets =
                typeDef.subtypes
                |> List.choose (fun st -> if st.typeKeyField.IsSome then Some st.typeKeyField.Value else None)

            let rootSnippets =
                if typeDef.rootCompletionFromSubtypes then
                    []
                else
                    match typeDef.typeKeyFilter with
                    | Some(keys: string list, false) -> keys
                    | _ -> [ typeDef.name ]

            rootSnippets @ subtypeSnippets
            |> List.map (fun s -> createSnippetForClause (fun _ -> 1) [||] None s)

        // Only show root type items when there's NO intermediate caller path.
        // If we have a caller path, we're inside a block (e.g. immediate), not at type root.
        let rootTypeItems =
            match intermediateCallerPath, inlinePath with
            | [], [ (_, _, _, CompletionContext.NodeLHS, _) ] -> pathFilteredTypes |> List.collect createSnippetForType
            | [], y when y.Length = 0 -> pathFilteredTypes |> List.collect createSnippetForType
            | _ -> []

        let scoreForLabel (label: string) =
            if allUsedKeys |> Set.contains label then 10 else 1

        (items @ rootTypeItems)
        |> List.map (function
            | Simple(label, None, kind) -> Simple(label, Some(scoreForLabel label), kind)
            | Detailed(label, desc, None, kind) -> Detailed(label, desc, Some(scoreForLabel label), kind)
            | Snippet(label, snippet, desc, None, kind) -> Snippet(label, snippet, desc, Some(scoreForLabel label), kind)
            | x -> x)
