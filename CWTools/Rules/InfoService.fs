namespace CWTools.Rules

open System.Collections.Frozen
open System.Collections.Generic
open CSharpHelpers
open CWTools.Rules.RulesWrapper
open CWTools.Utilities
open CWTools.Utilities.Utils2
open CWTools.Utilities.Utils
open CWTools.Common
open System
open CWTools.Utilities.Position
open CWTools.Games
open CWTools.Process.Localisation
open CWTools.Process
open CWTools.Process.Scopes
open CWTools.Validation
open CWTools.Validation.ValidationCore
open System.Collections.Concurrent
open CWTools.Utilities.StringResource

module Test =
    let inline mergeFolds (l1, lv1, c1, n1, vc1, ctx1) (l2, lv2, c2, n2, vc2, ctx2) =
        let fLeaf = (fun (acc1, acc2) l r -> (l1 acc1 l r, l2 acc2 l r))
        let fLeafValue = (fun (acc1, acc2) lv r -> (lv1 acc1 lv r, lv2 acc2 lv r))
        let fNode = (fun (acc1, acc2) n r -> (n1 acc1 n r, n2 acc2 n r))
        let fComment = (fun (acc1, acc2) c r -> (c1 acc1 c r, c2 acc2 c r))
        let fValueClause = (fun (acc1, acc2) vc r -> (vc1 acc1 vc r, vc2 acc2 vc r))
        fLeaf, fLeafValue, fComment, fNode, fValueClause, (ctx1, ctx2)

    let inline mergeFolds2 (l1, lv1, c1, n1, vc1, ctx1) (l2, lv2, c2, n2, vc2, ctx2) =
        let fLeaf = (fun ctx (acc1, acc2) l r -> (l1 ctx acc1 l r, l2 ctx acc2 l r))

        let fLeafValue =
            (fun ctx (acc1, acc2) lv r -> (lv1 ctx acc1 lv r, lv2 ctx acc2 lv r))

        let fNode = (fun ctx (acc1, acc2) n r -> (n1 ctx acc1 n r, n2 ctx acc2 n r))
        let fComment = (fun ctx (acc1, acc2) c r -> (c1 ctx acc1 c r, c2 ctx acc2 c r))

        let fValueClause =
            (fun ctx (acc1, acc2) vc r -> (vc1 ctx acc1 vc r, vc2 ctx acc2 vc r))

        fLeaf, fLeafValue, fComment, fNode, fValueClause, (ctx1, ctx2)

[<Sealed>]
type InfoService
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
        ruleValidationService: RuleValidationService,
        changeScope: ChangeScope,
        defaultContext,
        anyScope,
        defaultLang,
        processLocalisation:
            Lang * Collections.Map<string, CWTools.Localisation.Entry> -> Lang * Collections.Map<string, LocEntry>,
        validateLocalisation: LocEntry -> ScopeContext -> ValidationResult,
        ?extendedConfigMetadata: ExtendedConfigMetadata,
        ?aliasKeyMapOverride: Map<string, HashSet<StringToken>>,
        ?scopeContextOverride: IClause -> ScopeContext -> ScopeContext option
    ) =

    let extendedConfigMetadata = defaultArg extendedConfigMetadata ExtendedConfigMetadata.empty
    let scopeContextOverride = defaultArg scopeContextOverride (fun _ _ -> None)

    // Index TypeRules by name (case-insensitive, preserving entry order) so the
    // per-node info hot path does not re-filter the full rules array.
    let typeRulesByName =
        rootRules.TypeRules
        |> Array.fold
            (fun (m: Map<string, _>) (name, rules) ->
                let key = name.ToLowerInvariant()
                match Map.tryFind key m with
                | Some existing -> Map.add key (Array.append existing [| rules |]) m
                | None -> Map.add key [| rules |] m)
            Map.empty

    let applyScopeContextOverride (node: IClause) (context: ScopeContext) =
        let overrideInput =
            if node.Key.StartsWith("event_target:", System.StringComparison.OrdinalIgnoreCase) then
                // Unknown event targets get a temporary Any frame before the
                // normal scope-field pass. A precise game-specific override
                // replaces that placeholder; it must not preserve it as PREV.
                match context.Scopes, context.FromDepthStack with
                | current :: _ :: remainingScopes, _ :: remainingDepths ->
                    { context with
                        Scopes = current :: remainingScopes
                        FromDepthStack = remainingDepths }
                | _ -> context
            else
                context

        scopeContextOverride node overrideInput |> Option.defaultValue context

    let wildCardLinks =
        links.Values
        |> Seq.choose (function
            | :? ScopedEffect as e when e.IsWildCard -> Some e
            | _ -> None)
        |> Seq.toList



    let varSet =
        varMap.TryFind "variable" |> Option.defaultValue (PrefixOptimisedStringSet())

    let inner (map: IDictionary<string, ResizeArray<string>>) (subtype: string) (set: PrefixOptimisedStringSet) =
        set.IdValues
        |> Seq.map (fun i -> stringManager.GetStringForID i.normal)
        |> Seq.iter (fun v ->
            match map.TryGetValue v with
            | true, l -> l.Add subtype
            | false, _ ->
                map[v] <- ResizeArray<string>()
                map[v].Add subtype)

    // O(total type ids) inversion is only needed by type-localisation validation, so build it
    // lazily to keep it off the per-save service rebuild path.
    let invertedTypeMap: Lazy<IDictionary<string, ResizeArray<string>>> =
        lazy
            (let map = Dictionary<string, ResizeArray<string>>()
             types |> Seq.iter (fun pair -> inner map pair.Key pair.Value)
             map :> IDictionary<string, ResizeArray<string>>)

    let defaultKeys =
        localisation
        |> Array.choose (fun (l, ks) -> if l = defaultLang then Some ks else None)
        |> Array.tryHead
        |> Option.defaultValue Set.empty

    let localisationKeys =
        localisation
        |> Array.choose (fun (l, ks) -> if l = defaultLang then None else Some(l, ks))

    let aliasKeyMap =
        match aliasKeyMapOverride with
        | Some precomputed -> precomputed
        | None ->
            rootRules.Aliases
            |> Map.toList
            |> List.map (fun (key, rules) -> key, (rules |> Seq.collect (RulesMemoize.ruleToCompletionListHelper types enums) |> HashSet<StringToken>))
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
            | "distance"
            | "count"
            | "steps"
            | "value" -> true
            | _ -> false

        match ruleType with
        | LeafRule(SpecificField(SpecificValue key), _)
        | NodeRule(SpecificField(SpecificValue key), _) -> isComparisonKey key
        | _ -> false

    let memoizeRules =
        RulesMemoize.memoizeRulesWith
            rootRules
            (fun rules _ ->
                rules
                |> Array.collect (fun (r, o) ->
                    r
                    |> (function
                    | SubtypeRule(_, _, cfs) -> cfs
                    | x -> [||])))

    let getRulesContextFromOptions (subtypeScope: SubTypeScope option) (subtypes: string list) (typeruleOptions: Options option) =
        let replaceContext rs =
            let replaceContext =
                { Root = rs.root |> Option.orElse rs.this |> Option.defaultValue anyScope
                  From = rs.froms |> Option.defaultValue []
                  FromDepth = 0
                  FromDepthStack = []
                  Scopes = rs.prevs |> Option.defaultValue [] }

            if rs.this |> Option.isSome then
                { subtypes = subtypes
                  scopes =
                    { replaceContext with
                        Scopes = rs.this.Value :: replaceContext.Scopes }
                  warningOnly = false }
            else
                { subtypes = subtypes
                  scopes = replaceContext
                  warningOnly = false }

        match subtypeScope, typeruleOptions with
        | Some(SubTypeReplaceScopes rs), _ -> replaceContext rs
        | Some(SubTypePushScope ps), _ ->
            { subtypes = subtypes
              scopes =
                  { Root = ps
                    From = []
                    FromDepth = 0
                    FromDepthStack = []
                    Scopes = [ ps ] }
              warningOnly = false }
        | None, Some { replaceScopes = Some rs } -> replaceContext rs
        | None, Some { pushScope = Some ps } ->
            { subtypes = subtypes
              scopes =
                  { Root = ps
                    From = []
                    FromDepth = 0
                    FromDepthStack = []
                    Scopes = [ ps ] }
              warningOnly = false }
        | None, _ ->
            { subtypes = subtypes
              scopes = defaultContext
              warningOnly = false }

    let rec singleInfoService fNode fChild fLeaf fLeafValue fValueClause fComment acc child rule : 'r =
        let recurse = singleInfoService fNode fChild fLeaf fLeafValue fValueClause fComment

        match child with
        | NodeC node ->
            let finalAcc = fNode acc node rule

            match fChild finalAcc (node :> IClause) rule with
            | Some(child, newRule) -> recurse finalAcc child newRule
            | None -> finalAcc
        | ValueClauseC valueClause ->
            let finalAcc = fValueClause acc valueClause rule

            match fChild finalAcc (valueClause :> IClause) rule with
            | Some(child, newRule) -> recurse finalAcc child newRule
            | None -> finalAcc
        | LeafC leaf -> fLeaf acc leaf rule
        | LeafValueC leafvalue -> fLeafValue acc leafvalue rule
        | CommentC comment -> fComment acc comment rule

    let rec infoService fNode fChild fLeaf fLeafValue fValueClause fComment ignore acc child rule : 'r =
        let recurse = infoService fNode fChild fLeaf fLeafValue fValueClause fComment ignore

        match child with
        | NodeC node ->
            let finalAcc = fNode acc node rule

            fChild (node :> IClause) rule
            |> Seq.fold (fun a struct (c, r) -> recurse a c r) finalAcc
        | ValueClauseC valueClause ->
            let finalAcc = fValueClause acc valueClause rule

            fChild (valueClause :> IClause) rule
            |> Seq.fold (fun a struct (c, r) -> recurse a c r) finalAcc
        | LeafC leaf -> fLeaf acc leaf rule
        | LeafValueC leafvalue -> fLeafValue acc leafvalue rule
        | CommentC comment -> fComment acc comment rule

    /// Don't share context between siblings
    let rec depthInfoService fNode fChild fLeaf fLeafValue fValueClause fComment (ctx: 'c) (acc: 'r) child rule : 'r =
        let recurse = depthInfoService fNode fChild fLeaf fLeafValue fValueClause fComment

        match child with
        | NodeC node ->
            let newCtx, finalAcc = fNode ctx acc node rule

            fChild (node :> IClause) rule
            |> Seq.fold (fun a struct (c, r) -> recurse newCtx a c r) finalAcc
        | ValueClauseC valueClause ->
            let newCtx, finalAcc = fValueClause ctx acc valueClause rule

            fChild (valueClause :> IClause) rule
            |> Seq.fold (fun a struct (c, r) -> recurse newCtx a c r) finalAcc
        | LeafC leaf -> fLeaf ctx acc leaf rule
        | LeafValueC leafvalue -> fLeafValue ctx acc leafvalue rule
        | CommentC comment -> fComment ctx acc comment rule

    let fNodeContextAugmenter fNode = //: 'a -> Node -> _ -> (RuleContext<Scope> * 'a) =
        let x ctx acc (node: Node) ((field, options): NewRule) =
            let newCtx =
                match options.pushScope with
                | Some ps ->
                    { ctx with
                        RuleContext.scopes = ctx.scopes.PushScopeReset ps }
                | None ->
                    match options.replaceScopes with
                    | Some rs ->
                        let newctx =
                            match rs.this, rs.froms with
                            | Some this, Some froms ->
                                { ctx with
                                    scopes =
                                        { ctx.scopes with
                                            Scopes = this :: ctx.scopes.PopScope
                                            From = froms
                                            FromDepth = FromPath.FixedSlots
                                            FromDepthStack = [] } }
                            | Some this, None ->
                                { ctx with
                                    scopes =
                                        { ctx.scopes with
                                            Scopes = this :: ctx.scopes.PopScope } }
                            | None, Some froms ->
                                { ctx with
                                    scopes =
                                        { ctx.scopes with
                                            From = froms
                                            FromDepth = FromPath.FixedSlots
                                            FromDepthStack = [] } }
                            | None, None -> ctx

                        match rs.root with
                        | Some root ->
                            { newctx with
                                scopes = { newctx.scopes with Root = root } }
                        | None -> newctx
                    | None ->
                        if
                            node.Key.StartsWith("event_target:", System.StringComparison.OrdinalIgnoreCase)
                            || node.Key.StartsWith("parameter:", System.StringComparison.OrdinalIgnoreCase)
                        then
                            { ctx with
                                scopes = ctx.scopes.PushScopeReset anyScope }
                        else
                            ctx

            let newCtx =
                match field with
                | NodeRule(ScopeField s, f) ->
                    let scope = newCtx.scopes
                    let key = node.Key.Trim('"')

                    let newCtx =
                        match changeScope.Invoke(false, true, links, valueTriggers, wildCardLinks, varSet, key, scope) with
                        | NewScope(newScopes, _, _) ->
                            { newCtx with scopes = newScopes }
                        | VarFound ->
                            { newCtx with
                                scopes = newCtx.scopes.PushScopeReset anyScope }
                        | _ -> newCtx

                    newCtx
                | _ -> newCtx //, (Some options, None, Some (NodeC node))

            let newCtx =
                { newCtx with
                    scopes = applyScopeContextOverride node newCtx.scopes }

            newCtx, fNode ctx acc node ((field, options))

        x
    let p =
        { varMap = varMap
          enumsMap = enums
          typesMap = types
          databaseObjectTypes = extendedConfigMetadata.databaseObjectTypes
          linkMap = links
          valueTriggerMap = valueTriggers
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

    let foldWithPos fLeaf fLeafValue fComment fNode fValueClause acc (pos: pos) (node: Node) (logicalpath: string) =
        let fChild (ctx, _) (node: IClause) ((field, options): NewRule) =
            let rules =
                match field with
                | NodeRule(_, rs) -> rs
                | _ -> [||]

            let subtypedrules =
                rules
                |> Array.collect (fun (r, o) ->
                    r
                    |> (function
                    | SubtypeRule(_, _, cfs) -> cfs
                    | x -> [| (r, o) |]))

            let expandedrules =
                subtypedrules
                |> Array.collect (function
                    | LeafRule(AliasField a, _), _ -> (rootRules.Aliases.TryFind a |> Option.defaultValue [||])
                    | NodeRule(AliasField a, _), _ -> (rootRules.Aliases.TryFind a |> Option.defaultValue [||])
                    | x -> [| x |])

            let childMatch =
                node.Nodes |> Seq.tryFind (fun c -> rangeContainsPos c.Position pos)

            let leafMatch =
                node.Leaves |> Seq.tryFind (fun l -> rangeContainsPos l.Position pos)

            let leafValueMatch =
                node.LeafValues |> Seq.tryFind (fun lv -> rangeContainsPos lv.Position pos)

            match childMatch, leafMatch, leafValueMatch with
            | Some c, _, _ ->
                match
                    expandedrules
                    |> Array.tryPick (function
                        | NodeRule(l, rs), o when FieldValidators.checkLeftField p Severity.Error ctx l c.KeyId ->
                            Some(l, rs, o)
                        | _ -> None)
                with
                | None ->
                    Some(NodeC c, (field, options))
                | Some(l, rs, o) -> Some(NodeC c, ((NodeRule(l, rs)), o))
            | _, Some leaf, _ ->
                match
                    expandedrules
                    |> Array.tryPick (function
                        | LeafRule(l, r), o when FieldValidators.checkLeftField p Severity.Error ctx l leaf.KeyId ->
                            Some(l, r, o)
                        | _ -> None)
                with
                | None -> Some(LeafC leaf, (field, options))
                | Some(l, rs, o) -> Some(LeafC leaf, ((LeafRule(l, rs)), o))
            | _, _, Some lv -> Some(LeafValueC lv, (field, options))
            | None, None, None -> None

        let childMatch =
            node.Nodes |> Seq.tryFind (fun c -> rangeContainsPos c.Position pos)
        let skiprootkey (skipRootKey: SkipRootKey) (n: Node) =
            match skipRootKey with
            | SpecificKey key -> n.Key == key
            | AnyKey -> true
            | MultipleKeys(keys, shouldMatch) -> (keys |> List.exists ((==) n.Key)) <> (not shouldMatch)

        let rec foldAtPosSkipRoot rs o (t: TypeDefinition) (skipRootKeyStack: SkipRootKey list) acc (n: Node) =
            match skipRootKeyStack with
            | [] ->
                if FieldValidators.typekeyfilter t n.Key n.KeyPrefix then
                    Some(
                        singleInfoService
                            fNode
                            fChild
                            fLeaf
                            fLeafValue
                            fValueClause
                            fComment
                            acc
                            (NodeC n)
                            ((NodeRule(TypeMarkerField(n.KeyId.lower, t), rs), o))
                    )
                else
                    None
            | head :: tail ->
                if skiprootkey head n then
                    node.Nodes
                    |> Seq.tryFind (fun c -> rangeContainsPos c.Position pos)
                    |> Option.bind (foldAtPosSkipRoot rs o t tail acc)
                else
                    None

        let resultForType (child: Node option) (typedef: TypeDefinition) =
            let typeRules =
                rootRules.TypeRules |> Array.filter (fun (name, _) -> name == typedef.name)

            match child with
            | Some c ->
                match typeRules, typedef.type_per_file with
                | [| (n, (NodeRule(l, rs), o)) |], false -> foldAtPosSkipRoot rs o typedef typedef.skipRootKey acc c
                | [| (n, (NodeRule(l, rs), o)) |], true ->
                    Some(
                        singleInfoService
                            fNode
                            fChild
                            fLeaf
                            fLeafValue
                            fValueClause
                            fComment
                            acc
                            (NodeC node)
                            ((NodeRule(TypeMarkerField(node.KeyId.lower, typedef), rs), o))
                    )
                | _ -> None
            | None ->
                match typeRules with
                | [| (n, (NodeRule(l, rs), o)) |] ->
                    Some(
                        singleInfoService
                            fNode
                            fChild
                            fLeaf
                            fLeafValue
                            fValueClause
                            fComment
                            acc
                            (NodeC node)
                            ((NodeRule(TypeMarkerField(node.KeyId.lower, typedef), rs), o))
                    )
                | _ -> None

        typedefs
        |> List.filter (fun t -> FieldValidatorsHelper.CheckPathDir(t.pathOptions, logicalpath))
        |> List.fold (fun acc t -> Option.orElseWith (fun () -> resultForType childMatch t) acc) None
    let getNodeAtPos (pos: pos) (entity: Entity) =
        let fLeaf (ctx, _) (leaf: Leaf) ((field, o): NewRule) = ctx, Some(LeafC leaf)
        let fLeafValue (ctx, _) (leafvalue: LeafValue) (field, o: Options) = ctx, Some(LeafValueC leafvalue)
        let fComment (ctx, _) c _ = ctx, Some(CommentC c)
        //TODO: Actually implement value clause
        let fValueClause (ctx, _) valueClause _ = ctx, Some(ValueClauseC valueClause)

        let fNode (ctx, _) (node: Node) ((field, options): NewRule) =
            let newCtx =
                match options.pushScope with
                | Some ps ->
                    { ctx with
                        RuleContext.scopes = ctx.scopes.PushScopeReset ps }
                | None ->
                    match options.replaceScopes with
                    | Some rs ->
                        let newctx =
                            match rs.this, rs.froms with
                            | Some this, Some froms ->
                                { ctx with
                                    scopes =
                                        { ctx.scopes with
                                            Scopes = this :: ctx.scopes.PopScope
                                            From = froms
                                            FromDepth = FromPath.FixedSlots
                                            FromDepthStack = [] } }
                            | Some this, None ->
                                { ctx with
                                    scopes =
                                        { ctx.scopes with
                                            Scopes = this :: ctx.scopes.PopScope } }
                            | None, Some froms ->
                                { ctx with
                                    scopes =
                                        { ctx.scopes with
                                            From = froms
                                            FromDepth = FromPath.FixedSlots
                                            FromDepthStack = [] } }
                            | None, None -> ctx

                        match rs.root with
                        | Some root ->
                            { newctx with
                                scopes = { newctx.scopes with Root = root } }
                        | None -> newctx
                    | None ->
                        if
                            node.Key.StartsWith("event_target:", System.StringComparison.OrdinalIgnoreCase)
                            || node.Key.StartsWith("parameter:", System.StringComparison.OrdinalIgnoreCase)
                        then
                            { ctx with
                                scopes = ctx.scopes.PushScopeReset anyScope }
                        else
                            ctx

            newCtx, (Some(NodeC node))
        // | _ -> newCtx, (Some options, None, Some (NodeC node))

        let childMatch =
            entity.entity.Nodes
            |> Seq.tryFind (fun c -> rangeContainsPos c.Position pos)
        // log "%O %A %A %A" pos pathDir (typedefs |> List.tryHead) (childMatch.IsSome)
        let ctx =
            match
                childMatch,
                typedefs
                |> List.tryFind (fun t -> FieldValidatorsHelper.CheckPathDir(t.pathOptions, entity.logicalpath))
            with
            | Some c, Some typedef ->
                let typerules =
                    rootRules.TypeRules
                    |> Array.choose (function
                        | name, r when name == typedef.name -> Some r
                        | _ -> None)

                let typeruleOptions =
                    match typerules |> Array.tryHead with
                    | Some(NodeRule(SpecificField(SpecificValue x), rs), o) when
                        (StringResource.stringManager.GetStringForID x.normal) == typedef.name
                        ->
                        if FieldValidators.typekeyfilter typedef c.Key c.KeyPrefix then
                            Some o
                        else
                            None
                    | _ -> None

                let pushScope, subtypes = ruleValidationService.TestSubType(typedef.subtypes, c)
                let ctx = getRulesContextFromOptions pushScope subtypes typeruleOptions
                { ctx with scopes = applyScopeContextOverride c ctx.scopes }

            | _, _ ->
                { subtypes = []
                  scopes = defaultContext
                  warningOnly = false }

        let ctx = ctx, None
        foldWithPos fLeaf fLeafValue fComment fNode fValueClause ctx pos entity.entity entity.logicalpath

    let getInfoAtPos (pos: pos) (entity: Entity) =
        let changeScopeInner (key: string) scope =
            match changeScope.Invoke(false, true, links, valueTriggers, wildCardLinks, varSet, key, scope) with
            | ValueFound rh -> rh
            | WrongScope(_, _, _, rh) -> rh
            | NewScope(_, _, rh) -> rh
            | _ -> None

        let changeValueScopeInner (key: string) scope =
            let key =
                let trimmed = key.Trim('"')
                let pipeIndex = trimmed.IndexOf('|')
                if pipeIndex >= 0 then trimmed.Substring(0, pipeIndex) else trimmed

            match changeScope.Invoke(false, true, links, valueTriggers, wildCardLinks, varSet, key, scope) with
            | ValueFound rh -> rh
            | WrongScope(_, _, _, rh) -> rh
            | NewScope(_, _, rh) -> rh
            | _ ->
                match enums.TryFind "static_values" with
                | Some(_, ss) ->
                    if ss.Contains key then
                        Some(EnumRef("static_values", key))
                    else
                        None
                | None -> None

        let trimPrefixedFieldValue (s: string) =
            let s = s.Trim('"')
            let colonIndex = s.IndexOf(':')

            if colonIndex > 0 && colonIndex + 1 < s.Length && s.[colonIndex + 1] <> '\\' && s.[colonIndex + 1] <> '/' then
                s.Substring(colonIndex + 1)
            else
                s

        let trimPrefixes (s: string) =
            let s = s.Trim('"')
            if s.StartsWith("text:", StringComparison.OrdinalIgnoreCase) then s.Substring(5)
            elif s.StartsWith("desc:", StringComparison.OrdinalIgnoreCase) then s.Substring(5)
            elif s.StartsWith("background:", StringComparison.OrdinalIgnoreCase) then s.Substring(11)
            elif s.StartsWith("icon:", StringComparison.OrdinalIgnoreCase) then s.Substring(5)
            else s

        let fLeaf (ctx: RuleContext, _) (leaf: Leaf) ((field, o): NewRule) =
            match o.typeHint, field with
            | Some(t, true), _ -> ctx, (Some o, Some(TypeRef(t, trimPrefixes leaf.Key)), Some(LeafC leaf))
            | Some(t, false), _ -> ctx, (Some o, Some(TypeRef(t, trimPrefixes leaf.ValueText)), Some(LeafC leaf))
            | _, LeafRule(_, PrefixedField(TypeField(TypeType.Simple t))) ->
                ctx, (Some o, Some(TypeRef(t, trimPrefixedFieldValue leaf.ValueText)), Some(LeafC leaf))
            | _, LeafRule(_, PrefixedField(LocalisationField _)) ->
                ctx, (Some o, Some(LocRef(trimPrefixedFieldValue leaf.ValueText)), Some(LeafC leaf))
            | _, LeafRule(_, TypeField(TypeType.Simple t)) ->
                ctx, (Some o, Some(TypeRef(t, trimPrefixes leaf.ValueText)), Some(LeafC leaf))
            | _, LeafRule(_, LocalisationField _) -> ctx, (Some o, Some(LocRef(trimPrefixes leaf.ValueText)), Some(LeafC leaf))
            | _, LeafRule(_, FilepathField(Some pre, Some ext)) ->
                ctx, (Some o, Some(FileRef(pre + (trimPrefixes leaf.ValueText) + ext)), Some(LeafC leaf))
            | _, LeafRule(PrefixedField(TypeField(TypeType.Simple t)), _) ->
                ctx, (Some o, Some(TypeRef(t, trimPrefixedFieldValue leaf.Key)), Some(LeafC leaf))
            | _, LeafRule(PrefixedField(LocalisationField _), _) ->
                ctx, (Some o, Some(LocRef(trimPrefixedFieldValue leaf.Key)), Some(LeafC leaf))
            | _, LeafRule(TypeField(TypeType.Simple t), _) ->
                ctx, (Some o, Some(TypeRef(t, trimPrefixes leaf.Key)), Some(LeafC leaf))
            | _, _ when leaf.Key = "inline_script" || leaf.Key = "script" ->
                let value = trimPrefixes leaf.ValueText
                ctx, (Some o, Some(FileRef("common/inline_scripts/" + value)), Some(LeafC leaf))
            | _, LeafRule(LocalisationField _, _) -> ctx, (Some o, Some(LocRef(trimPrefixes leaf.Key)), Some(LeafC leaf))
            | _, LeafRule(_, ScopeField _) ->
                ctx, (Some o, changeScopeInner leaf.ValueText ctx.scopes, Some(LeafC leaf))
            | _, LeafRule(_, ValueScopeField _) ->
                ctx, (Some o, changeValueScopeInner leaf.ValueText ctx.scopes, Some(LeafC leaf))
            | _, LeafRule(ScopeField _, _) -> ctx, (Some o, changeScopeInner leaf.Key ctx.scopes, Some(LeafC leaf))
            | _, LeafRule(ValueScopeField _, _) ->
                ctx, (Some o, changeValueScopeInner leaf.Key ctx.scopes, Some(LeafC leaf))
            | _ -> ctx, (Some o, None, Some(LeafC leaf))

        let fLeafValue (ctx, _) (leafvalue: LeafValue) (field, o: Options) =
            match o.typeHint, field with
            | Some(t, true), _ -> ctx, (Some o, Some(TypeRef(t, trimPrefixes leafvalue.Key)), Some(LeafValueC leafvalue))
            | _, LeafValueRule(PrefixedField(TypeField(TypeType.Simple t))) ->
                ctx, (Some o, Some(TypeRef(t, trimPrefixedFieldValue leafvalue.Key)), Some(LeafValueC leafvalue))
            | _, LeafValueRule(PrefixedField(LocalisationField _)) ->
                ctx, (Some o, Some(LocRef(trimPrefixedFieldValue leafvalue.Key)), Some(LeafValueC leafvalue))
            | _, LeafValueRule(TypeField(TypeType.Simple t)) ->
                ctx, (Some o, Some(TypeRef(t, trimPrefixes leafvalue.Key)), Some(LeafValueC leafvalue))
            | _, LeafValueRule(LocalisationField _) ->
                ctx, (Some o, Some(LocRef(trimPrefixes leafvalue.Key)), Some(LeafValueC leafvalue))
            | _ -> ctx, (Some o, None, Some(LeafValueC leafvalue))

        let fComment (ctx, _) _ _ = ctx, (None, None, None)
        //TODO: Actually implement value clause
        let fValueClause (ctx, _) _ _ = ctx, (None, None, None)

        let fNode (ctx, (_, res, resc)) (node: Node) ((field, options): NewRule) =
            let newCtx =
                match options.pushScope with
                | Some ps ->
                    { ctx with
                        RuleContext.scopes = ctx.scopes.PushScopeReset ps }
                | None ->
                    match options.replaceScopes with
                    | Some rs ->
                        let newctx =
                            match rs.this, rs.froms with
                            | Some this, Some froms ->
                                { ctx with
                                    scopes =
                                        { ctx.scopes with
                                            Scopes = this :: ctx.scopes.PopScope
                                            From = froms
                                            FromDepth = FromPath.FixedSlots
                                            FromDepthStack = [] } }
                            | Some this, None ->
                                { ctx with
                                    scopes =
                                        { ctx.scopes with
                                            Scopes = this :: ctx.scopes.PopScope } }
                            | None, Some froms ->
                                { ctx with
                                    scopes =
                                        { ctx.scopes with
                                            From = froms
                                            FromDepth = FromPath.FixedSlots
                                            FromDepthStack = [] } }
                            | None, None -> ctx

                        match rs.root with
                        | Some root ->
                            { newctx with
                                scopes = { newctx.scopes with Root = root } }
                        | None -> newctx
                    | None ->
                        if
                            node.Key.StartsWith("event_target:", System.StringComparison.OrdinalIgnoreCase)
                            || node.Key.StartsWith("parameter:", System.StringComparison.OrdinalIgnoreCase)
                        then
                            { ctx with
                                scopes = ctx.scopes.PushScopeReset anyScope }
                        else
                            ctx

            match options.typeHint, field with
            | Some(t, true), _ -> ctx, (Some options, Some(TypeRef(t, node.Key)), Some(NodeC node))
            | _, NodeRule(ScopeField s, f) ->
                let scope = newCtx.scopes
                let key = node.Key.Trim('"')

                let newCtx, rh =
                    match changeScope.Invoke(false, true, links, valueTriggers, wildCardLinks, varSet, key, scope) with
                    | NewScope(newScopes, _, rh) ->
                        // Keep the complete context so links that advance FROM retain
                        // the remaining chain for nested scope switches.
                        { newCtx with scopes = newScopes }, rh
                    | VarFound ->
                        // log "cs %A %A %A" s node.Key current
                        { newCtx with
                            scopes =
                                { newCtx.scopes with
                                    Scopes = anyScope :: newCtx.scopes.Scopes } },
                        None
                    | ValueFound rh -> newCtx, rh
                    | WrongScope(_, _, _, rh) -> newCtx, rh
                    | _ -> newCtx, None

                let newCtx =
                    { newCtx with
                        scopes = applyScopeContextOverride node newCtx.scopes }

                newCtx, (Some options, None, Some(NodeC node))
            | _, NodeRule(TypeMarkerField(_, { name = typename; nameField = None }), _) ->
                ctx, (Some options, Some(TypeRef(typename, node.Key)), Some(NodeC node))
            | _,
              NodeRule(TypeMarkerField(_,
                                       { name = typename
                                         nameField = Some namefield }),
                       _) ->
                let typevalue = node.TagText namefield
                ctx, (Some options, Some(TypeRef(typename, typevalue)), Some(NodeC node))
            | _, NodeRule(TypeField(TypeType.Simple t), _) ->
                ctx, (Some options, Some(TypeRef(t, node.Key)), Some(NodeC node))
            | _, NodeRule(LocalisationField _, _) -> ctx, (Some options, Some(LocRef(node.Key)), Some(NodeC node))
            | _, NodeRule(_, f) ->
                let newCtx =
                    { newCtx with
                        scopes = applyScopeContextOverride node newCtx.scopes }

                newCtx, (Some options, None, Some(NodeC node))
            | _ ->
                let newCtx =
                    { newCtx with
                        scopes = applyScopeContextOverride node newCtx.scopes }

                newCtx, (Some options, None, Some(NodeC node))

        let childMatch =
            entity.entity.Nodes
            |> Seq.tryFind (fun c -> rangeContainsPos c.Position pos)
        // log "%O %A %A %A" pos pathDir (typedefs |> List.tryHead) (childMatch.IsSome)
        let ctx =


            match
                childMatch,
                typedefs
                |> List.tryFind (fun t -> FieldValidatorsHelper.CheckPathDir(t.pathOptions, entity.logicalpath))
            with
            | Some c, Some typedef ->
                let typerules =
                    rootRules.TypeRules
                    |> Array.choose (function
                        | name, r when name == typedef.name -> Some r
                        | _ -> None)

                let typeruleOptions =
                    match typerules |> Array.tryHead with
                    | Some(NodeRule(SpecificField(SpecificValue x), rs), o) when
                        (StringResource.stringManager.GetStringForID x.normal) == typedef.name
                        ->
                        if FieldValidators.typekeyfilter typedef c.Key c.KeyPrefix then
                            Some o
                        else
                            None
                    | _ -> None

                let pushScope, subtypes = ruleValidationService.TestSubType(typedef.subtypes, c)
                let ctx = getRulesContextFromOptions pushScope subtypes typeruleOptions
                { ctx with scopes = applyScopeContextOverride c ctx.scopes }
            | _, _ ->
                { subtypes = []
                  scopes = defaultContext
                  warningOnly = false }

        let tryFindLeafAtPos (pos: pos) (root: Node) =
            let rec loop path (node: Node) =
                match node.Leaves |> Seq.tryFind (fun leaf -> rangeContainsPos leaf.Position pos) with
                | Some leaf -> Some(List.rev (node :: path), leaf)
                | None -> node.Nodes |> Seq.tryPick (loop (node :: path))

            loop [] root

        let tryFindParameterOwner (path: Node list) =
            path
            |> List.mapi (fun i node -> i, node)
            |> List.rev
            |> List.tryPick (fun (i, node) ->
                if i > 0 && String.Equals(node.Key, "parameters", StringComparison.OrdinalIgnoreCase) then
                    Some(path.[i - 1], i)
                else
                    None)

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

        let tryAliasParameterInfo (ruleCtx: RuleContext) =
            let rec tryRulesForPath (rules: NewRule array) (nodes: Node list) =
                match nodes with
                | [] -> Some rules
                | node :: rest ->
                    let noderules, _, _, _, nodeSpecificDict, _ = memoizeRules rules ruleCtx.subtypes
                    let found, specificRules = nodeSpecificDict.TryGetValue node.KeyId.lower

                    let candidates: seq<NewRule> =
                        if found then
                            seq {
                                yield! specificRules
                                yield! noderules
                            }
                        else
                            noderules :> seq<NewRule>

                    candidates
                    |> Seq.tryPick (function
                        | NodeRule(l, innerRules), _ when
                            FieldValidators.checkLeftField p Severity.Error ruleCtx l node.KeyId
                            ->
                            tryRulesForPath innerRules rest
                        | _ -> None)

            let tryLeafInfo (rules: NewRule array) (leaf: Leaf) =
                let _, leafrules, _, _, _, leafSpecificDict = memoizeRules rules ruleCtx.subtypes
                let found, specificRules = leafSpecificDict.TryGetValue leaf.KeyId.lower

                let candidates: seq<NewRule> =
                    if found then
                        seq {
                            yield! specificRules
                            yield! leafrules
                        }
                    else
                        leafrules :> seq<NewRule>

                candidates
                |> Seq.tryPick (function
                    | LeafRule(l, _), _ as rule when FieldValidators.checkLeftField p Severity.Error ruleCtx l leaf.KeyId ->
                        let result = fLeaf (ruleCtx, (None, None, None)) leaf rule

                        match result with
                        | _, (_, Some _, _) -> Some result
                        | _ -> None
                    | _ -> None)

            match aliasParamMarkers.Length, tryFindLeafAtPos pos entity.entity with
            | 0, _
            | _, None -> None
            | _, Some(path, leaf) ->
                match tryFindParameterOwner path with
                | None -> None
                | Some(owner, parameterIndex) ->
                    aliasParamMarkers
                    |> Seq.tryPick (fun (aliasName, selectorField) ->
                        let selectedAlias = owner.TagText selectorField

                        match String.IsNullOrWhiteSpace selectedAlias, trySelectedAliasRules aliasName selectedAlias with
                        | true, _
                        | _, None -> None
                        | false, Some rules ->
                            path
                            |> List.skip (parameterIndex + 1)
                            |> tryRulesForPath rules
                            |> Option.bind (fun rules -> tryLeafInfo rules leaf))

        let ruleCtx = ctx
        let ctx = ruleCtx, (None, None, None)
        let baseInfo = foldWithPos fLeaf fLeafValue fComment fNode fValueClause ctx pos entity.entity entity.logicalpath

        match baseInfo with
        | Some(_, (_, Some(TypeRef _), _))
        | Some(_, (_, Some(EnumRef _), _))
        | Some(_, (_, Some(FileRef _), _)) -> baseInfo
        | _ -> tryAliasParameterInfo ruleCtx |> Option.orElse baseInfo

    let foldCollect infoServiceFunction fLeaf fLeafValue fComment fNode fValueClause acc (node: Node) (path: string) =
        let ctx =
            { subtypes = []
              scopes = defaultContext
              warningOnly = false }

        let fChild (node: IClause) ((field, options): NewRule) =
            let rules =
                match field with
                | NodeRule(_, rs) -> rs
                | ValueClauseRule rs -> rs
                | _ -> [||]

            let noderules, leafrules, leafvaluerules, valueclauserules, nodeSpecificDict, leafSpecificDict =
                memoizeRules rules ctx.subtypes

            let inner (child: Child) =
                match child with
                | NodeC c ->
                    let keyId = c.KeyId
                    let found, value = nodeSpecificDict.TryGetValue keyId.lower

                    let rs =
                        if found then
                            Seq.append value noderules
                        else
                            upcast noderules

                    rs
                    |> Seq.choose (function
                        | NodeRule(l, rs), o ->
                            (if FieldValidators.checkLeftField p Severity.Error ctx l keyId then
                                 Some struct (NodeC c, ((NodeRule(l, rs)), o))
                             else
                                 None)
                        | _ -> None)
                | ValueClauseC vc ->
                    valueclauserules
                    |> Seq.choose (function
                        | ValueClauseRule rs, o -> Some struct (ValueClauseC vc, ((ValueClauseRule rs), o))
                        | _ -> None)
                | LeafC leaf ->
                    let keyId = leaf.KeyId
                    let found, value = leafSpecificDict.TryGetValue keyId.lower

                    let rs =
                        if found then
                            Seq.append value leafrules
                        else
                            upcast leafrules

                    rs
                    |> Seq.choose (function
                        | LeafRule(l, r), o ->
                            (if FieldValidators.checkLeftField p Severity.Error ctx l keyId then
                                 Some struct (LeafC leaf, ((LeafRule(l, r)), o))
                             else
                                 None)
                        | _ -> None)
                | LeafValueC leafvalue ->
                    let keyId = leafvalue.ValueId

                    leafvaluerules
                    |> Seq.choose (function
                        | LeafValueRule lv, o ->
                            (if FieldValidators.checkLeftField p Severity.Error ctx lv keyId then
                                 Some struct (LeafValueC leafvalue, ((LeafValueRule lv), o))
                             else
                                 None)
                        | _ -> None)
                | CommentC _ -> Seq.empty

            node.AllArray |> Seq.collect inner

        let skiprootkey (skipRootKey: SkipRootKey) (n: Node) =
            match skipRootKey with
            | SpecificKey key -> n.Key == key
            | AnyKey -> true
            | MultipleKeys(keys, shouldMatch) -> (keys |> List.exists ((==) n.Key)) <> (not shouldMatch)

        let infoServiceNode (typedef: TypeDefinition) rs o =
            (fun a (c: Node) ->
                let ctx =
                    let typerules =
                        match Map.tryFind (typedef.name.ToLowerInvariant()) typeRulesByName with
                        | Some rules -> rules :> seq<_>
                        | None -> Seq.empty
                    let typeruleOptions =
                        match typerules |> Seq.tryHead with
                        | Some(NodeRule(SpecificField(SpecificValue x), rs), o) when
                            (StringResource.stringManager.GetStringForID x.normal) == typedef.name
                            ->
                            if FieldValidators.typekeyfilter typedef c.Key c.KeyPrefix then
                                Some o
                            else
                                None
                        | _ -> None

                    let pushScope, subtypes = ruleValidationService.TestSubType(typedef.subtypes, c)
                    let ctx = getRulesContextFromOptions pushScope subtypes typeruleOptions
                    { ctx with scopes = applyScopeContextOverride c ctx.scopes }

                infoServiceFunction
                    fNode
                    fChild
                    fLeaf
                    fLeafValue
                    fValueClause
                    fComment
                    ctx
                    a
                    (NodeC c)
                    (NodeRule(TypeMarkerField(c.KeyId.lower, typedef), rs), o))

        let pathFilteredTypes =
            typedefs
            |> List.filter (fun t -> FieldValidatorsHelper.CheckPathDir(t.pathOptions, path))

        let rec infoServiceSkipRoot rs o (t: TypeDefinition) (skipRootKeyStack: SkipRootKey list) acc (n: Node) =
            match skipRootKeyStack with
            | [] ->
                if FieldValidators.typekeyfilter t n.Key n.KeyPrefix then
                    infoServiceNode t rs o acc n
                else
                    acc
            | head :: tail ->
                if skiprootkey head n then
                    n.Nodes |> Seq.fold (infoServiceSkipRoot rs o t tail) acc
                else
                    acc

        let infoServiceBase (n: Node) acc (t: TypeDefinition) =
            let typerules =
                rootRules.TypeRules |> Array.filter (fun (name, _) -> name == t.name)

            match typerules, t.type_per_file with
            | [| (_, (NodeRule(_, rs), o)) |], false ->
                n.Nodes |> Seq.fold (infoServiceSkipRoot rs o t t.skipRootKey) acc
            | [| (_, (NodeRule(_, rs), o)) |], true -> infoServiceSkipRoot rs o t t.skipRootKey acc n
            | _ -> acc

        pathFilteredTypes |> List.fold (infoServiceBase node) acc


    let getTypesInEntity () = // (entity : Entity) =
        let changeValueScopeInner (keyId: StringTokens) scope =
            let metadata = stringManager.GetMetadataForID keyId.lower
            let key = stringManager.GetStringForIDs keyId

            let key =
                match metadata.containsPipe with
                | true -> key.Split('|', 2)[0]
                | _ -> key

            match changeScope.Invoke(false, true, links, valueTriggers, wildCardLinks, varSet, key, scope) with
            | ValueFound rh -> rh
            | WrongScope(_, _, _, rh) -> rh
            | NewScope(_, _, rh) -> rh
            | _ ->
                match enums.TryFind "static_values" with
                | Some(_, trie) ->
                    if trie.Contains key then
                        Some(EnumRef("static_values", key))
                    else
                        None
                | None -> None

        let createReferenceDetails name pos isOutgoing referenceLabel refType assocType =
            { ReferenceDetails.name = name
              originalValue = name
              position = pos
              isOutgoing = isOutgoing
              referenceLabel = referenceLabel
              referenceType = refType
              associatedType = assocType }

        let createReferenceDetailsValue name originalValue pos isOutgoing referenceLabel refType assocType =
            { ReferenceDetails.name = name
              originalValue = originalValue
              position = pos
              isOutgoing = isOutgoing
              referenceLabel = referenceLabel
              referenceType = refType
              associatedType = assocType }

        let res = ConcurrentDictionary<string, ResizeArray<ReferenceDetails>>()
        let lookup = res.GetAlternateLookup<ReadOnlySpan<char>>()

        let addReferenceDetails (s: string) token position isOutgoing referenceLabel referenceType assocType =
            let typename = s.AsSpan().SplitFirst('.')
            let result, resizeArray = lookup.TryGetValue(typename)

            if result then
                resizeArray.Add(createReferenceDetails token position isOutgoing referenceLabel referenceType assocType)
                res
            else
                let newArr = ResizeArray<ReferenceDetails>(4)
                newArr.Add(createReferenceDetails token position isOutgoing referenceLabel referenceType assocType)
                res.TryAdd(typename.ToString(), newArr) |> ignore

                res

        let addReferenceDetailsValue
            (s: string)
            typeValue
            token
            position
            isOutgoing
            referenceLabel
            referenceType
            assocType
            =
            let typename = s.AsSpan().SplitFirst('.')
            let result, resizeArray = lookup.TryGetValue(typename)

            if result then
                resizeArray.Add(
                    createReferenceDetailsValue
                        (stringManager.InternIdentifierToken typeValue)
                        token
                        position
                        isOutgoing
                        referenceLabel
                        referenceType
                        assocType
                )

                res
            else
                let newArr = ResizeArray<ReferenceDetails>(4)

                newArr.Add(
                    createReferenceDetailsValue
                        (stringManager.InternIdentifierToken typeValue)
                        token
                        position
                        isOutgoing
                        referenceLabel
                        referenceType
                        assocType
                )

                res.TryAdd(typename.ToString(), newArr) |> ignore
                res

        let fLeaf _ (leaf: Leaf) ((field, options): NewRule) =
            let isOutgoing, referenceLabel =
                options.referenceDetails
                |> Option.map (fun (b, s) -> b, Some s)
                |> Option.defaultValue (true, None)

            let assocType = options.typeHint |> Option.map fst

            match field with
            | LeafRule(_, TypeField(TypeType.Simple t)) ->
                addReferenceDetails
                    t
                    leaf.ValueId
                    leaf.Position
                    isOutgoing
                    referenceLabel
                    ReferenceType.TypeDef
                    assocType
            | LeafRule(_, TypeField(TypeType.Complex(_, t, _))) ->
                addReferenceDetails
                    t
                    leaf.ValueId
                    leaf.Position
                    isOutgoing
                    referenceLabel
                    ReferenceType.TypeDefFuzzy
                    assocType
            | LeafRule(_, ValueScopeField _) ->
                let refHint = changeValueScopeInner leaf.ValueId Scopes.defaultContext

                match refHint with
                | Some(TypeRef(typeName, typeValue)) ->
                    addReferenceDetailsValue
                        typeName
                        typeValue
                        leaf.ValueId
                        leaf.Position
                        isOutgoing
                        referenceLabel
                        ReferenceType.TypeDef
                        assocType
                | _ -> res
            | LeafRule(TypeField(TypeType.Simple t), _) ->
                addReferenceDetails t leaf.KeyId leaf.Position isOutgoing referenceLabel ReferenceType.TypeDef assocType
            | LeafRule(TypeField(TypeType.Complex(_, t, _)), _) ->
                addReferenceDetails
                    t
                    leaf.KeyId
                    leaf.Position
                    isOutgoing
                    referenceLabel
                    ReferenceType.TypeDefFuzzy
                    assocType
            | _ -> res

        let fLeafValue _ (leafvalue: LeafValue) (field, options) =
            let isOutgoing, referenceLabel =
                options.referenceDetails
                |> Option.map (fun (b, s) -> b, Some s)
                |> Option.defaultValue (true, None)

            let assocType = options.typeHint |> Option.map fst

            match field with
            | LeafValueRule(TypeField(TypeType.Simple t)) ->
                addReferenceDetails
                    t
                    leafvalue.ValueId
                    leafvalue.Position
                    isOutgoing
                    referenceLabel
                    ReferenceType.TypeDef
                    assocType
            | _ -> res

        let fComment _ _ _ = res

        let fNode _ (node: Node) ((field, options): NewRule) =
            let isOutgoing, referenceLabel =
                options.referenceDetails
                |> Option.map (fun (b, s) -> b, Some s)
                |> Option.defaultValue (true, None)

            let assocType = options.typeHint |> Option.map fst

            match field with
            | NodeRule(TypeField(TypeType.Simple t), _) ->
                addReferenceDetails t node.KeyId node.Position isOutgoing referenceLabel ReferenceType.TypeDef assocType
            | NodeRule(TypeField(TypeType.Complex(_, t, _)), _) ->
                addReferenceDetails
                    t
                    node.KeyId
                    node.Position
                    isOutgoing
                    referenceLabel
                    ReferenceType.TypeDefFuzzy
                    assocType
            | NodeRule(JominiGuiField, _) ->
                let typename = "gui_type"

                addReferenceDetails
                    typename
                    node.KeyId
                    node.Position
                    isOutgoing
                    referenceLabel
                    ReferenceType.TypeDef
                    assocType
            | _ -> res

        let fValueClause _ _ _ = res

        fLeaf, fLeafValue, fComment, fNode, fValueClause, res

    let getDefVarInEntity = //(ctx : Collections.Map<string, (string * range) list>) (entity : Entity) =
        let getVariableFromString (v: string) (s: string) =
            let first = s.AsSpan().SplitFirst('@')

            if v = "variable" then
                let range = first.Split('.').Last()
                let struct (start, length) = range.GetOffsetAndLength(first.Length)
                first.Slice(start, length).SplitFirst('?').ToString()
            else
                first.ToString()

        let fLeaf (res: Collections.Map<string, ResizeArray<string * range>>) (leaf: Leaf) ((field, _): NewRule) =
            match field with
            | LeafRule(_, VariableSetField v) ->
                res
                |> (fun m ->
                    m.Add(
                        v,
                        (m.TryFind(v)
                         |> Option.defaultValue (new ResizeArray<_>())
                         |> (fun i ->
                             i.Add((getVariableFromString v leaf.ValueText, leaf.Position))
                             i))
                    ))
            | LeafRule(VariableSetField v, _) ->
                res
                |> (fun m ->
                    m.Add(
                        v,
                        (m.TryFind(v)
                         |> Option.defaultValue (new ResizeArray<_>())
                         |> (fun i ->
                             i.Add((getVariableFromString v leaf.Key, leaf.Position))
                             i))
                    ))
            | _ -> res

        let fLeafValue (res: Collections.Map<string, ResizeArray<string * range>>) (leafvalue: LeafValue) (field, _) =
            match field with
            | LeafValueRule(VariableSetField v) ->
                res
                |> (fun m ->
                    m.Add(
                        v,
                        (m.TryFind(v)
                         |> Option.defaultValue (new ResizeArray<_>())
                         |> (fun i ->
                             i.Add((getVariableFromString v leafvalue.ValueText, leafvalue.Position))
                             i))
                    ))
            | _ -> res

        let fNode (res: Collections.Map<string, ResizeArray<string * range>>) (node: Node) ((field, option): NewRule) =
            match field with
            | NodeRule(VariableSetField v, _) ->
                res
                |> (fun m ->
                    m.Add(
                        v,
                        (m.TryFind(v)
                         |> Option.defaultValue (new ResizeArray<_>())
                         |> (fun i ->
                             i.Add((getVariableFromString v node.Key, node.Position))
                             i))
                    ))
            | _ -> res

        let fComment res _ _ = res
        let fValueClause res _ _ = res

        fLeaf, fLeafValue, fComment, fNode, fValueClause, Map.empty

    let getSavedScopesInEntity = //(ctx : Collections.Map<string, (string * range) list>) (entity : Entity) =
        let isEventTargetVariable variable =
            variable == "event_target" || variable == "global_event_target"

        let fLeaf (ctx: RuleContext) (res: ResizeArray<string * range * Scope>) (leaf: Leaf) ((field, _): NewRule) =
            match field with
            | LeafRule(_, VariableSetField variable) when isEventTargetVariable variable ->
                res.Add((leaf.ValueText, leaf.Position, ctx.scopes.CurrentScope))
            | LeafRule(VariableSetField variable, _) when isEventTargetVariable variable ->
                res.Add((leaf.Key, leaf.Position, ctx.scopes.CurrentScope))
            | _ -> ()

            res

        let fLeafValue (ctx: RuleContext) (res: ResizeArray<string * range * Scope>) (leafvalue: LeafValue) (field, _) =
            match field with
            | LeafValueRule(VariableSetField variable) when isEventTargetVariable variable ->
                res.Add(leafvalue.ValueText, leafvalue.Position, ctx.scopes.CurrentScope)
            | _ -> ()

            res

        let fNode
            (ctx: RuleContext)
            (res: ResizeArray<string * range * Scope>)
            (node: Node)
            ((field, option): NewRule)
            =
            match field with
            | NodeRule(VariableSetField variable, _) when isEventTargetVariable variable ->
                res.Add(node.Key, node.Position, ctx.scopes.CurrentScope)
            | _ -> ()

            res

        let fComment _ res _ _ = res
        let fValueClause _ res _ _ = res

        fLeaf, fLeafValue, fComment, fNode, fValueClause, (fun () -> new ResizeArray<_>())

    let getEffectsInEntity = //(ctx) (entity : Entity) =
        let fLeaf res (leaf: Leaf) ((field, _): NewRule) = res
        let fLeafValue res (leafvalue: LeafValue) (field, _) = res

        let fNode (res: Node list, finished: bool) (node: Node) ((field, option): NewRule) =
            match finished, field with
            | false, NodeRule(_, rs) when
                rs
                |> Array.exists (function
                    | LeafRule(AliasField "effect", _), _ -> true
                    | _ -> false)
                ->
                node :: res, true
            | _ -> res, false

        let fComment res _ _ = res
        let fValueClause res (valueclause: ValueClause) ((field, option): NewRule) = res

        fLeaf, fLeafValue, fComment, fNode, fValueClause, ([], false)

    let getTriggersInEntity = //(ctx) (entity : Entity) =
        let fLeaf res (leaf: Leaf) ((field, _): NewRule) = res
        let fLeafValue res (leafvalue: LeafValue) (field, _) = res

        let fNode (res: Node list, finished: bool) (node: Node) ((field, option): NewRule) =
            // TODO: Consider adding a case for "non-trigger rule after trigger rule" to reset for inner
            match finished, field with
            | false, NodeRule(_, rs) when
                rs
                |> Array.exists (function
                    | LeafRule(AliasField "trigger", _), _ -> true
                    | _ -> false)
                ->
                node :: res, true
            | false, _ -> res, false
            | true, _ -> res, true

        let fValueClause res (valueclause: ValueClause) ((field, option): NewRule) = res
        let fComment res _ _ = res

        fLeaf, fLeafValue, fComment, fNode, fValueClause, ([], false)

    let augmentFolder (fLeaf, fLeafValue, fComment, fNode, fValueClause, acc) =
        let fNode = fNodeContextAugmenter fNode
        fLeaf, fLeafValue, fComment, fNode, fValueClause, acc

    let allFolds entity =
        let fLeaf, fLeafValue, fComment, fNode, fValueClause, ctx =
            Test.mergeFolds getTriggersInEntity getEffectsInEntity
            |> Test.mergeFolds getDefVarInEntity
            |> Test.mergeFolds (getTypesInEntity ())

        let types, (defvars, (effects, triggers)) =
            foldCollect infoService fLeaf fLeafValue fComment fNode fValueClause ctx entity.entity entity.logicalpath

        let fLeaf, fLeafValue, fComment, fNode, fValueClause, ctx = getSavedScopesInEntity
        let fValueClause = (fun c r vc rul -> c, fValueClause c r vc rul)

        let eventtargets =
            foldCollect
                depthInfoService
                fLeaf
                fLeafValue
                fComment
                (fNodeContextAugmenter fNode)
                fValueClause
                (ctx ())
                entity.entity
                entity.logicalpath

        (types, defvars, triggers, effects, eventtargets)

    let singleFold (fLeaf, fLeafValue, fComment, fNode, fValueClause, ctx) entity =
        foldCollect infoService fLeaf fLeafValue fComment fNode fValueClause ctx entity.entity entity.logicalpath
    // Try building a specialized fold which builds a single array instead of folding

    let singleDepthFold (fLeaf, fLeafValue, fComment, fNode, fValueClause, ctx) entity =
        foldCollect depthInfoService fLeaf fLeafValue fComment fNode fValueClause ctx entity.entity entity.logicalpath

    let getSavedScopesInEntityFolder entity =
        let fLeaf, fLeafValue, fComment, fNode, fValueClause, ctx = getSavedScopesInEntity
        let fValueClause = (fun c r vc rul -> c, fValueClause c r vc rul)

        foldCollect
            depthInfoService
            fLeaf
            fLeafValue
            fComment
            (fNodeContextAugmenter fNode)
            fValueClause
            (ctx ())
            entity.entity
            entity.logicalpath

    let semanticSignatureForEntity entity =
        let variables = singleFold getDefVarInEntity entity
        let savedTargets = getSavedScopesInEntityFolder entity
        seq {
            for pair in variables do
                let kind = pair.Key
                let values = pair.Value
                for value, _ in values do
                    yield "variable\u001f" + kind + "\u001f" + value
            for name, _, scope in savedTargets do
                yield "event_target\u001f" + name + "\u001f" + scope.ToString()
        }
        |> Seq.distinct
        |> Seq.sort
        |> Seq.toArray

    let validateLocalisationFromTypes (entity: Entity) =
        let containsTypeValue (typeName: string) (value: string) =
            match types.TryGetValue typeName with
            | true, values -> values.Contains value
            | false, _ ->
                // Rule/type names are normally identical. Preserve the previous
                // case-insensitive behaviour for custom configs with mixed casing.
                types
                |> Seq.exists (fun pair -> pair.Key == typeName && pair.Value.Contains value)

        let fLeaf (res: ValidationResult) (leaf: Leaf) ((field, _): NewRule) =
            match field with
            | LeafRule(_, TypeField(TypeType.Simple t)) ->
                let value = leaf.ValueText

                if containsTypeValue t value then
                    (FieldValidators.validateTypeLocalisation typedefs invertedTypeMap.Value localisation t value leaf)
                    <&&> res
                else
                    res
            | LeafRule(TypeField(TypeType.Simple t), _) ->
                let value = leaf.Key

                if containsTypeValue t value then
                    (FieldValidators.validateTypeLocalisation typedefs invertedTypeMap.Value localisation t value leaf)
                    <&&> res
                else
                    res
            | LeafRule(LocalisationField(synced, isInline), _) ->
                FieldValidators.checkLocalisationField
                    p.processLocalisation
                    p.validateLocalisation
                    defaultContext
                    p.localisation
                    p.defaultLocalisation
                    p.defaultLang
                    synced
                    isInline
                    leaf.KeyId
                    leaf
                    res
            | _ -> res

        let fLeafValue (res: ValidationResult) (leafvalue: LeafValue) (field, _) =
            match field with
            | LeafValueRule(TypeField(TypeType.Simple t)) ->
                let value = leafvalue.ValueText

                if containsTypeValue t value then
                    (FieldValidators.validateTypeLocalisation typedefs invertedTypeMap.Value localisation t value leafvalue)
                    <&&> res
                else
                    res
            | _ -> res

        let fNode (res: ValidationResult) (node: Node) (field, _) =
            match field with
            | NodeRule(TypeField(TypeType.Simple t), _) ->
                let value = node.Key

                if containsTypeValue t value then
                    (FieldValidators.validateTypeLocalisation typedefs invertedTypeMap.Value localisation t value node)
                    <&&> res
                else
                    res
            | NodeRule(LocalisationField(synced, isInline), _) ->
                FieldValidators.checkLocalisationField
                    p.processLocalisation
                    p.validateLocalisation
                    defaultContext
                    p.localisation
                    p.defaultLocalisation
                    p.defaultLang
                    synced
                    isInline
                    node.KeyId
                    node
                    res
            | _ -> res

        let fComment res _ _ = res
        let fValueClause res _ _ = res

        let ctx = OK

        let res =
            foldCollect infoService fLeaf fLeafValue fComment fNode fValueClause ctx entity.entity entity.logicalpath

        res

    let referencedLocalisationKeys (entity: Entity) =
        let containsTypeValue (typeName: string) (value: string) =
            match types.TryGetValue typeName with
            | true, values -> values.Contains value
            | false, _ ->
                types
                |> Seq.exists (fun pair -> pair.Key == typeName && pair.Value.Contains value)

        let trimPrefixes (value: string) =
            let value = value.Trim('"')
            if value.StartsWith("text:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
            elif value.StartsWith("desc:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
            elif value.StartsWith("background:", StringComparison.OrdinalIgnoreCase) then value.Substring(11)
            elif value.StartsWith("icon:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
            else value

        let trimPrefixedValue (value: string) =
            let value = value.Trim('"')
            let colonIndex = value.IndexOf(':')
            if colonIndex > 0 && colonIndex + 1 < value.Length && value.[colonIndex + 1] <> '\\' && value.[colonIndex + 1] <> '/' then
                value.Substring(colonIndex + 1)
            else
                value

        let addKey (keys: Set<string>) key =
            if String.IsNullOrWhiteSpace key then keys else Set.add key keys

        let addTypeKeys keys typeName value =
            if containsTypeValue typeName value then
                FieldValidators.typeLocalisationKeys typedefs invertedTypeMap.Value typeName value
                |> Array.fold addKey keys
            else
                keys

        let fLeaf keys (leaf: Leaf) ((field, _): NewRule) =
            match field with
            | LeafRule(_, TypeField(TypeType.Simple typeName)) ->
                addTypeKeys keys typeName (trimPrefixes leaf.ValueText)
            | LeafRule(TypeField(TypeType.Simple typeName), _) ->
                addTypeKeys keys typeName (trimPrefixes leaf.Key)
            | LeafRule(_, PrefixedField(TypeField(TypeType.Simple typeName))) ->
                addTypeKeys keys typeName (trimPrefixedValue leaf.ValueText)
            | LeafRule(PrefixedField(TypeField(TypeType.Simple typeName)), _) ->
                addTypeKeys keys typeName (trimPrefixedValue leaf.Key)
            | LeafRule(_, LocalisationField _)
            | LeafRule(_, PrefixedField(LocalisationField _)) ->
                let value =
                    match field with
                    | LeafRule(_, PrefixedField(LocalisationField _)) -> trimPrefixedValue leaf.ValueText
                    | _ -> trimPrefixes leaf.ValueText
                addKey keys value
            | LeafRule(LocalisationField _, _)
            | LeafRule(PrefixedField(LocalisationField _), _) ->
                let value =
                    match field with
                    | LeafRule(PrefixedField(LocalisationField _), _) -> trimPrefixedValue leaf.Key
                    | _ -> trimPrefixes leaf.Key
                addKey keys value
            | _ -> keys

        let fLeafValue keys (leafValue: LeafValue) (field, _) =
            match field with
            | LeafValueRule(TypeField(TypeType.Simple typeName)) ->
                addTypeKeys keys typeName (trimPrefixes leafValue.ValueText)
            | LeafValueRule(PrefixedField(TypeField(TypeType.Simple typeName))) ->
                addTypeKeys keys typeName (trimPrefixedValue leafValue.ValueText)
            | LeafValueRule(LocalisationField _) -> addKey keys (trimPrefixes leafValue.ValueText)
            | LeafValueRule(PrefixedField(LocalisationField _)) ->
                addKey keys (trimPrefixedValue leafValue.ValueText)
            | _ -> keys

        let fNode keys (node: Node) (field, _) =
            match field with
            | NodeRule(TypeField(TypeType.Simple typeName), _) ->
                addTypeKeys keys typeName (trimPrefixes node.Key)
            | NodeRule(PrefixedField(TypeField(TypeType.Simple typeName)), _) ->
                addTypeKeys keys typeName (trimPrefixedValue node.Key)
            | NodeRule(LocalisationField _, _) -> addKey keys (trimPrefixes node.Key)
            | NodeRule(PrefixedField(LocalisationField _), _) -> addKey keys (trimPrefixedValue node.Key)
            | _ -> keys

        let fComment keys _ _ = keys
        let fValueClause keys _ _ = keys
        foldCollect infoService fLeaf fLeafValue fComment fNode fValueClause Set.empty entity.entity entity.logicalpath

    member _.GetInfo(pos: pos, entity: Entity) =
        (getInfoAtPos pos entity) |> Option.map (fun (p, e) -> p.scopes, e)

    member _.GetNode(pos: pos, entity: Entity) =
        (getNodeAtPos pos entity) |> Option.map (fun (p, n) -> n)

    member _.GetReferencedTypes(entity: Entity) = singleFold (getTypesInEntity ()) entity
    member _.GetDefinedVariables(entity: Entity) = singleFold getDefVarInEntity entity
    member _.GetSavedEventTargets(entity: Entity) = getSavedScopesInEntityFolder entity
    member _.GetTypeLocalisationErrors(entity: Entity) = validateLocalisationFromTypes entity
    member _.GetReferencedLocalisationKeys(entity: Entity) = referencedLocalisationKeys entity
    member _.GetSemanticSignature(entity: Entity) = semanticSignatureForEntity entity

    /// Force the lazy type-localisation inverted map. Called from staged prepare paths so
    /// the O(total type ids) build happens off the write lock instead of on the first
    /// write-locked validation.
    member _.WarmTypeLocalisationIndex() = invertedTypeMap.Force() |> ignore

    member _.GetEffectBlocks(entity: Entity) =
        (singleFold getEffectsInEntity entity), (singleFold getTriggersInEntity entity)

    member _.BatchFolds(entity: Entity) = allFolds entity
