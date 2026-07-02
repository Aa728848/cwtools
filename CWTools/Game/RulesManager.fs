namespace CWTools.Games

open System
open System.Collections.Generic
open System.Linq
open System.Text.RegularExpressions
open CWTools.Rules
open CWTools.Common
open CWTools.Utilities.Position
open FSharp.Collections.ParallelSeq
open CWTools.Process.Localisation
open CWTools.Process.Scopes
open CWTools.Process
open CWTools.Parser
open CWTools.Utilities.Utils
open CWTools.Utilities.Utils2
open CWTools.Rules.RulesHelpers
open System.IO
open System.Collections.Frozen
open CWTools.Parser.UtilityParser
open CWTools.Rules.RulesWrapper

type RulesSettings =
    { ruleFiles: (string * string) list
      validateRules: bool
      debugRulesOnly: bool
      debugMode: bool }

type LocalisationEmbeddedSettings =
    | Legacy of (string * Scope list) list * string list * (string * Scope list * Scope) list
    | Jomini of CWTools.Parser.DataTypeParser.JominiLocDataTypes

type EmbeddedSettings =
    { triggers: DocEffect list
      effects: DocEffect list
      embeddedFiles: (string * string) list
      modifiers: ActualModifier array
      cachedResourceData: (Resource * Entity) list
      localisationCommands: LocalisationEmbeddedSettings
      eventTargetLinks: EventTargetLink list
      cachedRuleMetadata: CachedRuleMetadata option
      featureSettings: FeatureSettings }

type RuleManagerSettings<'T, 'L when 'T :> ComputedData and 'L :> Lookup> =
    { rulesSettings: RulesSettings option
      useFormulas: bool
      stellarisScopeTriggers: bool
      parseScope: string -> Scope
      allScopes: Scope list
      anyScope: Scope
      scopeGroups: Collections.Map<string, Scope list>
      changeScope: ChangeScope
      defaultContext: ScopeContext
      defaultLang: Lang
      oneToOneScopesNames: string list
      loadConfigRulesHook: RootRule array -> 'L -> EmbeddedSettings -> RootRule array
      refreshConfigBeforeFirstTypesHook: 'L -> IResourceAPI<'T> -> EmbeddedSettings -> unit
      refreshConfigAfterFirstTypesHook: 'L -> IResourceAPI<'T> -> EmbeddedSettings -> unit
      refreshConfigAfterVarDefHook: 'L -> IResourceAPI<'T> -> EmbeddedSettings -> unit
      locFunctions:
          'L
              -> ((Lang * Collections.Map<string, CWTools.Localisation.Entry>
                  -> Lang * Collections.Map<string, LocEntry>) *
              (LocEntry -> ScopeContext -> CWTools.Validation.ValidationResult)) }

type RulesManager<'T, 'L when 'T :> ComputedData and 'L :> Lookup>
    (
        resources: IResourceAPI<'T>,
        lookup: 'L,
        settings: RuleManagerSettings<'T, 'L>,
        localisation: LocalisationManager<'T>,
        embeddedSettings: EmbeddedSettings,
        languages: Lang array,
        debugMode: bool
    ) =

    // Mutable shadow of the constructor's lookup: a staged full refresh temporarily
    // points this at a shallow clone so refreshConfig (and its hooks) mutate the clone,
    // while every external reader keeps seeing the untouched original until commit.
    let mutable lookup: 'L = lookup

    let addEmbeddedTypeDefData =
        match embeddedSettings.cachedRuleMetadata with
        | None -> id
        | Some md ->
            fun (newMap: Map<string, array<TypeDefInfo>>) ->
                Map.fold
                    (fun s k v ->
                        match Map.tryFind k s with
                        | Some v' -> Map.add k (Array.append v v') s
                        | None -> Map.add k v s)
                    newMap
                    md.typeDefs

    let addEmbeddedEnumDefData =
        match embeddedSettings.cachedRuleMetadata with
        | None -> id
        | Some md ->
            fun (newMap: Map<string, string * (string * range option) array>) ->
                let mdAdjusted =
                    md.enumDefs
                    |> Map.map (fun _ (s, sl) -> s, (sl |> Array.map (fun x -> x, None)))

                let res =
                    Map.fold
                        (fun s k (d, v) ->
                            match Map.tryFind k s with
                            | Some(d', v') -> Map.add k (d, Array.append v v') s
                            | None -> Map.add k (d, v) s)
                        newMap
                        mdAdjusted

                res
    // res |> Map.map (fun _ (s, sl) -> s, (sl |> List.map (fun x -> x, None)))

    let addEmbeddedVarDefData =
        match embeddedSettings.cachedRuleMetadata with
        | None -> id
        | Some md ->
            fun (newMap: Map<string, array<string * range>>) ->
                Map.fold
                    (fun s k v ->
                        match Map.tryFind k s with
                        | Some v' -> Map.add k (Array.append v v') s
                        | None -> Map.add k v s)
                    newMap
                    md.varDefs

    let addEmbeddedLoc (langs: Lang array) : (Lang * Set<string>) array -> (Lang * Set<string>) array =
        match embeddedSettings.cachedRuleMetadata with
        | None -> id
        | Some md ->
            fun (newList: (Lang * Set<string>) array) ->
                let newMap = newList |> Map.ofArray
                let oldList = md.loc |> Array.filter (fun (l, _) -> Array.contains l langs)
                let embeddedMap = oldList |> Map.ofArray

                let res =
                    Map.fold
                        (fun s k v ->
                            match Map.tryFind k s with
                            | Some v' -> Map.add k (Set.union v v') s
                            | None -> Map.add k v s)
                        newMap
                        embeddedMap

                res |> Map.toArray

    let addEmbeddedFiles =
        match embeddedSettings.cachedRuleMetadata with
        | None -> id
        | Some md ->
            fun (newSet: HashSet<string>) ->
                newSet.UnionWith(md.files)
                newSet

    let mutable simpleEnums = []
    let mutable complexEnums = []
    let mutable tempTypes = []
    let mutable tempValues = Map.empty

    let mutable tempTypeMap = [ ("", PrefixOptimisedStringSet()) ] |> Map.ofList

    let mutable tempEnumMap: FrozenDictionary<string, string * PrefixOptimisedStringSet> =
        FrozenDictionary.Empty

    let mutable rulesDataGenerated = false
    let mutable baseConfigRules: RootRule array = [||]


    let loadBaseConfig (rulesSettings: RulesSettings) =
        let rules, types, enums, complexenums, values, metadata =
            rulesSettings.ruleFiles
            |> List.filter (fun (fn, _) ->
                Path.GetExtension(fn.AsSpan()).Equals(".cwt", StringComparison.OrdinalIgnoreCase))
            |> RulesParser.parseConfigs
                settings.parseScope
                settings.allScopes
                settings.anyScope
                settings.scopeGroups
                settings.useFormulas
                settings.stellarisScopeTriggers
        baseConfigRules <- rules
        lookup.extendedConfigMetadata <- metadata
        // tempEffects <- updateScriptedEffects game rules
        // effects <- tempEffects
        // tempTriggers <- updateScriptedTriggers game rules
        // _triggers <- tempTriggers
        lookup.typeDefs <- types
        // let rulesWithMod = rules @ addModifiersWithScopes(game)
        let rulesPostHook = settings.loadConfigRulesHook rules lookup embeddedSettings

        if rulesSettings.debugMode then
            RulesConsistencyValidation.checkForUndefinedTypes rulesPostHook lookup.typeDefs
        // lookup.configRules <- rulesWithMod
        lookup.configRules <- rulesPostHook
        simpleEnums <- enums
        complexEnums <- complexenums
        tempTypes <- types
        tempValues <- values |> Map.ofList //|> List.map (fun (s, sl) -> s, (sl |> List.map (fun s2 -> s2, range.Zero))) |> Map.ofList
        rulesDataGenerated <- false
    // log (sprintf "Update config rules def: %i" timer.ElapsedMilliseconds); timer.Restart()

    let currentLoc () =
        addEmbeddedLoc languages localisation.localisationKeys

    let currentFiles () =
        addEmbeddedFiles(resources.GetFileNames().ToHashSet()).ToFrozenSet()

    let typeMapFromTypeDefInfo (typeDefInfo: Map<string, TypeDefInfo array>) =
        typeDefInfo
        |> Map.toSeq
        |> PSeq.map (fun (k, s) -> k, s |> Seq.map _.id |> createStringSet)
        |> Map.ofSeq

    let typeDefInfoForValidationFrom (typeDefInfo: Map<string, TypeDefInfo array>) =
        typeDefInfo
        |> Map.map (fun _ v ->
            v
            |> Array.choose (fun tdi ->
                if tdi.validate then
                    Some(struct (tdi.id, tdi.range))
                else
                    None))

    // The structures below only change on a full refreshConfig (or an explicit rules reload),
    // so rebuilding them on every incremental scripted-type commit is wasted work inside the
    // save path. All caches key on reference identity of their immutable sources: any real
    // change produces a new instance and therefore a cache miss.
    let mutable cachedRulesWrapperSource: obj = null
    let mutable cachedRulesWrapper: RulesWrapper option = None

    let rulesWrapperFor (rules: RootRule array) =
        match cachedRulesWrapper with
        | Some wrapper when Object.ReferenceEquals(cachedRulesWrapperSource, rules) -> wrapper
        | _ ->
            let wrapper = RulesWrapper(rules)
            cachedRulesWrapperSource <- box rules
            cachedRulesWrapper <- Some wrapper
            wrapper

    let mutable cachedVarMapSource: obj = null

    let mutable cachedVarMap: FrozenDictionary<string, PrefixOptimisedStringSet> =
        FrozenDictionary.Empty

    let currentVarMap () =
        if not (Object.ReferenceEquals(cachedVarMapSource, lookup.varDefInfo)) then
            cachedVarMap <-
                (lookup.varDefInfo
                 |> Map.toSeq
                 |> PSeq.map (fun (k, s) -> KeyValuePair(k, s |> Seq.map fst |> createStringSet)))
                    .ToFrozenDictionary()

            cachedVarMapSource <- box lookup.varDefInfo

        cachedVarMap

    let mutable cachedAliasKeyMapKey: (obj * obj * obj) voption = ValueNone

    let mutable cachedAliasKeyMap: Map<string, HashSet<CWTools.Utilities.StringToken>> =
        Map.empty

    let aliasKeyMapFor
        (rulesWrapper: RulesWrapper)
        (typeMapSource: Map<string, PrefixOptimisedStringSet>)
        (frozenTypeMap: FrozenDictionary<string, PrefixOptimisedStringSet>)
        =
        match cachedAliasKeyMapKey with
        | ValueSome(w, t, e) when
            Object.ReferenceEquals(w, rulesWrapper)
            && Object.ReferenceEquals(t, typeMapSource)
            && Object.ReferenceEquals(e, tempEnumMap)
            ->
            cachedAliasKeyMap
        | _ ->
            let result = computeAliasKeyMap rulesWrapper frozenTypeMap tempEnumMap
            cachedAliasKeyMapKey <- ValueSome(box rulesWrapper, box typeMapSource, box tempEnumMap)
            cachedAliasKeyMap <- result
            result

    let buildRuleValidationService rulesWrapper typeMap varMap loc files aliasKeyMap =
        let processLoc, validateLoc = settings.locFunctions lookup

        RuleValidationService(
            rulesWrapper,
            lookup.typeDefs,
            typeMap,
            tempEnumMap,
            varMap,
            loc,
            files,
            lookup.eventTargetLinksMap,
            lookup.valueTriggerMap,
            settings.anyScope,
            settings.changeScope,
            settings.defaultContext,
            settings.defaultLang,
            processLoc,
            validateLoc,
            extendedConfigMetadata = lookup.extendedConfigMetadata,
            ?aliasKeyMapOverride = aliasKeyMap
        )

    let buildServices rulesWrapper (typeMapSource: Map<string, PrefixOptimisedStringSet>) loc files =
        let typeMap = typeMapSource.ToFrozenDictionary()
        let varMap = currentVarMap ()
        let aliasKeyMap = aliasKeyMapFor rulesWrapper typeMapSource typeMap

        let dataTypes =
            embeddedSettings.localisationCommands
            |> function
                | Jomini dts -> dts
                | _ ->
                    { promotes = Map.empty
                      confidentFunctions = Map.empty
                      functions = Map.empty
                      dataTypes = Map.empty
                      dataTypeNames = Set.empty }

        let processLoc, validateLoc = settings.locFunctions lookup
        let globalScriptVariables = lookup.globalScriptedVariableNames

        let ruleValidationService =
            buildRuleValidationService rulesWrapper typeMap varMap loc files (Some aliasKeyMap)

        let infoService =
            InfoService(
                rulesWrapper,
                lookup.typeDefs,
                typeMap,
                tempEnumMap,
                varMap,
                loc,
                files,
                lookup.eventTargetLinksMap,
                lookup.valueTriggerMap,
                ruleValidationService,
                settings.changeScope,
                settings.defaultContext,
                settings.anyScope,
                settings.defaultLang,
                processLoc,
                validateLoc,
                extendedConfigMetadata = lookup.extendedConfigMetadata,
                aliasKeyMapOverride = aliasKeyMap
            )

        let completionService =
            CompletionService(
                rulesWrapper,
                lookup.typeDefs,
                typeMap,
                tempEnumMap,
                varMap,
                loc,
                files,
                lookup.eventTargetLinksMap,
                lookup.valueTriggerMap,
                globalScriptVariables,
                settings.changeScope,
                settings.defaultContext,
                settings.anyScope,
                settings.oneToOneScopesNames,
                settings.defaultLang,
                dataTypes,
                processLoc,
                validateLoc,
                extendedConfigMetadata = lookup.extendedConfigMetadata,
                aliasKeyMapOverride = aliasKeyMap
            )

        ruleValidationService, infoService, completionService

    let scriptedParameterPattern =
        Regex(@"\$([^$|]+)(?:\|([^$]*))?\$", RegexOptions.Compiled)

    let parameterName (text: string) =
        let pipeIndex = text.IndexOf('|')
        if pipeIndex >= 0 then text.Substring(0, pipeIndex) else text

    let normalizeParameterKey (key: string) =
        key.Trim().Trim('$') |> parameterName

    let replaceScriptedParameters (parameters: (string * string) seq) (text: string) =
        let values =
            parameters
            |> Seq.choose (fun (key, value) ->
                let name = normalizeParameterKey key
                if String.IsNullOrWhiteSpace name then None else Some(name, value))
            |> Map.ofSeq

        scriptedParameterPattern.Replace(
            text,
            MatchEvaluator(fun m ->
                let name = m.Groups.[1].Value
                match values |> Map.tryFind name with
                | Some value -> value
                | None when m.Groups.[2].Success -> m.Groups.[2].Value
                | None -> m.Value)
        )

    let replaceNodeScriptedParameters (parameters: (string * string) list) (node: Node) =
        let stringReplace = replaceScriptedParameters parameters

        let rec foldOverNode (node: Node) =
            node.Key <- stringReplace node.Key

            node.Leaves
            |> Seq.iter (fun (l: Leaf) ->
                l.Key <- stringReplace l.Key

                match l.Value with
                | Value.String s ->
                    l.Value <-
                        String(
                            stringReplace (s.GetString())
                            |> CWTools.Utilities.StringResource.stringManager.InternIdentifierToken
                        )
                | Value.QString s ->
                    l.Value <-
                        QString(
                            stringReplace (s.GetString())
                            |> CWTools.Utilities.StringResource.stringManager.InternIdentifierToken
                        )
                | _ -> ())

            node.LeafValues
            |> Seq.iter (fun (l: LeafValue) ->
                match l.Value with
                | Value.String s ->
                    l.Value <-
                        String(
                            stringReplace (s.GetString())
                            |> CWTools.Utilities.StringResource.stringManager.InternIdentifierToken
                        )
                | Value.QString s ->
                    l.Value <-
                        QString(
                            stringReplace (s.GetString())
                            |> CWTools.Utilities.StringResource.stringManager.InternIdentifierToken
                        )
                | _ -> ())

            node.Nodes |> Seq.iter foldOverNode

        foldOverNode node

    let mergeDefinedVariables (m: Map<string, (string * range) array>) (map: Map<string, ResizeArray<string * range>>) =
        Map.toList map
        |> List.fold
            (fun m2 (n, k) ->
                if Map.containsKey n m2 then
                    Map.add n (Array.append (k.ToArray()) m2[n]) m2
                else
                    Map.add n (k.ToArray()) m2)
            m

    let refreshConfig () =
        let timer = System.Diagnostics.Stopwatch()
        let endToEndTimer = System.Diagnostics.Stopwatch()
        timer.Start()
        endToEndTimer.Start()
        let rulesWrapper = rulesWrapperFor lookup.configRules

        // Materialize all entities once to avoid repeated Seq creation (5+ calls previously)
        let allEntitiesList = resources.AllEntities() |> Seq.toList

        /// Enums
        let complexEnumDefs =
            getEnumsFromComplexEnums complexEnums (allEntitiesList |> Seq.map structFst)

        let allEnums = simpleEnums @ complexEnumDefs

        let newEnumDefs =
            allEnums
            |> Seq.map (fun e -> (e.key, (e.description, e.valuesWithRange)))
            |> Map.ofSeq

        lookup.enumDefs <- addEmbeddedEnumDefData newEnumDefs

        settings.refreshConfigBeforeFirstTypesHook lookup resources embeddedSettings

        tempEnumMap <-
            (lookup.enumDefs
             |> Map.toSeq
             |> PSeq.map (fun (k, (d, s)) -> KeyValuePair(k, (d, s |> Array.map fst |> createStringSet))))
                .ToFrozenDictionary()

        /// First pass type defs
        let loc = currentLoc ()
        // log "Refresh rule caches time: %i" timer.ElapsedMilliseconds; timer.Restart()
        let files = currentFiles ()
        // log "Refresh rule caches time: %i" timer.ElapsedMilliseconds; timer.Restart()
        // log "Refresh rule caches time: %i" timer.ElapsedMilliseconds; timer.Restart()

        let refreshTypeInfo () =
            let emptyVarMap: FrozenDictionary<string, PrefixOptimisedStringSet> = FrozenDictionary.Empty

            let tempRuleValidationService =
                buildRuleValidationService
                    rulesWrapper
                    (tempTypeMap.ToFrozenDictionary())
                    emptyVarMap
                    loc
                    files
                    None

            let allEntities = allEntitiesList |> Seq.map structFst
            let typeDefInfo =
                getTypesFromDefinitions (Some tempRuleValidationService) tempTypes allEntities

            lookup.typeDefInfo <- addEmbeddedTypeDefData typeDefInfo // |> Map.map (fun _ v -> v |> List.map (fun (_, t, r) -> (t, r)))

            typeMapFromTypeDefInfo lookup.typeDefInfo

        logDiag $"Pre-refresh types time: %0.3f{float timer.ElapsedMilliseconds / 1000.0}"
        timer.Restart()
        let mutable i = 0
        let mutable beforeCount = tempTypeMap.Values |> Seq.sumBy _.IdCount

        let step () =
            //log "%A" current
            i <- i + 1
            //TODO: Only refresh the types which have subtypes that depend on other types
            tempTypeMap <- refreshTypeInfo ()
            logDiag $"Refresh types time: %0.3f{float timer.ElapsedMilliseconds / 1000.0}"
            timer.Restart()
            let afterCount = tempTypeMap.Values |> Seq.sumBy _.IdCount
            let complete = beforeCount = afterCount || i > 5
            beforeCount <- afterCount
            complete

        // TODO check this actually stops early
        while not (step ()) do
            ()

        let emptyVarMap: FrozenDictionary<string, PrefixOptimisedStringSet> = FrozenDictionary.Empty

        let tempRuleValidationService =
            buildRuleValidationService
                rulesWrapper
                (tempTypeMap.ToFrozenDictionary())
                emptyVarMap
                loc
                files
                None

        lookup.typeDefInfoForValidation <- typeDefInfoForValidationFrom lookup.typeDefInfo

        settings.refreshConfigAfterFirstTypesHook lookup resources embeddedSettings

        tempTypeMap <- typeMapFromTypeDefInfo lookup.typeDefInfo

        let processLoc, validateLoc = settings.locFunctions lookup

        let tempInfoService =
            InfoService(
                rulesWrapper,
                lookup.typeDefs,
                tempTypeMap.ToFrozenDictionary(),
                tempEnumMap,
                FrozenDictionary.Empty,
                loc,
                files,
                lookup.eventTargetLinksMap,
                lookup.valueTriggerMap,
                tempRuleValidationService,
                settings.changeScope,
                settings.defaultContext,
                settings.anyScope,
                settings.defaultLang,
                processLoc,
                validateLoc,
                extendedConfigMetadata = lookup.extendedConfigMetadata
            )


        //let infoService = tempInfoService
        // game.InfoService <- Some tempInfoService
        if not rulesDataGenerated then
            resources.ForceRulesDataGenerate()
            rulesDataGenerated <- true
        else
            ()

        let predefValues =
            tempValues
            |> Map.map (fun k vs -> (expandPredefinedValues tempTypeMap lookup.enumDefs vs))
            |> Map.toList
            |> List.map (fun (s, sl) -> s, (sl |> Seq.map (fun s2 -> s2, range.Zero) |> Array.ofSeq))
            |> Map.ofList

        let results =
            allEntitiesList
            |> PSeq.map (fun struct (e, l) ->
                (l.Force().Definedvariables
                 |> (Option.defaultWith (fun () -> tempInfoService.GetDefinedVariables e))))
            |> Seq.fold mergeDefinedVariables predefValues

        let collectExpandedScriptedDefinedVariables () =
            let entityMap =
                allEntitiesList
                |> Seq.map (fun struct (e, d) -> e.filepath, struct (e, d))
                |> Map.ofSeq

            let rec findNodeAtPosition (node: Node) (pos: range) =
                if node.Position.Equals pos then
                    Some node
                else
                    node.Nodes
                    |> Seq.tryFind (fun n -> rangeContainsRange n.Position pos)
                    |> Option.bind (fun child -> findNodeAtPosition child pos)

            let findEntityNode (pos: range) =
                entityMap
                |> Map.tryFind pos.FileName
                |> Option.bind (fun struct (e, _) -> findNodeAtPosition e.entity pos |> Option.map (fun n -> e, n))

            let lower (s: string) = s.ToLowerInvariant()

            let scriptedDefinitions =
                lookup.typeDefInfo
                |> Map.tryFind "scripted_effect"
                |> Option.defaultValue [||]
                |> Array.choose (fun se ->
                    findEntityNode se.range
                    |> Option.map (fun (entity, node) -> lower se.id, (entity, node)))
                |> Map.ofArray

            if Map.isEmpty scriptedDefinitions then
                Seq.empty
            else
                let extractCallParams (callNode: Node) =
                    callNode.Values |> List.map (fun l -> "$" + l.Key + "$", l.ValueText)

                let findCallParams (pos: range) =
                    findEntityNode pos |> Option.map (snd >> extractCallParams) |> Option.defaultValue []

                let rec findNestedCalls (node: Node) =
                    let leafCalls =
                        node.Values
                        |> List.choose (fun l ->
                            let key = lower l.Key
                            if Map.containsKey key scriptedDefinitions then Some(l.Key, []) else None)

                    let nodeCalls =
                        node.Nodes
                        |> Seq.choose (fun n ->
                            let key = lower n.Key
                            if Map.containsKey key scriptedDefinitions then Some(n.Key, extractCallParams n) else None)
                        |> List.ofSeq

                    let childCalls =
                        node.Nodes |> Seq.collect findNestedCalls |> List.ofSeq

                    leafCalls @ nodeCalls @ childCalls

                let canonicalParams parameters =
                    parameters
                    |> List.sortBy fst
                    |> List.map (fun (k, v) -> k + "=" + v)
                    |> String.concat ";"

                let onlyConcreteValues (definedVariables: Map<string, ResizeArray<string * range>>) =
                    definedVariables
                    |> Map.toSeq
                    |> Seq.choose (fun (name, values) ->
                        let concrete =
                            values
                            |> Seq.filter (fun (value, _) -> value.IndexOf('$') < 0)
                            |> ResizeArray

                        if concrete.Count = 0 then None else Some(name, concrete))
                    |> Map.ofSeq

                let visited = HashSet<string>()

                let rec collectFromScriptedEffect depth name parameters =
                    if depth > 12 then
                        []
                    else
                        let nameKey = lower name
                        let visitedKey = nameKey + "|" + canonicalParams parameters

                        if not (visited.Add visitedKey) then
                            []
                        else
                            match Map.tryFind nameKey scriptedDefinitions with
                            | None -> []
                            | Some(definitionEntity, definitionNode) ->
                                let expandedNode = STLProcess.cloneNode definitionNode
                                replaceNodeScriptedParameters parameters expandedNode

                                let rootNode = Node("root")
                                rootNode.AllArray <- [| NodeC expandedNode |]

                                let expandedEntity =
                                    { definitionEntity with
                                        rawEntity = rootNode
                                        entity = rootNode }

                                let direct =
                                    tempInfoService.GetDefinedVariables expandedEntity
                                    |> onlyConcreteValues

                                let nested =
                                    findNestedCalls expandedNode
                                    |> List.collect (fun (nestedName, nestedParams) ->
                                        collectFromScriptedEffect (depth + 1) nestedName nestedParams)

                                direct :: nested

                allEntitiesList
                |> Seq.collect (fun struct (_, d) ->
                    d.Force().Referencedtypes
                    |> Option.bind (Map.tryFind "scripted_effect")
                    |> Option.defaultValue [])
                |> Seq.filter (fun ref -> ref.referenceType = ReferenceType.TypeDef)
                |> Seq.collect (fun ref ->
                    let effectName = ref.name.GetString()
                    collectFromScriptedEffect 0 effectName (findCallParams ref.position))

        let results =
            collectExpandedScriptedDefinedVariables ()
            |> Seq.fold mergeDefinedVariables results

        lookup.varDefInfo <- addEmbeddedVarDefData results
        // eprintfn "vdi %A" results
        let results =
            allEntitiesList
            |> PSeq.map (fun struct (e, l) ->
                (l.Force().SavedEventTargets
                 |> (Option.defaultWith (fun () -> tempInfoService.GetSavedEventTargets e))))
            |> Seq.fold
                (fun (acc: ResizeArray<_>) e ->
                    acc.AddRange e
                    acc)
                (new ResizeArray<_>())

        lookup.savedEventTargets <- results
        //|> Seq.fold (fun m map -> Map.toList map |>  List.fold (fun m2 (n,k) -> if Map.containsKey n m2 then Map.add n ((k |> List.ofSeq)@m2.[n]) m2 else Map.add n (k |> List.ofSeq) m2) m) tempValues
        settings.refreshConfigAfterVarDefHook lookup resources embeddedSettings

        // Collect scripted variables with their values from all entities. Only variables
        // defined under common/scripted_variables are game-globals; every other @-variable
        // is file-local. The full list keeps feeding hover/docs, while completion receives
        // the globals only (CompletionService adds the current file's locals per entity).
        let isGlobalVariableEntity (e: Entity) =
            e.logicalpath.Replace('\\', '/').Contains("common/scripted_variables/")

        let scriptVariablesWithScope =
            allEntitiesList
            |> Seq.collect (fun struct (e, _) ->
                let isGlobal = isGlobalVariableEntity e

                e.entity.Leaves
                |> Seq.choose (fun leaf ->
                    if leaf.Key.StartsWith("@") && not (leaf.Key.StartsWith("@[")) && not (leaf.Key.StartsWith(@"@\[")) then
                        Some (isGlobal, leaf.Key, leaf.Value.ToRawString())
                    else None))
            |> Seq.toList

        // Store in lookup for later use (with actual values)
        lookup.scriptedVariables <-
            scriptVariablesWithScope
            |> Seq.map (fun (_, key, value) -> key, value)
            |> Seq.distinctBy fst
            |> Seq.toList

        lookup.globalScriptedVariableNames <-
            scriptVariablesWithScope
            |> Seq.choose (fun (isGlobal, key, _) -> if isGlobal then Some key else None)
            |> Seq.distinct
            |> Seq.toList

        let ruleValidationService, infoService, completionService =
            buildServices rulesWrapper tempTypeMap (currentLoc ()) (currentFiles ())

        // log "Refresh rule caches time: %i" timer.ElapsedMilliseconds; timer.Restart()
        // game.RefreshValidationManager()
        logInfo $"Refresh all lookups: %0.3f{float endToEndTimer.ElapsedMilliseconds / 1000.0}s"
        // Log type counts for key types
        let stCount = lookup.typeDefInfo |> Map.tryFind "scripted_trigger" |> Option.map Array.length |> Option.defaultValue 0
        let seCount = lookup.typeDefInfo |> Map.tryFind "scripted_effect" |> Option.map Array.length |> Option.defaultValue 0
        logInfo $"Type counts: scripted_trigger=%d{stCount}, scripted_effect=%d{seCount}, total types=%d{lookup.typeDefInfo.Count}"
        ruleValidationService, infoService, completionService

    let normaliseFilePath (path: string) =
        try
            FileInfo(path).FullName.Replace('\\', '/').ToLowerInvariant()
        with _ ->
            path.Replace('\\', '/').ToLowerInvariant()

    let getEntityByFilePathWithFallback (path: string) =
        match resources.GetEntityByFilePath path with
        | Some entity -> Some entity
        | None ->
            let target = normaliseFilePath path
            let fallback =
                resources.AllEntities()
                |> Seq.tryFind (fun struct (entity, _) -> normaliseFilePath entity.filepath = target)
            if fallback.IsSome then
                logDiag $"Refresh scripted types used normalised entity lookup fallback for %s{path}"
            fallback

    let refreshScriptedTypes (files: string list) (typeKeys: string list) =
        let timer = System.Diagnostics.Stopwatch.StartNew()
        let typeKeys = typeKeys |> List.distinct
        let typeKeySet = typeKeys |> Set.ofList
        let fileSet = files |> List.map normaliseFilePath |> Set.ofList

        lookup.configRules <- settings.loadConfigRulesHook baseConfigRules lookup embeddedSettings
        let rulesWrapper = rulesWrapperFor lookup.configRules
        let loc = currentLoc ()
        let allFiles = currentFiles ()
        let emptyVarMap: FrozenDictionary<string, PrefixOptimisedStringSet> = FrozenDictionary.Empty
        let baseFrozenTypeMap = tempTypeMap.ToFrozenDictionary()

        let tempRuleValidationService =
            buildRuleValidationService
                rulesWrapper
                baseFrozenTypeMap
                emptyVarMap
                loc
                allFiles
                (Some(aliasKeyMapFor rulesWrapper tempTypeMap baseFrozenTypeMap))

        let entities =
            files
            |> List.choose (fun path ->
                getEntityByFilePathWithFallback path
                |> Option.map (fun struct (entity, _) -> entity))

        let changedTypes =
            tempTypes |> List.filter (fun t -> typeKeySet.Contains t.name)

        let changedTypeDefInfo =
            if entities.IsEmpty || changedTypes.IsEmpty then
                Map.empty
            else
                getTypesFromDefinitions (Some tempRuleValidationService) changedTypes entities

        lookup.typeDefInfo <-
            typeKeys
            |> List.fold
                (fun typeDefInfo typeKey ->
                    let existing =
                        typeDefInfo
                        |> Map.tryFind typeKey
                        |> Option.defaultValue [||]
                        |> Array.filter (fun tdi -> not (fileSet.Contains(normaliseFilePath tdi.range.FileName)))

                    let updated =
                        changedTypeDefInfo
                        |> Map.tryFind typeKey
                        |> Option.defaultValue [||]

                    typeDefInfo |> Map.add typeKey (Array.append existing updated))
                lookup.typeDefInfo

        tempTypeMap <-
            typeKeys
            |> List.fold
                (fun acc typeKey ->
                    let ids =
                        lookup.typeDefInfo
                        |> Map.tryFind typeKey
                        |> Option.defaultValue [||]
                        |> Seq.map _.id
                    Map.add typeKey (createStringSet ids) acc)
                tempTypeMap
        lookup.typeDefInfoForValidation <- typeDefInfoForValidationFrom lookup.typeDefInfo

        let ruleValidationService, infoService, completionService =
            buildServices rulesWrapper tempTypeMap loc allFiles

        logInfo $"Refresh scripted types: files=%d{files.Length}, typeKeys=%d{typeKeys.Length}, elapsed=%0.3f{float timer.ElapsedMilliseconds / 1000.0}s"
        ruleValidationService, infoService, completionService

    let prepareScriptedTypes (files: string list) (typeKeys: string list) : StagedScriptedTypes option =
        let timer = System.Diagnostics.Stopwatch.StartNew()
        let typeKeys = typeKeys |> List.distinct
        let typeKeySet = typeKeys |> Set.ofList
        let fileSet = files |> List.map normaliseFilePath |> Set.ofList

        // Snapshot the shared maps once; the folds below seed from these locals, never the
        // live lookup fields, so this whole function leaves shared state untouched.
        let baseTypeDefInfo = lookup.typeDefInfo
        let baseTempTypeMap = tempTypeMap

        let rulesWrapper = rulesWrapperFor lookup.configRules
        let loc = currentLoc ()
        let allFiles = currentFiles ()
        let emptyVarMap: FrozenDictionary<string, PrefixOptimisedStringSet> = FrozenDictionary.Empty
        let baseFrozenTypeMap = baseTempTypeMap.ToFrozenDictionary()

        let tempRuleValidationService =
            buildRuleValidationService
                rulesWrapper
                baseFrozenTypeMap
                emptyVarMap
                loc
                allFiles
                (Some(aliasKeyMapFor rulesWrapper baseTempTypeMap baseFrozenTypeMap))

        let entities =
            files
            |> List.choose (fun path ->
                getEntityByFilePathWithFallback path
                |> Option.map (fun struct (entity, _) -> entity))

        let changedTypes =
            tempTypes |> List.filter (fun t -> typeKeySet.Contains t.name)

        let changedTypeDefInfo =
            if entities.IsEmpty || changedTypes.IsEmpty then
                Map.empty
            else
                getTypesFromDefinitions (Some tempRuleValidationService) changedTypes entities

        let newTypeDefInfo =
            typeKeys
            |> List.fold
                (fun typeDefInfo typeKey ->
                    let existing =
                        typeDefInfo
                        |> Map.tryFind typeKey
                        |> Option.defaultValue [||]
                        |> Array.filter (fun tdi -> not (fileSet.Contains(normaliseFilePath tdi.range.FileName)))

                    let updated =
                        changedTypeDefInfo
                        |> Map.tryFind typeKey
                        |> Option.defaultValue [||]

                    typeDefInfo |> Map.add typeKey (Array.append existing updated))
                baseTypeDefInfo

        let newTempTypeMap =
            typeKeys
            |> List.fold
                (fun acc typeKey ->
                    let ids =
                        newTypeDefInfo
                        |> Map.tryFind typeKey
                        |> Option.defaultValue [||]
                        |> Seq.map _.id
                    Map.add typeKey (createStringSet ids) acc)
                baseTempTypeMap

        let newTypeDefInfoForValidation = typeDefInfoForValidationFrom newTypeDefInfo

        let ruleValidationService, infoService, completionService =
            buildServices rulesWrapper newTempTypeMap loc allFiles

        // Pay the lazy inverted-map cost here (read lock) rather than on the first
        // write-locked validation after commit.
        infoService.WarmTypeLocalisationIndex()

        logInfo $"Prepare scripted types: files=%d{files.Length}, typeKeys=%d{typeKeys.Length}, elapsed=%0.3f{float timer.ElapsedMilliseconds / 1000.0}s"

        Some
            { typeDefInfo = newTypeDefInfo
              tempTypeMap = newTempTypeMap
              typeDefInfoForValidation = newTypeDefInfoForValidation
              baseTypeDefInfo = baseTypeDefInfo
              ruleService = box ruleValidationService
              infoService = box infoService
              completionService = box completionService }

    let commitScriptedTypes (staged: StagedScriptedTypes) =
        if not (System.Object.ReferenceEquals(lookup.typeDefInfo, staged.baseTypeDefInfo)) then
            None
        else
            lookup.typeDefInfo <- staged.typeDefInfo
            tempTypeMap <- staged.tempTypeMap
            lookup.typeDefInfoForValidation <- staged.typeDefInfoForValidation
            Some(
                staged.ruleService :?> RuleValidationService,
                staged.infoService :?> InfoService,
                staged.completionService :?> CompletionService
            )

    // Staged full refresh: run the heavy refreshConfig against a shallow clone of the
    // lookup so it can execute without the write lock. Shared manager state (tempTypeMap
    // etc.) is snapshotted and restored, so between prepare and commit the instance stays
    // fully consistent with the untouched original lookup.
    let prepareRefreshConfig () =
        let original = lookup
        let baseTypeDefInfo = original.typeDefInfo
        let baseVarDefInfo = original.varDefInfo
        let baseConfigRules = original.configRules
        let baseTempTypeMap = tempTypeMap
        let baseTempEnumMap = tempEnumMap
        let baseRulesDataGenerated = rulesDataGenerated
        let clone = original.ShallowClone() :?> 'L
        lookup <- clone

        try
            let ruleValidationService, infoService, completionService = refreshConfig ()
            // Pay the lazy inverted-map cost during the read-locked prepare, not after commit.
            infoService.WarmTypeLocalisationIndex()

            let staged =
                { refreshedLookup = box clone
                  baseTypeDefInfo = box baseTypeDefInfo
                  baseVarDefInfo = box baseVarDefInfo
                  baseConfigRules = box baseConfigRules
                  newTempTypeMap = box tempTypeMap
                  newTempEnumMap = box tempEnumMap
                  newRulesDataGenerated = rulesDataGenerated
                  ruleService = box ruleValidationService
                  infoService = box infoService
                  completionService = box completionService }

            Some staged
        finally
            lookup <- original
            tempTypeMap <- baseTempTypeMap
            tempEnumMap <- baseTempEnumMap
            rulesDataGenerated <- baseRulesDataGenerated

    let commitRefreshConfig (staged: StagedCacheRefresh) =
        let guardsHold =
            System.Object.ReferenceEquals(lookup.typeDefInfo, staged.baseTypeDefInfo)
            && System.Object.ReferenceEquals(lookup.varDefInfo, staged.baseVarDefInfo)
            && System.Object.ReferenceEquals(lookup.configRules, staged.baseConfigRules)

        if not guardsHold then
            None
        else
            lookup.AbsorbFieldsFrom(staged.refreshedLookup :?> Lookup)
            tempTypeMap <- staged.newTempTypeMap :?> Map<string, PrefixOptimisedStringSet>

            tempEnumMap <-
                staged.newTempEnumMap :?> FrozenDictionary<string, string * PrefixOptimisedStringSet>

            rulesDataGenerated <- staged.newRulesDataGenerated

            Some(
                staged.ruleService :?> RuleValidationService,
                staged.infoService :?> InfoService,
                staged.completionService :?> CompletionService
            )

    member _.LoadBaseConfig(rulesSettings) = loadBaseConfig rulesSettings
    member _.RefreshConfig() = refreshConfig ()
    member _.PrepareRefreshConfig() = prepareRefreshConfig ()
    member _.CommitRefreshConfig(staged) = commitRefreshConfig staged
    member _.RefreshScriptedTypes(files, typeKeys) = refreshScriptedTypes files typeKeys
    member _.PrepareScriptedTypes(files, typeKeys) = prepareScriptedTypes files typeKeys
    member _.CommitScriptedTypes(staged) = commitScriptedTypes staged
