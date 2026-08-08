namespace CWTools.Games

open System
open System.Collections.Concurrent
open CWTools.Common
open CWTools.Validation
open CWTools.Validation.ValidationCore
open CWTools.Utilities.Utils
open CWTools.Rules
open CWTools.Process
open CWTools.Parser.Types
open CWTools.Validation.Stellaris.STLLocalisationValidation
open CWTools.Utilities.Position
open CWTools.Process.Scopes
open FSharp.Collections.ParallelSeq
open CWTools.Process.Localisation

/// Whole-workspace entity snapshot shared by the scripted-effect/trigger and
/// scripted-value parameter validators. Holds only Entity references (never
/// their Lazy computed data) so workspace updates cannot strand large objects.
/// Invalidated per file: refreshFile re-extracts a single changed file.
type ScriptedParamsSnapshot =
    { entitiesByFile: Map<string, Entity>
      fileLocalVariables: Map<string, Map<string, string>>
      globalVarValues: Map<string, string>
      scriptedEffectNodes: Map<string * string, Node>
      scriptedTriggerNodes: Map<string * string, Node>
      scriptValueNodes: Map<string * string, Node> }

module ScriptedParamsSnapshot =
    let private variablesInEntity (e: Entity) =
        e.entity.Leaves
        |> Seq.choose (fun leaf ->
            if leaf.Key.StartsWith("@", StringComparison.Ordinal)
               && not (leaf.Key.StartsWith("@[", StringComparison.Ordinal))
               && not (leaf.Key.StartsWith(@"@\[", StringComparison.Ordinal)) then
                Some(leaf.Key, leaf.Value.ToRawString())
            else
                None)
        |> Seq.distinctBy fst
        |> Map.ofSeq

    let private isScriptedVariablesPath (e: Entity) =
        e.logicalpath
            .Replace('\\', '/')
            .Contains("common/scripted_variables/", StringComparison.OrdinalIgnoreCase)

    let findNodeInEntity (entity: Entity) (pos: range) =
        let rec findChild (node: Node) =
            if node.Position.Equals(pos) then
                Some node
            else
                match node.Nodes |> Seq.tryFind (fun n -> rangeContainsRange n.Position pos) with
                | Some c -> findChild c
                | None -> None
        findChild entity.entity

    let private definitionNodes (lu: Lookup) (typeName: string) (entitiesByFile: Map<string, Entity>) =
        lu.typeDefInfo
        |> Map.tryFind typeName
        |> Option.defaultValue [||]
        |> Array.choose (fun se ->
            entitiesByFile
            |> Map.tryFind se.range.FileName
            |> Option.bind (fun e -> findNodeInEntity e se.range)
            |> Option.map (fun node -> (se.id, se.range.FileName), node))
        |> Map.ofArray

    let build (res: IResourceAPI<'T>) (lu: Lookup) : ScriptedParamsSnapshot =
        let allEntities =
            res.AllEntities()
            |> Seq.map (fun struct (e, _) -> e)
            |> Seq.filter (fun e -> e.overwrite <> Overwrite.Overwritten)
            |> Seq.toList
        let entitiesByFile = allEntities |> List.map (fun e -> e.filepath, e) |> Map.ofList
        let fileLocalVariables = entitiesByFile |> Map.map (fun _ e -> variablesInEntity e)
        let globalVarValues =
            allEntities
            |> Seq.filter isScriptedVariablesPath
            |> Seq.collect (variablesInEntity >> Map.toSeq)
            |> Seq.distinctBy fst
            |> Map.ofSeq
        { entitiesByFile = entitiesByFile
          fileLocalVariables = fileLocalVariables
          globalVarValues = globalVarValues
          scriptedEffectNodes = definitionNodes lu "scripted_effect" entitiesByFile
          scriptedTriggerNodes = definitionNodes lu "scripted_trigger" entitiesByFile
          scriptValueNodes = definitionNodes lu "script_value" entitiesByFile }

    /// Re-extract one changed file. Called before validation for every file
    /// that was updated or removed since the snapshot was last refreshed,
    /// keeping the whole-workspace build amortised O(changed files).
    let refreshFile (res: IResourceAPI<'T>) (lu: Lookup) (snap: ScriptedParamsSnapshot) (filepath: string) : ScriptedParamsSnapshot =
        let removeNodesForFile (nodes: Map<string * string, Node>) =
            nodes |> Map.filter (fun _ n -> n.Position.FileName <> filepath)
        let addNodesForFile (lu: Lookup) (typeName: string) (nodes: Map<string * string, Node>) (entitiesByFile: Map<string, Entity>) =
            lu.typeDefInfo
            |> Map.tryFind typeName
            |> Option.defaultValue [||]
            |> Array.fold (fun acc se ->
                if se.range.FileName <> filepath then
                    acc
                else
                    match entitiesByFile |> Map.tryFind filepath |> Option.bind (fun e -> findNodeInEntity e se.range) with
                    | Some node -> Map.add (se.id, se.range.FileName) node acc
                    | None -> acc) (removeNodesForFile nodes)
        match res.GetEntityByFilePath filepath with
        | Some struct (e, _) when e.overwrite <> Overwrite.Overwritten ->
            let entitiesByFile = snap.entitiesByFile |> Map.add filepath e
            let localVariables = variablesInEntity e
            let globalVarValues =
                if isScriptedVariablesPath e then
                    let oldVars =
                        snap.fileLocalVariables |> Map.tryFind filepath |> Option.defaultValue Map.empty
                    let withoutOld = oldVars |> Map.fold (fun acc k _ -> Map.remove k acc) snap.globalVarValues
                    localVariables |> Map.fold (fun acc k v -> Map.add k v acc) withoutOld
                else
                    snap.globalVarValues
            { entitiesByFile = entitiesByFile
              fileLocalVariables = snap.fileLocalVariables |> Map.add filepath localVariables
              globalVarValues = globalVarValues
              scriptedEffectNodes = addNodesForFile lu "scripted_effect" snap.scriptedEffectNodes entitiesByFile
              scriptedTriggerNodes = addNodesForFile lu "scripted_trigger" snap.scriptedTriggerNodes entitiesByFile
              scriptValueNodes = addNodesForFile lu "script_value" snap.scriptValueNodes entitiesByFile }
        | _ ->
            let entitiesByFile = snap.entitiesByFile |> Map.remove filepath
            { entitiesByFile = entitiesByFile
              fileLocalVariables = snap.fileLocalVariables |> Map.remove filepath
              globalVarValues = snap.globalVarValues
              scriptedEffectNodes = removeNodesForFile snap.scriptedEffectNodes
              scriptedTriggerNodes = removeNodesForFile snap.scriptedTriggerNodes
              scriptValueNodes = removeNodesForFile snap.scriptValueNodes }

type LookupFileValidator<'T when 'T :> ComputedData> =
    Files.FileManager -> RuleValidationService option -> Lookup -> FileValidator<'T>

/// Validators that consume a whole-workspace entity snapshot built once and
/// invalidated per file. Receives the snapshot instead of rebuilding it on
/// every validation pass.
type ScriptedParamsValidator<'T when 'T :> ComputedData> =
    ScriptedParamsSnapshot -> LookupFileValidator<'T>

type ValidationManagerSettings<'T when 'T :> ComputedData> =
    { validators: (LocalStructureValidator<'T> * string) list
      globalValidators: (StructureValidator<'T> * string) list
      /// Cross-file validators required by deferred dynamic call-site validation.
      dynamicValidators: (StructureValidator<'T> * string) list
      experimentalValidators: (StructureValidator<'T> * string) list
      heavyExperimentalValidators: (LookupValidator<'T> * string) list
      experimental: bool
      fileValidators: (FileValidator<'T> * string) list
      globalFileValidators: (FileValidator<'T> * string) list
      lookupValidators: (LocalLookupValidator<'T> * string) list
      globalLookupValidators: (LookupValidator<'T> * string) list
      lookupFileValidators: (LookupFileValidator<'T> * string) list
      scriptedParamsValidators: (ScriptedParamsValidator<'T> * string) list
      useRules: bool
      debugRulesOnly: bool
      localisationValidators: LocalisationValidator<'T> list }

type ValidationManagerServices<'T when 'T :> ComputedData> =
    { resources: IResourceAPI<'T>
      lookup: Lookup
      ruleValidationService: RuleValidationService option
      infoService: InfoService option
      localisationKeys: unit -> (Lang * Set<string>) array
      fileManager: Files.FileManager }

open System.Collections.Generic

type ErrorCache() =

    let sourceToErrorsForTargets =
        ConcurrentDictionary<string, ConcurrentDictionary<string, CWError list>>()

    let targetToErrors = ConcurrentDictionary<string, HashSet<CWError>>()
    let selfErrors = ConcurrentDictionary<string, HashSet<CWError>>()

    let monitor = new Object()
    
    /// 清理不存在文件的缓存条目，防止内存泄漏
    member this.Cleanup(existingFiles: Set<string>) =
        lock monitor (fun () ->
            // 清理 sourceToErrorsForTargets 中不存在的文件
            let sourceFiles = sourceToErrorsForTargets.Keys |> Seq.toList
            for sourceFile in sourceFiles do
                if not (existingFiles.Contains sourceFile) then
                    match sourceToErrorsForTargets.TryRemove sourceFile with
                    | true, _ -> ()
                    | _ -> ()
            
            // 清理 targetToErrors 中不存在的文件
            let targetFiles = targetToErrors.Keys |> Seq.toList
            for targetFile in targetFiles do
                if not (existingFiles.Contains targetFile) then
                    match targetToErrors.TryRemove targetFile with
                    | true, _ -> ()
                    | _ -> ()
            
            // 清理 selfErrors 中不存在的文件
            let selfErrorFiles = selfErrors.Keys |> Seq.toList
            for selfFile in selfErrorFiles do
                if not (existingFiles.Contains selfFile) then
                    match selfErrors.TryRemove selfFile with
                    | true, _ -> ()
                    | _ -> ()
        )

    member this.AddErrorsGeneratedByFile(fromEntity: Entity, errorsForFiles: CWError seq) =
        lock monitor (fun () ->
            let errorsForFiles = errorsForFiles |> Seq.toList
            let wrappedInlineErrors =
                errorsForFiles
                |> List.filter (fun error -> error.code = "CW274")
                |> List.collect (fun error -> error.relatedErrors |> Option.defaultValue [])

            let isWrappedInlineError (error: CWError) =
                wrappedInlineErrors
                |> List.exists (fun related ->
                    related.message = error.message
                    && related.location.FileName = error.range.FileName
                    && related.location.StartLine = error.range.StartLine
                    && related.location.StartColumn = error.range.StartColumn
                    && related.location.EndLine = error.range.EndLine
                    && related.location.EndColumn = error.range.EndColumn)

            let errorsForFiles =
                errorsForFiles
                |> List.filter (fun error -> error.code = "CW274" || not (isWrappedInlineError error))

            let mutable impactedFiles = HashSet<string>()
            // Remove existing errors generated by this file
            if sourceToErrorsForTargets.ContainsKey fromEntity.filepath then
                match sourceToErrorsForTargets.TryRemove fromEntity.filepath with
                | true, oldErrors ->
                    for pair in oldErrors do
                        let targetFile, errors = pair.Key, pair.Value
                        impactedFiles.Add targetFile |> ignore
                        // 安全地访问 targetToErrors，确保键存在
                        match targetToErrors.TryGetValue targetFile with
                        | true, bag ->
                            for error in errors do
                                bag.Remove error |> ignore
                        | false, _ -> () // 键不存在，跳过
                | _ -> ()

            match selfErrors.TryRemove fromEntity.filepath with
            | true, _ -> impactedFiles.Add fromEntity.filepath |> ignore
            | _ -> ()

            // Add new errors
            let groupedErrors = errorsForFiles |> Seq.groupBy (fun x -> x.range.FileName)
            let newErrors = new ConcurrentDictionary<string, CWError list>()
            sourceToErrorsForTargets.[fromEntity.filepath] <- newErrors

            for targetFile, cwErrors in groupedErrors do
                if fromEntity.filepath = targetFile then
                    // 使用 TryAdd 或索引器安全地更新字典
                    let _ = selfErrors.TryGetValue(targetFile)
                    selfErrors.[targetFile] <- new HashSet<CWError>(cwErrors)
                else
                    impactedFiles.Add targetFile |> ignore
                    newErrors.[targetFile] <- cwErrors |> List.ofSeq
                    let bag = targetToErrors.GetOrAdd(targetFile, (fun _ -> new HashSet<CWError>()))

                    for error in cwErrors do
                        bag.Add error |> ignore

            impactedFiles)

    member this.GetErrorsForEntity(entity: Entity) = this.GetErrorsForFile entity.filepath

    member this.GetErrorsForFile(filepath: string) =
        match targetToErrors.TryGetValue(filepath), selfErrors.TryGetValue(filepath) with
        | (true, errors1), (true, errors2) -> Some(Seq.append errors1 errors2 |> Seq.toList)
        | (false, _), (true, errors)
        | (true, errors), (false, _) -> Some(Seq.toList errors)
        | _ -> None

    member this.GetNonSelfErrorsForFile(entity: Entity) =
        match targetToErrors.TryGetValue(entity.filepath) with
        | true, cwErrors -> Some(Seq.toList cwErrors)
        | _ -> None

type ValidationManager<'T when 'T :> ComputedData>
    (
        settings: ValidationManagerSettings<'T>,
        services: ValidationManagerServices<'T>,
        validateLocalisationCommand,
        defaultContext: ScopeContext,
        noneContext: ScopeContext,
        errorCache: ErrorCache
    ) =
    let resources = services.resources
    let validators = settings.validators
    let errorCache = errorCache
    let cancellationCheck = System.Threading.AsyncLocal<unit -> bool>()

    // Whole-workspace snapshot consumed by the scripted-parameter validators,
    // invalidated per file. Entity-only (no Lazy computed data) so workspace
    // updates cannot strand large objects behind the cache.
    let scriptedParamsGate = obj ()
    let mutable scriptedParamsSnapshotCache: ScriptedParamsSnapshot option = None
    let mutable scriptedParamsDirtyFiles: Set<string> = Set.empty

    let ensureScriptedParamsSnapshot () =
        lock scriptedParamsGate (fun () ->
            match scriptedParamsSnapshotCache with
            | Some snap when scriptedParamsDirtyFiles.IsEmpty -> snap
            | Some snap ->
                let snap' =
                    scriptedParamsDirtyFiles
                    |> Set.fold
                        (fun acc filepath -> ScriptedParamsSnapshot.refreshFile resources services.lookup acc filepath)
                        snap
                scriptedParamsDirtyFiles <- Set.empty
                scriptedParamsSnapshotCache <- Some snap'
                snap'
            | None ->
                let snap = ScriptedParamsSnapshot.build resources services.lookup
                scriptedParamsDirtyFiles <- Set.empty
                scriptedParamsSnapshotCache <- Some snap
                snap)

    let markScriptedParamsDirty (filepaths: string list) =
        lock scriptedParamsGate (fun () ->
            if scriptedParamsSnapshotCache.IsSome then
                scriptedParamsDirtyFiles <-
                    filepaths |> List.fold (fun acc filepath -> Set.add filepath acc) scriptedParamsDirtyFiles)

    let clearScriptedParamsSnapshot () =
        lock scriptedParamsGate (fun () ->
            scriptedParamsSnapshotCache <- None
            scriptedParamsDirtyFiles <- Set.empty)

    // A DidChange interactive pass and the following save often validate the exact
    // same immutable Entity with the exact same RuleValidationService. Keep a small
    // bounded LRU of completed results so save-time deep validation can reuse them
    // without retaining results for an unbounded number of edited workspace files.
    let maxDetachedRuleResults = 32
    let detachedRuleResults =
        Dictionary<string, struct (Entity * RuleValidationService * ValidationResult)>()
    let detachedRuleResultOrder = LinkedList<string>()
    let detachedRuleResultNodes = Dictionary<string, LinkedListNode<string>>()
    let detachedRuleResultGate = obj ()
    let pathComparer = if OperatingSystem.IsWindows() then StringComparer.OrdinalIgnoreCase else StringComparer.Ordinal
    let localisationReferenceGate = obj ()
    let localisationKeysByFile = Dictionary<string, Set<string>>(pathComparer)
    let localisationFilesByKey = Dictionary<string, HashSet<string>>(StringComparer.Ordinal)
    let mutable localisationReferenceIndexBuilt = false

    let removeLocalisationReferencesForFileUnsafe filepath =
        match localisationKeysByFile.TryGetValue filepath with
        | true, keys ->
            for key in keys do
                match localisationFilesByKey.TryGetValue key with
                | true, files ->
                    files.Remove filepath |> ignore
                    if files.Count = 0 then localisationFilesByKey.Remove key |> ignore
                | false, _ -> ()
            localisationKeysByFile.Remove filepath |> ignore
        | false, _ -> ()

    let addLocalisationReferencesUnsafe filepath keys =
        removeLocalisationReferencesForFileUnsafe filepath
        localisationKeysByFile.[filepath] <- keys
        for key in keys do
            let files =
                match localisationFilesByKey.TryGetValue key with
                | true, existing -> existing
                | false, _ ->
                    let created = HashSet<string>(pathComparer)
                    localisationFilesByKey.Add(key, created)
                    created
            files.Add filepath |> ignore

    let addLocalisationReferencesForEntityUnsafe (entity: Entity) =
        match services.infoService with
        | Some infoService -> addLocalisationReferencesUnsafe entity.filepath (infoService.GetReferencedLocalisationKeys entity)
        | None -> removeLocalisationReferencesForFileUnsafe entity.filepath

    let ensureLocalisationReferenceIndexUnsafe () =
        if not localisationReferenceIndexBuilt then
            localisationKeysByFile.Clear()
            localisationFilesByKey.Clear()
            for struct (entity, _) in resources.ValidatableEntities() do
                addLocalisationReferencesForEntityUnsafe entity
            localisationReferenceIndexBuilt <- true

    let localisationFilesForKeys (keys: seq<string>) =
        lock localisationReferenceGate (fun () ->
            ensureLocalisationReferenceIndexUnsafe ()
            let files = HashSet<string>(pathComparer)
            for key in keys do
                match localisationFilesByKey.TryGetValue key with
                | true, referencedBy -> files.UnionWith referencedBy
                | false, _ -> ()
            files |> Seq.toArray)

    let entitiesForFiles (files: Set<string>) =
        files
        |> Seq.choose (fun filepath -> resources.GetEntityByFilePath filepath)
        |> Seq.toList

    let removeDetachedRuleResultUnsafe filepath =
        detachedRuleResults.Remove filepath |> ignore
        match detachedRuleResultNodes.TryGetValue filepath with
        | true, node ->
            detachedRuleResultOrder.Remove node
            detachedRuleResultNodes.Remove filepath |> ignore
        | _ -> ()

    let removeDetachedRuleResult filepath =
        lock detachedRuleResultGate (fun () -> removeDetachedRuleResultUnsafe filepath)

    let storeDetachedRuleResult (entity: Entity) (service: RuleValidationService) result =
        lock detachedRuleResultGate (fun () ->
            detachedRuleResults.[entity.filepath] <- struct (entity, service, result)

            match detachedRuleResultNodes.TryGetValue entity.filepath with
            | true, node ->
                detachedRuleResultOrder.Remove node
                detachedRuleResultOrder.AddLast node
            | _ ->
                let node = detachedRuleResultOrder.AddLast entity.filepath
                detachedRuleResultNodes.[entity.filepath] <- node

            while detachedRuleResults.Count > maxDetachedRuleResults do
                removeDetachedRuleResultUnsafe detachedRuleResultOrder.First.Value)

    let validationCancelled () =
        let check = cancellationCheck.Value
        not (isNull (box check)) && check ()

    let runRuleValidation (entity: Entity) =
        match services.ruleValidationService with
        | None -> Some OK
        | Some service ->
            let check = cancellationCheck.Value
            if isNull (box check) then
                Some(service.RuleValidateEntity entity)
            else
                service.RuleValidateEntityCancellable(entity, check)

    let tryTakeDetachedRuleResult (entity: Entity) =
        lock detachedRuleResultGate (fun () ->
            match services.ruleValidationService with
            | Some service ->
                match detachedRuleResults.TryGetValue entity.filepath with
                | true, struct (cachedEntity, cachedService, result) when
                    Object.ReferenceEquals(cachedEntity, entity)
                    && Object.ReferenceEquals(cachedService, service)
                    ->
                    removeDetachedRuleResultUnsafe entity.filepath
                    Some result
                | true, _ ->
                    removeDetachedRuleResultUnsafe entity.filepath
                    None
                | _ -> None
            | None -> None)

    let addToCache (entity: Entity) errors =
        // Try to get all other files which this file had generated errors for
        // And all files that it now generates errors for
        errorCache.AddErrorsGeneratedByFile(entity, errors)
    // let cache = (errorCache :> System.Collections.Generic.IDictionary<_,_>)
    // if cache.ContainsKey entity.filepath then cache.[entity.filepath] <- errors else cache.Add(entity.filepath, errors)
    let getErrorsForEntity (entity: Entity) = errorCache.GetErrorsForEntity entity

    /// Validate the current entities without changing ErrorCache. This is used
    /// after an editor resource has been committed: completion may read the game
    /// concurrently under the same read lock, while diagnostic publication is
    /// guarded by the document/model versions in the language server.
    let validateInteractiveDetached (entities: struct (Entity * Lazy<'T>) list) =
        if not settings.useRules || services.ruleValidationService.IsNone then
            []
        else
            entities
            |> List.collect (fun struct (entity, _) ->
                let fileIndex = fileIndexOfFile entity.filepath

                let result =
                    match runRuleValidation entity with
                    | Some result -> result
                    | None -> raise (OperationCanceledException("Rule validation snapshot was superseded."))

                storeDetachedRuleResult entity services.ruleValidationService.Value result

                result
                |> function
                    | Invalid(_, errors) ->
                        errors
                        |> List.filter (fun error ->
                            error.code <> "CW100"
                            && error.range.FileIndex = fileIndex)
                    | _ -> [])

    /// Drop cached diagnostics generated by the old version of an edited file.
    /// Detached interactive validation intentionally does not repopulate this
    /// cross-file cache; save/deep validation remains its authoritative writer.
    let invalidateInteractive (entities: struct (Entity * Lazy<'T>) list) =
        entities
        |> List.iter (fun struct (entity, _) ->
            removeDetachedRuleResult entity.filepath
            addToCache entity Seq.empty |> ignore)
        lock localisationReferenceGate (fun () ->
            if localisationReferenceIndexBuilt then
                for struct (entity, _) in entities do
                    addLocalisationReferencesForEntityUnsafe entity)

    /// Validate only the edited entities against CWT rules. This intentionally skips
    /// validators that inspect the full resource set; it is the latency-sensitive path
    /// used while typing; save-time or explicit validation supplies global diagnostics.
    let validateInteractive (entities: struct (Entity * Lazy<'T>) list) =
        if not settings.useRules || services.ruleValidationService.IsNone then
            []
        else
            let impactedFileBag = ConcurrentBag<string>()
            use ruleCancellation = new System.Threading.CancellationTokenSource()

            let cancelledResult () =
                ruleCancellation.Cancel()
                OK

            let ruleValidate (e: Entity) =
                if validationCancelled () then
                    cancelledResult ()
                else
                    let result =
                        match tryTakeDetachedRuleResult e with
                        | Some cached -> Some cached
                        | None -> runRuleValidation e

                    match result with
                    | None -> cancelledResult ()
                    | Some _ when validationCancelled () -> cancelledResult ()
                    | Some res ->
                        let errors =
                            res
                            |> function
                                | Invalid(_, es) -> es
                                | _ -> []

                        let impactedFiles = addToCache e errors
                        impactedFiles |> Seq.iter impactedFileBag.Add
                        let fileIndex = fileIndexOfFile e.filepath

                        res
                        |> function
                            | Invalid(_, es) ->
                                Invalid(Guid.NewGuid(), es |> List.filter (fun error -> error.range.FileIndex = fileIndex))
                            | _ -> OK

            let directErrors =
                entities
                |> List.map (fun struct (e, _) -> e)
                <&!&> ruleValidate                |> function
                    | Invalid(_, es) -> es
                    | _ -> []

            // Parallel rule workers communicate cancellation through a shared flag.
            // Raising inside PLINQ would wrap OperationCanceledException and leak it
            // past the cancellable API instead of returning None to the LSP caller.
            if ruleCancellation.IsCancellationRequested || validationCancelled () then
                raise (OperationCanceledException("Rule validation snapshot was superseded."))

            let nonSelfErrors =
                entities
                |> List.choose (fun struct (e, _) -> errorCache.GetNonSelfErrorsForFile e)
                |> List.collect id

            let impactedErrors =
                impactedFileBag
                |> Seq.choose errorCache.GetErrorsForFile
                |> Seq.collect id
                |> List.ofSeq

            directErrors @ nonSelfErrors @ impactedErrors
            |> List.filter (fun error -> error.code <> "CW100")

    let validateGlobal (shallow: bool) (entities: struct (Entity * Lazy<'T>) list) =
        log (sprintf "Validating %i files" entities.Length)
        // log $"Validation cache size %i{errorCache.}"
        let oldEntities = EntitySet(resources.AllEntities())
        let newEntities = EntitySet entities

        let runStructureValidators localValidators globalValidators experimentalValidators =
            (localValidators <&!!&> (fun (v, s) -> duration (fun _ -> v newEntities) s)
             |> (function
             | Invalid(_, es) -> es
             | _ -> []))
            @ (globalValidators <&!!&> (fun (v, s) -> duration (fun _ -> v oldEntities newEntities) s)
               |> (function
               | Invalid(_, es) -> es
               | _ -> []))
            @ (if not settings.experimental then
                   []
               else
                   experimentalValidators <&!&> (fun (v, s) -> duration (fun _ -> v oldEntities newEntities) s)
                   |> (function
                   | Invalid(_, es) -> es
                   | _ -> []))
        // log "Validating misc"
        let res = runStructureValidators settings.validators settings.globalValidators settings.experimentalValidators
        // log "Validating rules"
        // let rres = (if settings.useRules && services.ruleValidationService.IsSome then (runValidators (fun f -> f oldEntities newEntities) [services.ruleValidationService.Value.RuleValidate(), "rules"]) else [])
        let rres = validateInteractive entities

        let shallow, deep =
            if settings.debugRulesOnly then
                rres, []
            else

                // log "Validating files"
                let fres =
                    (settings.fileValidators @ settings.globalFileValidators)
                    <&!&> (fun (v, s) -> duration (fun _ -> v resources newEntities) s)
                    |> (function
                    | Invalid(_, es) -> es
                    | _ -> [])
                // log "Validating effects/triggers"
                let lres =
                    (settings.lookupValidators
                     <&!&> (fun (v, s) -> duration (fun _ -> v services.lookup newEntities) s)
                     |> function
                         | Invalid(_, es) -> es
                         | _ -> [])
                    @ (settings.globalLookupValidators
                       <&!&> (fun (v, s) -> duration (fun _ -> v services.lookup oldEntities newEntities) s)
                       |> function
                           | Invalid(_, es) -> es
                           | _ -> [])

                let lfres =
                    settings.lookupFileValidators
                    <&!&> (fun (v, s) ->
                        duration
                            (fun _ ->
                                v
                                    services.fileManager
                                    services.ruleValidationService
                                    services.lookup
                                    resources
                                    newEntities)
                            s)
                    |> function
                        | Invalid(_, es) -> es
                        | _ -> []

                let spres =
                    if settings.scriptedParamsValidators.IsEmpty then
                        []
                    else
                        let snapshot = ensureScriptedParamsSnapshot ()
                        settings.scriptedParamsValidators
                        <&!&> (fun (v, s) ->
                            duration
                                (fun _ ->
                                    (v snapshot)
                                        services.fileManager
                                        services.ruleValidationService
                                        services.lookup
                                        resources
                                        newEntities)
                                s)
                        |> function
                            | Invalid(_, es) -> es
                            | _ -> []

                let hres =
                    if settings.experimental && (not shallow) then
                        settings.heavyExperimentalValidators
                        <&!&> (fun (v, s) -> duration (fun _ -> v services.lookup oldEntities newEntities) s)
                        |> function
                            | Invalid(_, es) -> es
                            | _ -> []
                    else
                        []

                res @ fres @ lres @ lfres @ spres @ rres, hres

        shallow, deep

    /// Local/single-file validation avoids the full workspace enumeration. Its
    /// validator contracts expose only the changed entities; project-level checks
    /// that need the full workspace remain in the global validation domain.
    let validateLocal (entities: struct (Entity * Lazy<'T>) list) =
        log (sprintf "Local validating %i files" entities.Length)
        let newEntities = EntitySet entities

        let res =
            (settings.validators
             <&!!&> (fun (v, s) -> duration (fun _ -> v newEntities) s)
             |> (function
             | Invalid(_, es) -> es
             | _ -> []))

        let rres = validateInteractive entities

        if settings.debugRulesOnly then
            rres, []
        else
            // log "Validating files"
            let fres =
                settings.fileValidators
                <&!&> (fun (v, s) -> duration (fun _ -> v resources newEntities) s)
                |> (function
                | Invalid(_, es) -> es
                | _ -> [])
            // log "Validating effects/triggers"
            let lres =
                settings.lookupValidators
                <&!&> (fun (v, s) -> duration (fun _ -> v services.lookup newEntities) s)
                |> function
                    | Invalid(_, es) -> es
                    | _ -> []

            let lfres =
                settings.lookupFileValidators
                <&!&> (fun (v, s) ->
                    duration
                        (fun _ ->
                            v
                                services.fileManager
                                services.ruleValidationService
                                services.lookup
                                resources
                                newEntities)
                        s)
                |> function
                    | Invalid(_, es) -> es
                    | _ -> []

            let spres =
                if settings.scriptedParamsValidators.IsEmpty then
                    []
                else
                    let snapshot = ensureScriptedParamsSnapshot ()
                    settings.scriptedParamsValidators
                    <&!&> (fun (v, s) ->
                        duration
                            (fun _ ->
                                (v snapshot)
                                    services.fileManager
                                    services.ruleValidationService
                                    services.lookup
                                    resources
                                    newEntities)
                            s)
                    |> function
                        | Invalid(_, es) -> es
                        | _ -> []

            res @ fres @ lres @ lfres @ spres @ rres, []

    let validateDynamicLocal (entities: struct (Entity * Lazy<'T>) list) =
        let shallow, deep = validateLocal entities

        if settings.dynamicValidators.IsEmpty || validationCancelled () then
            shallow, deep
        else
            let workspaceEntities = EntitySet(resources.AllEntities())
            let changedEntities = EntitySet entities
            let dynamicErrors =
                settings.dynamicValidators
                <&!!&> (fun (validator, name) ->
                    duration (fun _ -> validator workspaceEntities changedEntities) name)
                |> function
                    | Invalid(_, errors) -> errors
                    | _ -> []
            shallow @ dynamicErrors, deep

    let validateLocalisation buildReferenceIndex (entities: struct (Entity * Lazy<'T>) list) =
        log (sprintf "Localisation check %i files" entities.Length)
        let timer = System.Diagnostics.Stopwatch()
        timer.Start()
        let newEntities = EntitySet entities

        let vs =
            (settings.localisationValidators
             |> List.map (fun v -> v (services.localisationKeys ()) newEntities)
             |> List.fold (<&&>) OK)

        let collectedReferences = ConcurrentBag<string * Set<string>>()
        let typeVs =
            if services.infoService.IsSome && (settings.useRules || buildReferenceIndex) then
                (entities
                 |> List.map (fun struct (e, _) -> e)
                 |> PSeq.map (fun entity ->
                     let errors =
                         if settings.useRules then
                             services.infoService.Value.GetTypeLocalisationErrors entity
                         else
                             OK
                     if buildReferenceIndex then
                         collectedReferences.Add(
                             entity.filepath,
                             services.infoService.Value.GetReferencedLocalisationKeys entity
                         )
                     errors))
                |> Seq.fold (<&&>) OK
            else
                OK

        if buildReferenceIndex && services.infoService.IsSome then
            lock localisationReferenceGate (fun () ->
                localisationKeysByFile.Clear()
                localisationFilesByKey.Clear()
                for filepath, keys in collectedReferences do
                    addLocalisationReferencesUnsafe filepath keys
                localisationReferenceIndexBuilt <- true)

        let vs = if settings.debugRulesOnly then typeVs else vs <&&> typeVs
        log (sprintf "Localisation check took %ims" timer.ElapsedMilliseconds)
        // logDiag (sprintf "%A" vs)
        (vs
         |> (function
         | Invalid(_, es) -> es
         | _ -> []))

    let createScopeContextFromReplace (rep: ReplaceScopes option) =
        match rep with
        | None -> noneContext
        | Some rs ->
            let ctx = defaultContext

            let prevctx =
                match rs.prevs with
                | Some prevs -> { ctx with Scopes = prevs }
                | None -> ctx

            let newctx =
                match (rs.this, rs.froms) with
                | Some this, Some froms ->
                    { prevctx with
                        Scopes = this :: prevctx.PopScope
                        From = froms
                        FromDepth = FromPath.FixedSlots
                        FromDepthStack = [] }
                | Some this, None ->
                    { prevctx with
                        Scopes = this :: prevctx.PopScope }
                | None, Some froms ->
                    { prevctx with
                        From = froms
                        FromDepth = FromPath.FixedSlots
                        FromDepthStack = [] }
                | None, None -> prevctx

            match rs.root with
            | Some root -> { newctx with Root = root }
            | None -> newctx

    let globalTypeLocalisationIndex =
        lazy
            let index = Dictionary<string, ResizeArray<struct (range * TypeLocalisation)>>(StringComparer.Ordinal)
            let typeDefinitions = Dictionary<string, TypeDefinition>(StringComparer.Ordinal)
            for definition in services.lookup.typeDefs do
                typeDefinitions.TryAdd(definition.name, definition) |> ignore

            let addExpectedKey key range localisation =
                let entries =
                    match index.TryGetValue key with
                    | true, existing -> existing
                    | false, _ ->
                        let created = ResizeArray<struct (range * TypeLocalisation)>()
                        index.Add(key, created)
                        created
                entries.Add(struct (range, localisation))

            let addLocalisations (values: struct (string * range) array) (localisations: TypeLocalisation list) =
                for localisation in localisations do
                    if localisation.required && localisation.explicitField.IsNone then
                        for struct (value, range) in values do
                            if not (value.Contains '.') then
                                addExpectedKey (localisation.prefix + value + localisation.suffix) range localisation

            for pair in services.lookup.typeDefInfoForValidation do
                let typeName = pair.Key
                let values = pair.Value
                match typeDefinitions.TryGetValue typeName with
                | true, definition -> addLocalisations values definition.localisation
                | false, _ -> ()

                let splitType = typeName.Split('.', 2)
                if splitType.Length > 1 then
                    match typeDefinitions.TryGetValue splitType.[0] with
                    | true, definition ->
                        match definition.subtypes |> List.tryFind (fun subtype -> subtype.name = splitType.[1]) with
                        | Some subtype -> addLocalisations values subtype.localisation
                        | None -> ()
                    | false, _ -> ()
            index

    let validateGlobalTypeLocalisationEntries (entries: seq<string * struct (range * TypeLocalisation)>) =
        let valLocCommand = validateLocalisationCommand services.lookup

        entries
        |> Seq.fold (fun result (locKey, struct (range, localisation)) ->
            let commandErrors =
                services.lookup.proccessedLoc
                |> List.fold (fun state (_, processed) ->
                    match Map.tryFind locKey processed with
                    | Some locEntry ->
                        valLocCommand locEntry (createScopeContextFromReplace localisation.replaceScopes)
                        <&&> state
                    | None -> state) OK

            let fakeLeaf = LeafValue(Value.Bool true, range)
            result
            <&&> commandErrors
            <&&> checkLocKeysLeafOrNode (services.localisationKeys ()) locKey fakeLeaf) OK

    let indexedGlobalTypeLocalisationEntries () =
        globalTypeLocalisationIndex.Value
        |> Seq.collect (fun pair -> pair.Value |> Seq.map (fun entry -> pair.Key, entry))

    let globalTypeDefLoc () =
        indexedGlobalTypeLocalisationEntries ()
        |> validateGlobalTypeLocalisationEntries

    let globalTypeDefLocForKeys (keys: seq<string>) =
        keys
        |> Seq.distinct
        |> Seq.collect (fun key ->
            match globalTypeLocalisationIndex.Value.TryGetValue key with
            | true, entries -> entries |> Seq.map (fun entry -> key, entry)
            | false, _ -> Seq.empty)
        |> validateGlobalTypeLocalisationEntries

    let globalTypeDefLocFilesForKeys (keys: seq<string>) =
        keys
        |> Seq.distinct
        |> Seq.collect (fun key ->
            match globalTypeLocalisationIndex.Value.TryGetValue key with
            | true, entries -> entries |> Seq.map (fun struct (range, _) -> range.FileName)
            | false, _ -> Seq.empty)
        |> Seq.distinct
        |> Seq.toArray

    let globalTypeDefLocForFiles (files: Set<string>) =
        indexedGlobalTypeLocalisationEntries ()
        |> Seq.filter (fun (_, struct (range, _)) -> files.Contains range.FileName)
        |> validateGlobalTypeLocalisationEntries


    member _.Validate(shallow: bool, entities: struct (Entity * Lazy<'T>) list) = validateGlobal shallow entities
    member _.ValidateCancellable(shallow: bool, entities: struct (Entity * Lazy<'T>) list, shouldCancel: unit -> bool) =
        let previous = cancellationCheck.Value
        cancellationCheck.Value <- shouldCancel

        try
            if shouldCancel () then
                None
            else
                try
                    let result = validateGlobal shallow entities
                    if shouldCancel () then None else Some result
                with :? OperationCanceledException ->
                    None
        finally
            cancellationCheck.Value <- previous

    member _.ValidateLocal(entities: struct (Entity * Lazy<'T>) list) = validateLocal entities
    /// Mark files whose workspace entity changed so the scripted-parameter
    /// snapshot refreshes only those entries before the next validation.
    member _.MarkScriptedParamsDirty(filepaths: string list) = markScriptedParamsDirty filepaths
    /// Drop the whole scripted-parameter snapshot (e.g. after a full recompute).
    member _.ClearScriptedParamsSnapshot() = clearScriptedParamsSnapshot ()
    member _.ValidateLocalCancellable(entities: struct (Entity * Lazy<'T>) list, shouldCancel: unit -> bool) =
        let previous = cancellationCheck.Value
        cancellationCheck.Value <- shouldCancel

        try
            if shouldCancel () then
                None
            else
                try
                    let result = validateLocal entities
                    if shouldCancel () then None else Some result
                with :? OperationCanceledException ->
                    None
        finally
            cancellationCheck.Value <- previous

    member _.ValidateDynamicLocalCancellable(entities: struct (Entity * Lazy<'T>) list, shouldCancel: unit -> bool) =
        let previous = cancellationCheck.Value
        cancellationCheck.Value <- shouldCancel

        try
            if shouldCancel () then
                None
            else
                try
                    let result = validateDynamicLocal entities
                    if shouldCancel () then None else Some result
                with :? OperationCanceledException ->
                    None
        finally
            cancellationCheck.Value <- previous

    member _.ValidateInteractive(entities: struct (Entity * Lazy<'T>) list) = validateInteractive entities
    member _.ValidateInteractiveDetached(entities: struct (Entity * Lazy<'T>) list) =
        validateInteractiveDetached entities
    member _.ValidateInteractiveDetachedCancellable(entities: struct (Entity * Lazy<'T>) list, shouldCancel: unit -> bool) =
        let previous = cancellationCheck.Value
        cancellationCheck.Value <- shouldCancel

        try
            if shouldCancel () then
                None
            else
                try
                    let result = validateInteractiveDetached entities
                    if shouldCancel () then None else Some result
                with :? OperationCanceledException ->
                    None
        finally
            cancellationCheck.Value <- previous

    member _.InvalidateInteractive(entities: struct (Entity * Lazy<'T>) list) =
        invalidateInteractive entities
    member _.ValidateLocalisation(entities: struct (Entity * Lazy<'T>) list) = validateLocalisation false entities
    member _.ValidateAllLocalisation(entities: struct (Entity * Lazy<'T>) list) = validateLocalisation true entities
    member _.ValidateGlobalLocalisation() = globalTypeDefLoc ()
    member _.ValidateGlobalLocalisationForKeys(keys: seq<string>) = globalTypeDefLocForKeys keys
    member _.GlobalLocalisationFilesForKeys(keys: seq<string>) = globalTypeDefLocFilesForKeys keys
    member _.ValidateGlobalLocalisationForFiles(files: Set<string>) = globalTypeDefLocForFiles files
    member _.LocalisationFilesForKeys(keys: seq<string>) = localisationFilesForKeys keys
    member _.ValidateLocalisationFiles(files: Set<string>) = entitiesForFiles files |> validateLocalisation false

    member this.CachedRuleLocalisationErrorsForFiles(files: Set<string>) =
        let locKeysArray = services.localisationKeys ()
        this.CachedRuleErrors(entitiesForFiles files)
        |> List.filter (fun error ->
            if error.code = "CW100" then
                match error.data with
                | Some key -> not (locKeysArray |> Array.exists (fun (_, keys) -> keys.Contains key))
                | None -> true
            else
                false)

    /// 清理不存在文件的缓存条目，防止内存泄漏
    member _.Cleanup(existingFiles: Set<string>) =
        errorCache.Cleanup existingFiles
        lock detachedRuleResultGate (fun () ->
            for filePath in detachedRuleResults.Keys |> Seq.toArray do
                if not (existingFiles.Contains filePath) then
                    removeDetachedRuleResultUnsafe filePath)
        lock localisationReferenceGate (fun () ->
            if localisationReferenceIndexBuilt then
                for filePath in localisationKeysByFile.Keys |> Seq.toArray do
                    if not (existingFiles.Contains filePath) then
                        removeLocalisationReferencesForFileUnsafe filePath)

    member _.InvalidateFile(filepath: string) =
        removeDetachedRuleResult filepath

    member _.CachedRuleErrors(entities: struct (Entity * Lazy<'T>) list) =
        let res =
            entities
            |> List.map (fun struct (e, l) -> (struct (e, l)), errorCache.GetErrorsForEntity e)

        let forced =
            res
            |> List.filter (fun (e, errors) -> errors.IsNone)
            |> List.choose (fun (struct (e, _), _) -> errorCache.GetErrorsForEntity e)
            |> List.collect id

        (res |> List.choose (fun (_, errors) -> errors) |> List.collect id) @ forced

    member _.ErrorCache() = errorCache
