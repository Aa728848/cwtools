namespace CWTools.Games

open System.Linq

open CWTools.Common
// open CWTools.Process.STLScopes
open Files
open System.Text
open CWTools.Utilities.Utils
open System.IO
open CWTools.Rules



type ValidationSettings =
    { langs: Lang array
      validateVanilla: bool
      experimental: bool }

type GameSettings<'L> =
    { rootDirectories: WorkspaceDirectoryInput array
      embedded: EmbeddedSettings
      validation: ValidationSettings
      rules: RulesSettings option
      scriptFolders: string array option
      excludeGlobPatterns: string array option
      modFilter: string option
      initialLookup: 'L
      maxFileSize: int option
      enableInlineScripts: bool }

type EmbeddedSetupSettings =
    | FromConfig of embeddedFiles: (string * string) list * cachedResourceData: (Resource * Entity) list
    | Metadata of cachedRuleMetadata: CachedRuleMetadata
    | ManualSettings of EmbeddedSettings

type StopPoint =
    | GameCtor
    | GameInitLoad
    | GameAfterInit
    | GameInitialConfigRules
    | Full

type DebugSettings =
    { EarlyStop: StopPoint }

    static member Default = { EarlyStop = Full }

type GameSetupSettings<'L> =
    { rootDirectories: WorkspaceDirectoryInput array
      embedded: EmbeddedSetupSettings
      validation: ValidationSettings
      rules: RulesSettings option
      scriptFolders: string array option
      excludeGlobPatterns: string array option
      modFilter: string option
      maxFileSize: int option
      debugSettings: DebugSettings
      vanillaPath: string option }

[<Sealed>]
type GameObject<'T, 'L when 'T :> ComputedData and 'L :> Lookup>
    (
        settings: GameSettings<'L>,
        game,
        scriptFolders,
        computeFunction,
        computeUpdateFunction,
        localisationService,
        locFunctions,
        defaultContext,
        noneContext,
        encoding: Encoding,
        fallbackencoding: Encoding,
        validationSettings,
        globalLocalisation: GameObject<'T, 'L> -> CWError list,
        afterUpdateFile: GameObject<'T, 'L> -> string -> unit,
        localisationExtension: string,
        ruleManagerSettings: RuleManagerSettings<'T, 'L>,
        debugSettings: DebugSettings
    ) as this =
    let scriptFolders = settings.scriptFolders |> Option.defaultValue scriptFolders
    let excludeGlobPatterns = settings.excludeGlobPatterns |> Option.defaultValue [||]

    let embeddedDir =
        settings.embedded.cachedResourceData
        |> List.tryHead
        |> Option.map (fun (r, e) -> e.filepath.Replace("\\", "/").TrimStart('.').Replace(e.logicalpath, ""))

    let fileManager =
        FileManager(
            settings.rootDirectories,
            embeddedDir,
            scriptFolders,
            game,
            encoding,
            excludeGlobPatterns,
            settings.maxFileSize |> Option.defaultValue 2
        )
    // let computeEU4Data (e : Entity) = EU4ComputedData()
    // let mutable infoService : InfoService<_> option = None
    // let mutable completionService : CompletionService<_> option = None
    let mutable ruleValidationService: RuleValidationService option = None
    let mutable infoService: InfoService option = None

    let resourceManager =
        ResourceManager<'T>(
            computeFunction (fun () -> this.InfoService),
            computeUpdateFunction (fun () -> this.InfoService),
            encoding,
            fallbackencoding,
            settings.enableInlineScripts
        )

    let validatableFiles () = this.Resources.ValidatableFiles
    let lookup = settings.initialLookup

    let localisationManager =
        LocalisationManager<'T>(
            resourceManager.Api,
            localisationService,
            settings.validation.langs,
            lookup,
            locFunctions >> fst,
            localisationExtension
        )

    let debugMode =
        settings.rules |> Option.map (fun r -> r.debugMode) |> Option.defaultValue false

    let addEmbeddedLoc langs =
        match settings.embedded.cachedRuleMetadata with
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

    let validationServices () =
        { resources = resourceManager.Api
          lookup = lookup
          ruleValidationService = ruleValidationService
          infoService = infoService
          localisationKeys =
            (fun _ -> addEmbeddedLoc settings.validation.langs (localisationManager.LocalisationKeys()))
          fileManager = fileManager }

    let mutable validationManager: ValidationManager<'T> =
        ValidationManager(
            validationSettings,
            validationServices (),
            locFunctions >> snd,
            defaultContext,
            (if debugMode then noneContext else defaultContext),
            ErrorCache()
        )

    let rulesManager =
        RulesManager<'T, 'L>(
            resourceManager.Api,
            lookup,
            ruleManagerSettings,
            localisationManager,
            settings.embedded,
            settings.validation.langs,
            debugMode
        )
    let errorCache = System.Collections.Concurrent.ConcurrentDictionary<string, CWError list>()

    let updateFile (shallow: bool) filepath (fileText: string option) =
        log $"updateFile %s{filepath}"
        let timer = System.Diagnostics.Stopwatch()
        timer.Start()

        let res =
            match filepath with
            | x when x.EndsWith localisationExtension ->
                let file = fileText |> Option.defaultWith (fun () -> File.ReadAllText filepath)

                let resourceInput =
                    LanguageFeatures.makeFileWithContentResourceInput fileManager filepath file

                let resource, _ = this.Resources.UpdateFile(resourceInput)

                match resource with
                | FileWithContentResource(_, r) -> this.LocalisationManager.UpdateLocalisationFile r
                | _ -> logWarning (sprintf "Localisation file failed to parse %s" filepath)

                []
            | x when PdxShaderFeatures.isShaderFile x ->
                let file =
                    fileText |> Option.defaultWith (fun () -> File.ReadAllText(filepath, encoding))

                let resource =
                    LanguageFeatures.makeFileWithContentResourceInput fileManager filepath file

                this.Resources.UpdateFile resource |> ignore
                PdxShaderFeatures.validate this.Resources filepath file
            | _ ->
                let file =
                    fileText |> Option.defaultWith (fun () -> File.ReadAllText(filepath, encoding))

                let resource = LanguageFeatures.makeEntityResourceInput fileManager filepath file
                let newEntities = [ this.Resources.UpdateFile resource ] |> List.choose snd
                afterUpdateFile this filepath
                validationManager.InvalidateInteractive newEntities

                match shallow with
                | true ->
                    let shallowres, _ = validationManager.Validate(shallow, newEntities)
                    let shallowres = shallowres @ (validationManager.ValidateLocalisation newEntities)
                    let deep = match errorCache.TryGetValue(filepath) with true, v -> v | _ -> []
                    shallowres @ deep
                | false ->
                    let shallowres, deepres = validationManager.Validate(shallow, newEntities)
                    let shallowres = shallowres @ (validationManager.ValidateLocalisation newEntities)
                    errorCache.[filepath] <- deepres
                    shallowres @ deepres

        log $"Update file Time: %i{timer.ElapsedMilliseconds}"
        res

    /// Parse an editor update without mutating the live resource maps.
    let prepareUpdateFileInteractive filepath (fileText: string option) =
        let fullPath = Path.GetFullPath filepath
        let kind, file, resourceInput =
            match fullPath with
            | x when x.EndsWith localisationExtension ->
                let file = fileText |> Option.defaultWith (fun () -> File.ReadAllText fullPath)
                LocalisationFile,
                file,
                LanguageFeatures.makeFileWithContentResourceInput fileManager fullPath file
            | x when PdxShaderFeatures.isShaderFile x ->
                let file = fileText |> Option.defaultWith (fun () -> File.ReadAllText(fullPath, encoding))
                ShaderFile,
                file,
                LanguageFeatures.makeFileWithContentResourceInput fileManager fullPath file
            | _ ->
                let file = fileText |> Option.defaultWith (fun () -> File.ReadAllText(fullPath, encoding))
                EntityFile,
                file,
                LanguageFeatures.makeEntityResourceInput fileManager fullPath file

        { filepath = fullPath
          fileText = file
          kind = kind
          resourceUpdate = resourceManager.PrepareFile resourceInput }

    /// Install a prepared editor resource. Parsing and rule validation are not
    /// part of this mutation phase, keeping the caller's write lock short.
    let commitUpdateFileInteractive (staged: StagedFileUpdate) =
        let resource, entity = resourceManager.CommitPreparedFile staged.resourceUpdate

        match staged.kind with
        | LocalisationFile ->
            match resource with
            | FileWithContentResource(_, r) -> this.LocalisationManager.UpdateLocalisationFile r
            | _ -> logWarning (sprintf "Localisation file failed to parse %s" staged.filepath)
        | ShaderFile -> ()
        | EntityFile ->
            afterUpdateFile this staged.filepath
            entity
            |> Option.iter (fun current -> validationManager.InvalidateInteractive [ current ])

        true

    /// Validate the committed editor resource without updating cross-file or
    /// deep-validation caches. Those caches are repopulated by save/deep lint.
    let validateFileInteractive (staged: StagedFileUpdate) =
        match staged.kind with
        | LocalisationFile -> []
        | ShaderFile -> PdxShaderFeatures.validate this.Resources staged.filepath staged.fileText
        | EntityFile ->
            match resourceManager.Api.GetEntityByFilePath staged.filepath with
            | Some entity -> validationManager.ValidateInteractiveDetached [ entity ]
            | None -> []

    let validateFileInteractiveCancellable (staged: StagedFileUpdate) (shouldCancel: unit -> bool) =
        if shouldCancel () then
            None
        else
            match staged.kind with
            | LocalisationFile -> Some []
            | ShaderFile ->
                let result = PdxShaderFeatures.validate this.Resources staged.filepath staged.fileText
                if shouldCancel () then None else Some result
            | EntityFile ->
                match resourceManager.Api.GetEntityByFilePath staged.filepath with
                | Some entity -> validationManager.ValidateInteractiveDetachedCancellable([ entity ], shouldCancel)
                | None -> Some []

    /// Compatibility wrapper for callers that do not split prepare/commit/validate.
    let updateFileInteractive filepath (fileText: string option) =
        log $"updateFileInteractive %s{filepath}"
        let timer = System.Diagnostics.Stopwatch.StartNew()
        let staged = prepareUpdateFileInteractive filepath fileText
        commitUpdateFileInteractive staged |> ignore
        let res = validateFileInteractive staged
        log $"Interactive update file time: %i{timer.ElapsedMilliseconds}"
        res

    let normaliseComparableFilePath filepath =
        let fullPath =
            try FileInfo(filepath).FullName.Replace('\\', '/')
            with _ -> filepath.Replace('\\', '/')
        if System.OperatingSystem.IsWindows() then fullPath.ToLowerInvariant() else fullPath

    let entityByFilePathWithFallback filepath =
        match resourceManager.Api.GetEntityByFilePath filepath with
        | Some entity -> Some entity
        | None ->
            let target = normaliseComparableFilePath filepath

            resourceManager.Api.AllEntities()
            |> Seq.tryFind (fun struct (entity, _) ->
                normaliseComparableFilePath entity.filepath = target)

    let validateFile (shallow: bool) filepath =
        log $"validateFile %s{filepath}"
        let timer = System.Diagnostics.Stopwatch.StartNew()
        let res =
            match entityByFilePathWithFallback filepath with
            | None -> []
            | Some entity ->
                match shallow with
                | true ->
                    let shallowres, _ = validationManager.Validate(shallow, [ entity ])
                    let shallowres = shallowres @ (validationManager.ValidateLocalisation [ entity ])
                    let deep = match errorCache.TryGetValue(filepath) with true, v -> v | _ -> []
                    shallowres @ deep
                | false ->
                    let shallowres, deepres = validationManager.Validate(shallow, [ entity ])
                    let shallowres = shallowres @ (validationManager.ValidateLocalisation [ entity ])
                    errorCache.[filepath] <- deepres
                    shallowres @ deepres

        log $"Validate file Time: %i{timer.ElapsedMilliseconds}"
        res

    let validateFileCancellable (shallow: bool) filepath (shouldCancel: unit -> bool) =
        log $"validateFileCancellable %s{filepath}"
        let timer = System.Diagnostics.Stopwatch.StartNew()
        let result =
            if shouldCancel () then
                None
            else
                match entityByFilePathWithFallback filepath with
                | None -> Some []
                | Some entity ->
                    match validationManager.ValidateCancellable(shallow, [ entity ], shouldCancel) with
                    | None -> None
                    | Some(shallowres, deepres) ->
                        if shouldCancel () then
                            None
                        else
                            let localisationErrors = validationManager.ValidateLocalisation [ entity ]
                            if shouldCancel () then
                                None
                            else
                                let shallowres = shallowres @ localisationErrors
                                if shallow then
                                    let deep = match errorCache.TryGetValue(filepath) with true, v -> v | _ -> []
                                    Some(shallowres @ deep)
                                else
                                    errorCache.[filepath] <- deepres
                                    Some(shallowres @ deepres)

        log $"Validate cancellable file Time: %i{timer.ElapsedMilliseconds}"
        result

    let validateFiles (filepaths: string list) =
        log $"validateFiles count=%i{filepaths.Length}"
        let timer = System.Diagnostics.Stopwatch.StartNew()
        let entities =
            filepaths
            |> List.distinctBy normaliseComparableFilePath
            |> List.choose entityByFilePathWithFallback

        let shallowres, deepres = validationManager.Validate(false, entities)
        log $"Validate files Time: %i{timer.ElapsedMilliseconds} files=%i{entities.Length}"
        shallowres @ deepres

    let initialLoad () =
        let timer = System.Diagnostics.Stopwatch()
        timer.Start()

        let embeddedFiles =
            settings.embedded.embeddedFiles
            |> List.map (fun (filePath: string, fileText) ->
                let newFilePath = filePath.Replace('\\', '/')
                if fileText = "" then
                    FileResourceInput
                        { scope = "embedded"
                          filepath = newFilePath
                          logicalpath = (fileManager.ConvertPathToLogicalPath newFilePath) }
                else
                    FileWithContentResourceInput
                        { scope = "embedded"
                          filepath = newFilePath
                          logicalpath = (fileManager.ConvertPathToLogicalPath newFilePath)
                          filetext = fileText
                          validate = false })

        let disableValidate (r, e) : Resource * Entity =
            match r with
            | EntityResource(s, er) ->
                EntityResource(
                    s,
                    { er with
                        validate = false
                        scope = "embedded" }
                )
            | x -> x
            , { e with validate = false }

        let cached =
            settings.embedded.cachedResourceData
            |> List.map (fun (r, e) -> CachedResourceInput(disableValidate (r, e)))

        let embedded = embeddedFiles.Concat(cached).ToArray()

        // Load vanilla cache BEFORE workspace files so that inline scripts
        // from the base game are available when processing mod files
        if fileManager.ShouldUseEmbedded then
            resourceManager.Api.UpdateFiles(embedded) |> ignore
            log $"Parsed embedded in %A{timer.ElapsedMilliseconds}"
            timer.Restart()
        else
            ()

        let files = fileManager.AllFilesByPath()
        log $"Parsing %i{files.Length} files"

        let filteredfiles =
            if settings.validation.validateVanilla then
                files
            else
                files
                |> Array.choose (function
                    | FileResourceInput f -> Some(FileResourceInput f)
                    | FileWithContentResourceInput f -> Some(FileWithContentResourceInput f)
                    | EntityResourceInput f ->
                        (if f.scope = "vanilla" then
                             Some(EntityResourceInput { f with validate = false })
                         else
                             Some(EntityResourceInput f))
                    | _ -> None)

        resourceManager.Api.UpdateFiles(filteredfiles) |> ignore
        log $"Parsed files in %A{timer.ElapsedMilliseconds}"

    let mutable prevRuleServiceRef: System.WeakReference option = None
    let mutable prevInfoServiceRef: System.WeakReference option = None
    let mutable prevCompletionServiceRef: System.WeakReference option = None

    let updateRulesCache () =
        // Capture old service instances for leak detection
        let oldRule = this.RuleValidationService |> Option.map (fun x -> System.WeakReference(x))
        let oldInfo = this.InfoService |> Option.map (fun x -> System.WeakReference(x))
        let oldCompletion = this.completionService |> Option.map (fun x -> System.WeakReference(x))

        let rules, info, completion = rulesManager.RefreshConfig()
        this.RuleValidationService <- Some rules
        this.InfoService <- Some info
        this.completionService <- Some completion
        this.RefreshValidationManager()
        LanguageFeatures.clearCompletionEntityCache ()
        LanguageFeatures.clearTypeReferenceIndexCache ()

        // Check if previous instances were collected (diagnostic)
        match prevRuleServiceRef, prevInfoServiceRef, prevCompletionServiceRef with
        | Some r, Some i, Some c ->
            log $"[MemDiag:WeakRef] prev services alive: rule={r.IsAlive} info={i.IsAlive} completion={c.IsAlive}"
        | _ -> ()
        prevRuleServiceRef <- oldRule
        prevInfoServiceRef <- oldInfo
        prevCompletionServiceRef <- oldCompletion

    let updateScriptedTypesCache files typeKeys =
        let rules, info, completion = rulesManager.RefreshScriptedTypes(files, typeKeys)
        this.RuleValidationService <- Some rules
        this.InfoService <- Some info
        this.completionService <- Some completion
        this.RefreshValidationManager()
        LanguageFeatures.clearCompletionEntityCache ()
        LanguageFeatures.clearTypeReferenceIndexCache ()

    let initialConfigRules () =
        log "Initial config rules update"
        let timer = new System.Diagnostics.Stopwatch()
        timer.Start()
        localisationManager.UpdateAllLocalisation()
        log (sprintf "Loc updated in %A" timer.ElapsedMilliseconds)
        timer.Restart()

        if settings.rules.IsSome then
            rulesManager.LoadBaseConfig(settings.rules.Value)
        else
            ()

        log (sprintf "Rules loaded in %A" timer.ElapsedMilliseconds)
        timer.Restart()
        updateRulesCache ()
        log (sprintf "Rules cache updated in %A" timer.ElapsedMilliseconds)
        timer.Restart()
        this.Resources.ForceRecompute()
        log (sprintf "Resource recomputer in %A" timer.ElapsedMilliseconds)
        timer.Restart()
        localisationManager.UpdateAllLocalisation()
        log (sprintf "Loc updated again in %A" timer.ElapsedMilliseconds)

    do
        lookup.rootFolders <- settings.rootDirectories

        if debugSettings.EarlyStop >= GameInitLoad then
            initialLoad ()

    member _.RuleValidationService = ruleValidationService

    member _.RuleValidationService
        with set value = ruleValidationService <- value
    // member val ruleValidationService : RuleValidationService<'S> option = None with get, set
    member _.InfoService = infoService

    member _.InfoService
        with set value = infoService <- value
    // member val infoService : InfoService<'S> option = None with get, set
    member val completionService: CompletionService option = None with get, set

    member _.Resources: IResourceAPI<'T> = resourceManager.Api
    member _.ResourceManager = resourceManager
    member _.Lookup: 'L = lookup
    // member __.AllLocalisation() = localisationManager.allLocalisation()
    // member __.ValidatableLocalisation() = localisationManager.validatableLocalisation()
    member _.FileManager = (fun () -> fileManager) ()
    member _.LocalisationManager: LocalisationManager<'T> = localisationManager
    member _.ValidationManager = validationManager
    member _.Settings = settings
    member _.UpdateFile shallow file text = updateFile shallow file text
    member _.UpdateFileInteractive file text = updateFileInteractive file text
    member _.PrepareUpdateFileInteractive file text = prepareUpdateFileInteractive file text
    member _.CommitUpdateFileInteractive staged = commitUpdateFileInteractive staged
    member _.ValidateFileInteractive staged = validateFileInteractive staged
    member _.ValidateFileInteractiveCancellable staged shouldCancel =
        validateFileInteractiveCancellable staged shouldCancel
    member _.ValidateFile shallow file = validateFile shallow file
    member _.ValidateFileCancellable shallow file shouldCancel =
        validateFileCancellable shallow file shouldCancel
    member _.ValidateFiles files = validateFiles files
    member _.RemoveFile file = resourceManager.Api.RemoveFile file

    member _.RefreshValidationManager() =
        validationManager <-
            ValidationManager(
                validationSettings,
                validationServices (),
                locFunctions >> snd,
                defaultContext,
                (if debugMode then noneContext else defaultContext),
                validationManager.ErrorCache()
            )
    
    /// 清理不存在文件的缓存条目，防止内存泄漏
    member _.CleanupCache(existingFiles: Set<string>) =
        validationManager.Cleanup existingFiles
        // 清理 errorCache 中不存在文件的条目
        for key in errorCache.Keys |> Seq.toArray do
            if not (existingFiles.Contains key) then
                errorCache.TryRemove(key) |> ignore

    /// 清除单个文件的深度验证缓存。
    /// 在文件编辑时调用，确保 shallow lint 不会返回过时的 deep 错误。
    member _.InvalidateFileCache(filepath: string) =
        errorCache.TryRemove(filepath) |> ignore
        validationManager.InvalidateFile filepath

    member _.RefreshInlineScriptCallers(scriptNames: string list) =
        let callers = resourceManager.Api.RefreshInlineScriptCallers scriptNames
        for filepath in callers do
            errorCache.TryRemove(filepath) |> ignore
        callers

    member this.InfoAtPos pos file text =
        if PdxShaderFeatures.isShaderFile file then
            PdxShaderFeatures.infoAtPos this.Resources pos file text
        else
            LanguageFeatures.symbolInformationAtPos
                this.FileManager
                this.ResourceManager
                this.InfoService
                this.Lookup
                pos
                file
                text

    member _.OverrideModeAtPath(file: string) =
        let logicalPath =
            (try
                fileManager.ConvertPathToLogicalPath file
             with _ ->
                file)

        ExtendedConfigMetadata.tryFindPriorityForPath logicalPath lookup.extendedConfigMetadata

    member _.OverrideModes() =
        lookup.extendedConfigMetadata.priorities
        |> Map.toSeq
        |> Seq.map snd
        |> Seq.sortBy (fun p -> p.path)
        |> Seq.toArray

    member _.OverrideModesInfo() =
        lookup.extendedConfigMetadata.overrideModesInfo
        |> Map.toSeq
        |> Seq.map snd
        |> Seq.sortBy (fun m -> m.id)
        |> Seq.toArray

    member _.ReplaceConfigRules rules = rulesManager.LoadBaseConfig rules
    member _.RefreshCaches() = updateRulesCache ()

    member _.PrepareRefreshCaches() = rulesManager.PrepareRefreshConfig()

    member this.CommitRefreshCaches(staged) =
        match rulesManager.CommitRefreshConfig(staged) with
        | Some(rules, info, completion) ->
            this.RuleValidationService <- Some rules
            this.InfoService <- Some info
            this.completionService <- Some completion
            this.RefreshValidationManager()
            LanguageFeatures.clearCompletionEntityCache ()
            LanguageFeatures.clearTypeReferenceIndexCache ()
            true
        | None -> false

    member _.RefreshScriptedTypesForFiles(files, typeKeys) = updateScriptedTypesCache files typeKeys

    member _.PrepareScriptedTypesForFiles(files, typeKeys) =
        rulesManager.PrepareScriptedTypes(files, typeKeys)

    member this.CommitScriptedTypesForFiles(staged) =
        match rulesManager.CommitScriptedTypes(staged) with
        | Some(rules, info, completion) ->
            this.RuleValidationService <- Some rules
            this.InfoService <- Some info
            this.completionService <- Some completion
            this.RefreshValidationManager()
            LanguageFeatures.clearCompletionEntityCache ()
            LanguageFeatures.clearTypeReferenceIndexCache ()
            true
        | None -> false

    member _.PrepareTypeIndexForFiles(files, typeKeys) =
        rulesManager.PrepareTypeIndex(files, typeKeys)

    member _.CommitTypeIndexForFiles(staged) =
        rulesManager.CommitTypeIndex(staged)

    member this.RemoveTypeIndexForFiles(files, typeKeys) =
        for file in files do
            this.RemoveFile file |> ignore
        match rulesManager.PrepareTypeIndex(files, typeKeys) with
        | Some staged -> this.CommitTypeIndexForFiles staged
        | None -> false

    member _.InitialConfigRules() = initialConfigRules ()
    member private _.DebugSettings = debugSettings

    static member CreateGame settings afterInit =
        let game = GameObject(settings)

        if game.DebugSettings.EarlyStop >= GameAfterInit then
            afterInit game

        if game.DebugSettings.EarlyStop >= GameInitialConfigRules then
            game.InitialConfigRules()

        game
