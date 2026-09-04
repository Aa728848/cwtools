namespace CWTools.Games

open CWTools.Common
open CWTools.Process
open CWTools.Parser.Types
open CWTools.Utilities.Position
open CWTools.Game
open CWTools.Games.Helpers
open CWTools.Games.LanguageFeatures
open CWTools.Validation

[<AbstractClass>]
type CWToolsGameBase<'T, 'L when 'T :> ComputedData and 'L :> Lookup>
    (
        game: GameObject<'T, 'L>,
        defaultLang: Lang,
        parseErrors: unit -> (string * string * FParsec.Position) list,
        localisationErrors: bool * bool -> CWError list
    ) =

    let resources = game.Resources
    let lookup = game.Lookup
    let fileManager = game.FileManager
    let references = References<'T>(resources, lookup, game.LocalisationManager.GetCleanLocalisationAPIs())

    member _.Lookup: 'L = lookup
    member _.Resources = resources
    member _.FileManager = fileManager

    new (game: GameObject<'T, 'L>, defaultLang: Lang) =
        let defaultParseErrors () =
            game.Resources.GetResources()
            |> List.choose (function
                | EntityResource(_, e) -> Some e
                | _ -> None)
            |> List.choose (fun r ->
                r.result
                |> function
                    | Fail result when r.validate -> Some(r.filepath, result.error, result.position)
                    | _ -> None)
        let defaultLocalisationErrors (force, forceGlobal) =
            getLocalisationErrors game Hooks.globalLocalisation (force, forceGlobal)
        CWToolsGameBase(game, defaultLang, defaultParseErrors, defaultLocalisationErrors)

    new (gameAndLang: GameObject<'T, 'L> * Lang) =
        CWToolsGameBase(fst gameAndLang, snd gameAndLang)

    interface IGame<'T> with
        member _.ParserErrors() = parseErrors ()
        member _.ValidationErrors() =
            let s, d = game.ValidationManager.Validate(false, resources.ValidatableEntities()) in s @ d
        member _.LocalisationErrors(force: bool, forceGlobal: bool) =
            localisationErrors (force, forceGlobal)
        member _.Folders() = fileManager.AllFolders()
        member _.AllFiles() = resources.GetResources()
        member _.AllLoadedLocalisation() =
            game.LocalisationManager.LocalisationFileNames()
        member _.ScriptedTriggers() = lookup.triggers
        member _.ScriptedEffects() = lookup.effects
        member _.ScriptedVariables() = lookup.scriptedVariables
        member _.StaticModifiers() = [||]
        member _.UpdateFile shallow file text = game.UpdateFile shallow file text
        member _.UpdateFileInteractive file text = game.UpdateFileInteractive file text
        member _.PrepareUpdateFileInteractive file text = game.PrepareUpdateFileInteractive file text
        member _.CommitUpdateFileInteractive staged = game.CommitUpdateFileInteractive staged
        member _.ValidateFileInteractive staged = game.ValidateFileInteractive staged
        member _.ValidateOverlayFile(file, text) = game.ValidateOverlayFile file text
        member _.ValidateOverlayFilesCancellable(files, shouldCancel) =
            game.ValidateOverlayFilesCancellable files shouldCancel
        member _.ValidateFile shallow file = game.ValidateFile shallow file
        member _.ValidateFiles files = game.ValidateFiles files
        member _.ValidateFilesLocalCancellable(files, shouldCancel) =
            game.ValidateFilesLocalCancellable(files, shouldCancel)
        member _.AllEntities() = resources.AllEntities()
        member _.References() = references
        member _.Complete pos file text =
            completion fileManager game.completionService game.InfoService game.ResourceManager pos file text
        member _.ScopesAtPos pos file text =
            scopesAtPos fileManager game.ResourceManager game.InfoService scopeManager.AnyScope pos file text
        member _.GoToType pos file text =
            getInfoAtPos
                fileManager
                game.ResourceManager
                game.InfoService
                game.LocalisationManager
                lookup
                (game.Settings.validation.langs |> Array.tryHead |> Option.defaultValue defaultLang)
                pos
                file
                text
        member _.FindAllRefs pos file text =
            findAllRefsFromPos fileManager game.ResourceManager game.InfoService pos file text
        member _.FindAllRefsByType typeName id =
            findAllRefsByType game.ResourceManager game.InfoService typeName id
        member _.TypeReferenceIndex() =
            getOrBuildTypeReferenceIndex game.ResourceManager game.InfoService
        member _.InfoAtPos pos file text = game.InfoAtPos pos file text
        member _.OverrideModeAtPath file = game.OverrideModeAtPath file
        member _.OverrideModes() = game.OverrideModes()
        member _.OverrideModesInfo() = game.OverrideModesInfo()
        member _.ReplaceConfigRules rules =
            game.ReplaceConfigRules
                { ruleFiles = rules
                  validateRules = true
                  debugRulesOnly = false
                  debugMode = false }
        member _.PrepareConfigRules rules =
            game.PrepareConfigRules
                { ruleFiles = rules
                  validateRules = true
                  debugRulesOnly = false
                  debugMode = false }
        member _.CommitConfigRules staged = game.CommitConfigRules staged
        member _.RefreshCaches() = game.RefreshCaches()
        member _.PrepareRefreshCaches() = game.PrepareRefreshCaches()
        member _.CommitRefreshCaches(staged) = game.CommitRefreshCaches(staged)
        member _.RefreshScriptedTypes files =
            let typeKeys = game.IncrementalTypeKeysForFiles files
            if typeKeys.IsEmpty then false
            else
                game.RefreshScriptedTypesForFiles(files, typeKeys)
                true
        member _.RemoveScriptedTypes files = game.RemoveIncrementalScriptedTypes files
        member _.PrepareFileDeletion(files, scripted) =
            game.PrepareIncrementalFileDeletion(files, scripted)
        member _.CommitFileDeletion staged =
            game.CommitFileDeletionForFiles staged
        member _.PrepareScriptedTypes(files, additionalSemanticChanged) =
            game.PrepareIncrementalScriptedTypes(files, additionalSemanticChanged)
        member _.CommitScriptedTypes staged = game.CommitScriptedTypesForFiles staged
        member _.RefreshLocalisationCaches() =
            game.LocalisationManager.UpdateProcessedLocalisation()
        member _.CleanupCache(existingFiles) = game.CleanupCache existingFiles
        member _.InvalidateFileCache(filepath) = game.InvalidateFileCache filepath
        member _.ForceRecompute() = resources.ForceRecompute()
        member _.ForceDynamicParameterData(timeoutMs, maxEntities) =
            resources.ForceDynamicParameterData(timeoutMs, maxEntities)
        member _.ForceDynamicParameterDataForFiles filepaths =
            resources.ForceDynamicParameterDataForFiles filepaths
        member _.GetInlineScriptCallers scriptName = resources.GetInlineScriptCallers scriptName
        member _.RefreshInlineScriptCallers scriptNames = game.RefreshInlineScriptCallers scriptNames
        member _.PrepareInlineScriptCallers scriptNames = game.PrepareInlineScriptCallers scriptNames
        member _.CommitInlineScriptCallers staged = game.CommitInlineScriptCallers staged
        member _.Types() = game.Lookup.typeDefInfo
        member _.TypeDefs() = game.Lookup.typeDefs
        member _.GetPossibleCodeEdits file text = []
        member _.GetCodeEdits file text = None
        member _.GetEventGraphData: GraphDataRequest =
            (fun files gameType depth ->
                graphEventDataForFiles references game.ResourceManager lookup files gameType depth)
        member _.GetEmbeddedMetadata() =
            getEmbeddedMetadata lookup game.LocalisationManager game.ResourceManager

    interface IIncrementalTypeIndex with
        member _.PrepareTypeIndex files = game.PrepareIncrementalTypeIndex files
        member _.CommitTypeIndex staged = game.CommitTypeIndexForFiles staged
        member _.RemoveTypeIndex files = game.RemoveIncrementalTypeIndex files

    interface IIncrementalLocalisation with
        member _.IsLocalisationFile filepath = game.IsLocalisationFile filepath
        member _.PeekLocalisationDelta owner = game.PeekLocalisationDelta owner
        member _.AckLocalisationDelta cursor = game.AckLocalisationDelta cursor
        member _.DiscardLocalisationDelta cursor = game.DiscardLocalisationDelta cursor
        member _.TakeLocalisationDelta() = game.TakeLocalisationDelta()
        member _.ValidateLocalisationDelta delta = game.ValidateIncrementalLocalisationDelta delta
        member _.PrepareLocalisationRefresh owner =
            game.PrepareLocalisationRefresh(owner, game.ValidateIncrementalLocalisationDelta)
        member _.TryCommitLocalisationRefresh staged = game.TryCommitLocalisationRefresh staged
        member _.DiscardLocalisationRefresh staged = game.DiscardLocalisationRefresh staged
        member _.ValidateLocalisationFiles files = game.ValidateIncrementalLocalisationFiles files
        member _.RemoveLocalisationFile filepath = game.RemoveIncrementalLocalisationFile filepath

    interface ISemanticDeltaProvider with
        member _.SemanticSignatureForFile filepath = game.SemanticSignatureForFile filepath
