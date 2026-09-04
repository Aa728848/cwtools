namespace CWTools.Games.Jomini

open CWTools.Game
open CWTools.Localisation
open CWTools.Games
open CWTools.Common
open System.IO
open CWTools.Validation.Common.CommonValidation
open CWTools.Process.Scopes
open System.Text
open CWTools.Games.LanguageFeatures
open CWTools.Games.Helpers
open CWTools.Parser

type JominiGameObject = GameObject<JominiComputedData, JominiLookup>

/// Per-game knobs shared by the Jomini-derived games (VIC3, EU5, CK3).
type JominiGameProfile =
    { gameName: string
      defaultLang: Lang
      oneToOneScopes: (string * (CWTools.Process.Scopes.ScopeContext * bool -> CWTools.Process.Scopes.ScopeContext * bool)) list
      oneToOneScopesNames: string list
      localisationService: (string * string) list -> ILocalisationAPICreator
      scriptFolders: string array
      afterInit: JominiGameObject -> unit
      includeModifierValidators: bool }

module JominiGameFunctions =
    type GameObject = JominiGameObject

    let createEmbeddedSettings embeddedFiles cachedResourceData (configs: (string * string) list) cachedRuleMetadata =
        initializeScopesAndModifierCategories configs (fun _ -> [||]) (fun _ -> [||])

        let modifiers = getActualModifiers configs

        let jominiLocDataTypes =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "data_types.log")
            |> Option.map (fun (fn, ft) ->
                DataTypeParser.parseDataTypesStreamRes (
                    new MemoryStream(System.Text.Encoding.GetEncoding(1252).GetBytes(ft))
                ))
            |> Option.defaultValue
                { DataTypeParser.JominiLocDataTypes.promotes = Map.empty
                  confidentFunctions = Map.empty
                  DataTypeParser.JominiLocDataTypes.functions = Map.empty
                  DataTypeParser.JominiLocDataTypes.dataTypes = Map.empty
                  DataTypeParser.JominiLocDataTypes.dataTypeNames = Set.empty }

        let irEventTargetLinks =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "links.cwt")
            |> Option.map (fun (fn, ft) ->
                UtilityParser.loadEventTargetLinks
                    scopeManager.AnyScope
                    (scopeManager.ParseScope())
                    scopeManager.AllScopes
                    fn
                    ft)
            |> Option.defaultValue (CWTools.Process.Scopes.IR.scopedEffects |> List.map SimpleLink)

        let effects =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "effects.log")
            |> Option.bind (fun (fn, ft) ->
                JominiParser.parseEffectStreamRes (
                    new MemoryStream(System.Text.Encoding.GetEncoding(1252).GetBytes(ft))
                ))
            |> Option.map (JominiParser.processEffects scopeManager.ParseScopes)
            |> Option.defaultWith (fun () ->
                eprintfn "effects.log was not found in config"
                [])

        let triggers =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "triggers.log")
            |> Option.bind (fun (fn, ft) ->
                JominiParser.parseTriggerStreamRes (
                    new MemoryStream(System.Text.Encoding.GetEncoding(1252).GetBytes(ft))
                ))
            |> Option.map (JominiParser.processTriggers scopeManager.ParseScopes)
            |> Option.defaultWith (fun () ->
                eprintfn "triggers.log was not found in config"
                [])

        let featureSettings = getFeatureSettings configs

        { triggers = triggers
          effects = effects
          modifiers = modifiers
          embeddedFiles = embeddedFiles
          cachedResourceData = cachedResourceData
          localisationCommands = Jomini jominiLocDataTypes
          eventTargetLinks = irEventTargetLinks
          cachedRuleMetadata = cachedRuleMetadata
          featureSettings = featureSettings }

    let initGame (setupSettings: GameSetupSettings<JominiLookup>) (profile: JominiGameProfile) =
        let validationSettings =
            { validators = CWTools.Validation.ValidationCore.toLocalStructureValidators [ validateIfWithNoEffect, "ifnoeffect" ]
              globalValidators = []
              dynamicValidators = []
              experimentalValidators = []
              heavyExperimentalValidators = []
              experimental = false
              fileValidators = []
              globalFileValidators = []
              lookupValidators = []
              globalLookupValidators =
                if profile.includeModifierValidators then
                    [ validateUndefinedModifierTypes, "undefinedmodifiers"
                      validateDefinitionInjections, "definitioninjections"
                      validateConfiguredOnActionEventTypes, "configuredonactioneventtypes" ]
                    @ commonValidationRules
                else
                    commonValidationRules
              lookupFileValidators = []
              scriptedParamsValidators = []
              useRules = true
              debugRulesOnly = false
              localisationValidators = [] }

        let embeddedSettings =
            match setupSettings.embedded with
            | FromConfig(ef, crd) ->
                createEmbeddedSettings
                    ef
                    crd
                    (setupSettings.rules
                     |> Option.map (fun r -> r.ruleFiles)
                     |> Option.defaultValue [])
                    None
            | Metadata cmd ->
                createEmbeddedSettings
                    []
                    []
                    (setupSettings.rules
                     |> Option.map (fun r -> r.ruleFiles)
                     |> Option.defaultValue [])
                    (Some cmd)
            | ManualSettings e -> e

        let settings =
            { rootDirectories = setupSettings.rootDirectories
              excludeGlobPatterns = setupSettings.excludeGlobPatterns
              embedded = embeddedSettings
              GameSettings.rules = setupSettings.rules
              validation = setupSettings.validation
              scriptFolders = setupSettings.scriptFolders
              modFilter = setupSettings.modFilter
              initialLookup = JominiLookup()
              maxFileSize = setupSettings.maxFileSize
              enableInlineScripts = false }

        if scopeManager.Initialized |> not then
            eprintfn "%A has no scopes" (settings.rootDirectories |> Array.head)
        else
            ()

        let settings =
            { settings with
                initialLookup = JominiLookup() }

        let changeScope =
            Scopes.createJominiChangeScope
                profile.oneToOneScopes
                (Scopes.complexVarPrefixFun "variable:from:" "variable:")

        let jominiLocDataTypes =
            settings.embedded.localisationCommands
            |> function
                | Jomini dts -> Some dts
                | _ -> None

        let processLocalisationFunction lookup =
            (createJominiLocalisationFunctions jominiLocDataTypes lookup)

        let rulesManagerSettings =
            { rulesSettings = settings.rules
              useFormulas = true
              stellarisScopeTriggers = false
              parseScope = scopeManager.ParseScope()
              allScopes = scopeManager.AllScopes
              anyScope = scopeManager.AnyScope
              scopeGroups = scopeManager.ScopeGroups
              changeScope = changeScope
              scopeContextOverride = fun _ _ -> None
              defaultContext = CWTools.Process.Scopes.Scopes.defaultContext
              defaultLang = profile.defaultLang
              oneToOneScopesNames = profile.oneToOneScopesNames
              loadConfigRulesHook = Hooks.loadConfigRulesHook
              refreshConfigBeforeFirstTypesHook = Hooks.refreshConfigBeforeFirstTypesHook
              refreshConfigAfterFirstTypesHook = Hooks.refreshConfigAfterFirstTypesHook true
              refreshConfigAfterVarDefHook = Hooks.refreshConfigAfterVarDefHook true
              locFunctions = processLocalisationFunction }

        let scriptFolders = profile.scriptFolders

        let game =
            GameObject.CreateGame
                ((settings,
                  profile.gameName,
                  scriptFolders,
                  Compute.Jomini.computeJominiData,
                  Compute.Jomini.computeJominiDataUpdate,
                  profile.localisationService,
                  processLocalisationFunction,
                  CWTools.Process.Scopes.Scopes.defaultContext,
                  CWTools.Process.Scopes.Scopes.noneContext,
                  Encoding.UTF8,
                  Encoding.GetEncoding(1252),
                  validationSettings,
                  Hooks.globalLocalisation,
                  (fun _ _ -> ()),
                  ".yml",
                  rulesManagerSettings,
                  setupSettings.debugSettings))
                profile.afterInit

        let defaultLang =
            settings.validation.langs
            |> Array.tryHead
            |> Option.defaultValue profile.defaultLang

        (game, defaultLang)

open JominiGameFunctions

type JominiGame(setupSettings: GameSetupSettings<JominiLookup>, profile: JominiGameProfile) =
    inherit CWToolsGameBase<JominiComputedData, JominiLookup>(initGame setupSettings profile)
