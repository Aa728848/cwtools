namespace CWTools.Games.VIC2

open CWTools.Game
open CWTools.Localisation
open CWTools.Utilities.Utils2
open CWTools.Games
open CWTools.Common
open CWTools.Localisation.VIC2Localisation
open System.IO
open CWTools.Validation.Common.CommonValidation
open CWTools.Rules
open CWTools.Common.VIC2Constants
open CWTools.Process.Scopes.VIC2
open CWTools.Process.Scopes.Scopes
open System.Text
open CWTools.Games.LanguageFeatures
open System
open CWTools.Games.Helpers
open CWTools.Parser
open CWTools.Process.Localisation
open Microsoft.FSharp.Collections

type VIC2Settings = GameSetupSettings<VIC2Lookup>

module VIC2GameFunctions =
    type GameObject = GameObject<VIC2ComputedData, VIC2Lookup>

    let createLocDynamicSettings (lookup: Lookup) =
        let eventtargets =
            (lookup.varDefInfo.TryFind "event_target"
             |> Option.defaultValue [||]
             |> Array.map fst)

        let definedvars =
            (lookup.varDefInfo.TryFind "variable"
             |> Option.defaultValue [||]
             |> Array.map fst)

        { scriptedLocCommands = lookup.scriptedLoc |> Array.map (fun s -> s, [ scopeManager.AnyScope ])
          eventTargets = eventtargets |> Array.map (fun s -> s, scopeManager.AnyScope)
          setVariables = definedvars |> IgnoreCaseStringSet }


    let updateModifiers (game: GameObject) =
        game.Lookup.coreModifiers <- game.Settings.embedded.modifiers

    let updateProvinces (game: GameObject) =
        game.Lookup.VIC2provinces <- loadDefinitionCsvProvinces game.Resources



    let refreshConfigBeforeFirstTypesHook (lookup: VIC2Lookup) _ _ =
        let modifierEnums =
            { key = "modifiers"
              values = lookup.coreModifiers |> Array.map _.tag
              description = "Modifiers"
              valuesWithRange = lookup.coreModifiers |> Array.map (fun m -> m.tag, None) }

        let provinceEnums =
            { key = "provinces"
              description = "provinces"
              values = lookup.VIC2provinces
              valuesWithRange = lookup.VIC2provinces |> Array.map (fun x -> x, None) }

        lookup.enumDefs <-
            lookup.enumDefs
            |> Map.add modifierEnums.key (modifierEnums.description, modifierEnums.valuesWithRange)
            |> Map.add provinceEnums.key (provinceEnums.description, provinceEnums.valuesWithRange)

    let afterInit (game: GameObject) =
        updateProvinces (game)
        updateModifiers (game)

    let createEmbeddedSettings embeddedFiles cachedResourceData (configs: (string * string) list) cachedRuleMetadata =
        initializeScopesAndModifierCategories configs defaultScopeInputs defaultModifiersInputs

        let vic2Mods = getActualModifiers configs

        let vic2LocCommands =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "localisation.cwt")
            |> Option.map (fun (fn, ft) -> UtilityParser.loadLocCommands fn ft)
            |> Option.defaultValue ([], [], [])

        let vic2EventTargetLinks =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "links.cwt")
            |> Option.map (fun (fn, ft) ->
                UtilityParser.loadEventTargetLinks
                    scopeManager.AnyScope
                    (scopeManager.ParseScope())
                    scopeManager.AllScopes
                    fn
                    ft)
            |> Option.defaultValue []

        let featureSettings = getFeatureSettings configs

        { triggers = []
          effects = []
          modifiers = vic2Mods
          embeddedFiles = embeddedFiles
          cachedResourceData = cachedResourceData
          localisationCommands = Legacy vic2LocCommands
          eventTargetLinks = vic2EventTargetLinks
          cachedRuleMetadata = cachedRuleMetadata
          featureSettings = featureSettings }

    let initGame (setupSettings: VIC2Settings) =
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
              globalLookupValidators = commonValidationRules
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
              initialLookup = VIC2Lookup()
              maxFileSize = setupSettings.maxFileSize
              enableInlineScripts = false }

        if scopeManager.Initialized |> not then
            eprintfn "%A has no scopes" (settings.rootDirectories |> Array.head)
        else
            ()

        let locSettings =
            settings.embedded.localisationCommands
            |> function
                | Legacy(l, v, links) ->
                    (if l.Length = 0 then
                         Legacy([], [], [])
                     else
                         Legacy(l, v, links))
                | _ -> Legacy([], [], [])

        let settings =
            { settings with
                embedded =
                    { settings.embedded with
                        localisationCommands = locSettings }
                initialLookup = VIC2Lookup() }

        let legacyLocDataTypes =
            settings.embedded.localisationCommands
            |> function
                | Legacy(c, v, links) -> (c, v, links)
                | _ -> ([], [], [])

        let processLocalisationFunction lookup =
            (createLocalisationFunctions VIC2.locStaticSettings createLocDynamicSettings legacyLocDataTypes lookup)

        let rulesManagerSettings =
            { rulesSettings = settings.rules
              useFormulas = false
              stellarisScopeTriggers = false
              parseScope = scopeManager.ParseScope()
              allScopes = scopeManager.AllScopes
              anyScope = scopeManager.AnyScope
              scopeGroups = scopeManager.ScopeGroups
              changeScope = changeScope
              scopeContextOverride = fun _ _ -> None
              defaultContext = defaultContext
              defaultLang = VIC2 VIC2Lang.English
              oneToOneScopesNames = oneToOneScopesNames
              loadConfigRulesHook = Hooks.loadConfigRulesHook
              refreshConfigBeforeFirstTypesHook = refreshConfigBeforeFirstTypesHook
              refreshConfigAfterFirstTypesHook = Hooks.refreshConfigAfterFirstTypesHook false
              refreshConfigAfterVarDefHook = Hooks.refreshConfigAfterVarDefHook false
              locFunctions = processLocalisationFunction }

        let game =
            GameObject<VIC2ComputedData, VIC2Lookup>.CreateGame
                ((settings,
                  "victoria 2",
                  scriptFolders,
                  Compute.computeVIC2Data,
                  Compute.computeVIC2DataUpdate,
                  (VIC2LocalisationService >> (fun f -> f :> ILocalisationAPICreator)),
                  processLocalisationFunction,
                  defaultContext,
                  noneContext,
                  Encoding.UTF8,
                  Encoding.GetEncoding(1252),
                  validationSettings,
                  Hooks.globalLocalisation,
                  (fun _ _ -> ()),
                  ".yml",
                  rulesManagerSettings,
                  setupSettings.debugSettings))
                afterInit

        let defaultLang =
            settings.validation.langs
            |> Array.tryHead
            |> Option.defaultValue (VIC2 VIC2Lang.English)

        (game, defaultLang)

open VIC2GameFunctions

type VIC2Game(setupSettings: VIC2Settings) =
    inherit CWToolsGameBase<VIC2ComputedData, VIC2Lookup>(initGame setupSettings)
