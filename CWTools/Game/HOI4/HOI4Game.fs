namespace CWTools.Games.HOI4

open CSharpHelpers
open CWTools.Common.HOI4Constants
open CWTools.Game
open CWTools.Localisation
open CWTools.Utilities.Utils2
open CWTools.Games
open CWTools.Common
open CWTools.Localisation.HOI4
open CWTools.Utilities
open System.IO
open CWTools.Validation.Common.CommonValidation
open CWTools.Rules
open CWTools.Process.Scopes.HOI4
open CWTools.Process.Scopes.Scopes
open System.Text
open CWTools.Games.LanguageFeatures
open System
open CWTools.Games.Helpers
open CWTools.Parser
open CWTools.Process.Localisation
open System.Linq

type HOI4Settings = GameSetupSettings<HOI4Lookup>

module HOI4GameFunctions =
    type GameObject = GameObject<HOI4ComputedData, HOI4Lookup>

    let createLocDynamicSettings (lookup: Lookup) =
        //eprintfn "clds %A" (lookup.enumDefs.TryFind "country_tags")
        let eventtargets =
            seq {

                yield!
                    lookup.varDefInfo.TryFind "event_target"
                    |> Option.defaultValue [||]
                    |> Seq.map fst

                yield!
                    lookup.varDefInfo.TryFind "global_event_target"
                    |> Option.defaultValue [||]
                    |> Seq.map fst

                yield! lookup.typeDefInfo.TryFind "state" |> Option.defaultValue [||] |> Seq.map _.id

                yield!
                    lookup.enumDefs.TryFind "country_tags"
                    |> Option.map (fun x -> (snd x) |> Seq.map fst)
                    |> Option.defaultValue Seq.empty
            }

        let definedvars =
            seq {
                yield! (lookup.varDefInfo.TryFind "variable" |> Option.defaultValue [||] |> Seq.map fst)

                yield!
                    (lookup.varDefInfo.TryFind "saved_name"
                     |> Option.defaultValue [||]
                     |> Seq.map fst)

                yield!
                    (lookup.varDefInfo.TryFind "exiled_ruler"
                     |> Option.defaultValue [||]
                     |> Seq.map fst)
            }
            |> IgnoreCaseStringSet

        { scriptedLocCommands =
            lookup.scriptedLoc
            |> Seq.map (fun s -> s, [ scopeManager.AnyScope ])
            |> Array.ofSeq
          eventTargets = eventtargets |> Seq.map (fun s -> s, scopeManager.AnyScope) |> Array.ofSeq
          setVariables = definedvars }

    let updateModifiers (game: GameObject) =
        game.Lookup.coreModifiers <- game.Settings.embedded.modifiers

    let updateProvinces (game: GameObject) =
        game.Lookup.HOI4provinces <- loadDefinitionCsvProvinces game.Resources

    let updateScriptedLoc (game: GameObject) =
        let rawLocs =
            game.Resources.AllEntities()
            |> Seq.choose (function
                | struct (f, _) when f.filepath.Contains("scripted_localisation") -> Some f.entity
                | _ -> None)
            |> Seq.collect _.Nodes
            |> Seq.map (fun l -> l.TagText "name")
            |> Seq.toArray

        game.Lookup.embeddedScriptedLoc <-
            game.Settings.embedded.cachedRuleMetadata
            |> Option.map _.scriptedLoc
            |> Option.defaultValue [||]

        game.Lookup.scriptedLoc <- rawLocs

    let ruleToEffect (rule, effectType) =
        let r, o = rule

        let name =
            match r with
            | LeafRule(SpecificField(SpecificValue n), _) -> StringResource.stringManager.GetStringForID n.normal
            | NodeRule(SpecificField(SpecificValue n), _) -> StringResource.stringManager.GetStringForID n.normal
            | _ -> ""

        DocEffect(name, o.requiredScopes, o.pushScope, effectType, o.description |> Option.defaultValue "", "")
        :> Effect

    let updateScriptedEffects (rules: RootRule array) (states: _ array) (countries: _ array) =
        let effects =
            rules
            |> Array.choose (function
                | AliasRule("effect", r) -> Some(ruleToEffect (r, EffectType.Effect))
                | _ -> None)

        let stateEffects =
            states
            |> Array.map (fun p ->
                ScopedEffect(
                    p,
                    scopeManager.AllScopes,
                    Some(scopeManager.ParseScope () "State"),
                    EffectType.Link,
                    defaultDesc,
                    "",
                    true
                )
                :> Effect)

        let countryEffects =
            countries
            |> Array.map (fun p ->
                ScopedEffect(
                    p,
                    scopeManager.AllScopes,
                    Some(scopeManager.ParseScope () "Country"),
                    EffectType.Link,
                    defaultDesc,
                    "",
                    true
                )
                :> Effect)

        Array.concat [| effects; stateEffects; countryEffects |]

    let updateScriptedTriggers (rules: RootRule array) (states: _ array) (countries: _ array) =
        let effects =
            rules
            |> Array.choose (function
                | AliasRule("trigger", r) -> Some(ruleToEffect (r, EffectType.Trigger))
                | _ -> None)

        let stateEffects =
            (states
             |> Array.map (fun p ->
                 ScopedEffect(
                     p,
                     scopeManager.AllScopes,
                     Some(scopeManager.ParseScope () "State"),
                     EffectType.Link,
                     defaultDesc,
                     "",
                     true
                 )
                 :> Effect))

        let countryEffects =
            (countries
             |> Array.map (fun p ->
                 ScopedEffect(
                     p,
                     scopeManager.AllScopes,
                     Some(scopeManager.ParseScope () "Country"),
                     EffectType.Link,
                     defaultDesc,
                     "",
                     true
                 )
                 :> Effect))

        Array.concat [| effects; stateEffects; countryEffects |]

    let loadConfigRulesHook (rules: RootRule array) (lookup: Lookup) embedded =
        lookup.allCoreLinks <- lookup.triggers @ lookup.effects @ updateEventTargetLinks embedded
        Array.append rules (Hooks.addModifiersWithScopes lookup)

    let refreshConfigBeforeFirstTypesHook (lookup: HOI4Lookup) _ _ =
        let provinceEnums =
            { key = "provinces"
              description = "provinces"
              values = lookup.HOI4provinces
              valuesWithRange = lookup.HOI4provinces |> Array.map (fun x -> x, None) }

        lookup.enumDefs <-
            lookup.enumDefs
            |> Map.add provinceEnums.key (provinceEnums.description, provinceEnums.valuesWithRange)

    let refreshConfigAfterFirstTypesHook (lookup: Lookup) _ (embeddedSettings: EmbeddedSettings) =
        let states =
            lookup.typeDefInfo.TryFind "state"
            |> Option.map (fun sl ->
                sl
                |> Array.map (fun tdi -> StringResource.stringManager.InternIdentifierToken tdi.id))
            |> Option.defaultValue [||]

        let countries =
            lookup.enumDefs.TryFind "country_tag"
            |> Option.map (fun x -> (snd x) |> Array.map (fst >> StringResource.stringManager.InternIdentifierToken))
            |> Option.defaultValue [||]

        let ts = updateScriptedTriggers lookup.configRules states countries
        let es = updateScriptedEffects lookup.configRules states countries

        let ls =
            updateEventTargetLinks embeddedSettings
            @ addDataEventTargetLinks lookup embeddedSettings false

        lookup.allCoreLinks <- ts.Concat(es).Concat(ls) |> List.ofSeq

    let refreshConfigAfterVarDefHook
        (lookup: Lookup)
        (resources: IResourceAPI<_>)
        (embeddedSettings: EmbeddedSettings)
        =
        lookup.allCoreLinks <-
            lookup.triggers
            @ lookup.effects
            @ updateEventTargetLinks embeddedSettings
            @ addDataEventTargetLinks lookup embeddedSettings false

    let afterInit (game: GameObject) =
        updateModifiers (game)
        updateProvinces (game)
        updateScriptedLoc (game)

    let createEmbeddedSettings
        embeddedFiles
        cachedResourceData
        (configs: (string * string) list)
        (cachedRuleMetadata: CachedRuleMetadata option)
        =

        initializeScopesAndModifierCategories configs defaultScopeInputs defaultModifiersInputs

        let hoi4Mods = getActualModifiers configs

        let hoi4LocCommands =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "localisation.cwt")
            |> Option.map (fun (fn, ft) -> UtilityParser.loadLocCommands fn ft)
            |> Option.defaultValue ([], [], [])

        let triggers, effects = ([], [])

        let eventTargetLinks =
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

        { triggers = triggers
          effects = effects
          modifiers = hoi4Mods
          embeddedFiles = embeddedFiles
          cachedResourceData = cachedResourceData
          localisationCommands = Legacy hoi4LocCommands
          eventTargetLinks = eventTargetLinks
          cachedRuleMetadata = cachedRuleMetadata
          featureSettings = featureSettings }

    let initGame (setupSettings: HOI4Settings) =
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

        let validationSettings =
            { validators =
                CWTools.Validation.ValidationCore.toLocalStructureValidators
                    [ validateIfWithNoEffect, "ifnoeffect"
                      validateRedundantANDWithNOT, "AND"
                      validateOptimisations embeddedSettings.featureSettings.ListMergeOptimisations, "opt" ]
              globalValidators = []
              dynamicValidators = []
              experimentalValidators = []
              heavyExperimentalValidators = []
              experimental = setupSettings.validation.experimental
              fileValidators = []
              globalFileValidators = []
              lookupValidators = []
              globalLookupValidators = commonValidationRules
              lookupFileValidators = []
              scriptedParamsValidators = []
              useRules = true
              debugRulesOnly = false
              localisationValidators = [] }

        let settings =
            { rootDirectories = setupSettings.rootDirectories
              excludeGlobPatterns = setupSettings.excludeGlobPatterns
              embedded = embeddedSettings
              GameSettings.rules = setupSettings.rules
              validation = setupSettings.validation
              scriptFolders = setupSettings.scriptFolders
              modFilter = setupSettings.modFilter
              initialLookup = HOI4Lookup()
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
                initialLookup = HOI4Lookup() }


        let legacyLocDataTypes =
            settings.embedded.localisationCommands
            |> function
                | Legacy(c, v, links) -> (c, v, links)
                | _ -> ([], [], [])

        let processLocalisationFunction lookup =
            (createLocalisationFunctions HOI4.locStaticSettings createLocDynamicSettings legacyLocDataTypes lookup)

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
              defaultLang = HOI4 HOI4Lang.Default
              oneToOneScopesNames = oneToOneScopesNames
              loadConfigRulesHook = loadConfigRulesHook
              refreshConfigBeforeFirstTypesHook = refreshConfigBeforeFirstTypesHook
              refreshConfigAfterFirstTypesHook = refreshConfigAfterFirstTypesHook
              refreshConfigAfterVarDefHook = refreshConfigAfterVarDefHook
              locFunctions = processLocalisationFunction }

        let game =
            GameObject.CreateGame
                (settings,
                 "hearts of iron iv",
                 scriptFolders,
                 Compute.computeHOI4Data,
                 Compute.computeHOI4DataUpdate,
                 (HOI4LocalisationService >> (fun f -> f :> ILocalisationAPICreator)),
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
                 setupSettings.debugSettings)
                afterInit

        let defaultLang =
            settings.validation.langs
            |> Array.tryHead
            |> Option.defaultValue (HOI4 HOI4Lang.Default)

        (game, defaultLang)

open HOI4GameFunctions

type HOI4Game(setupSettings: HOI4Settings) =
    inherit CWToolsGameBase<HOI4ComputedData, HOI4Lookup>(initGame setupSettings)
