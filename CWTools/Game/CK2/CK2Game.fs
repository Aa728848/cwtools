namespace CWTools.Games.CK2

open CWTools.Game
open CWTools.Localisation
open CWTools.Utilities.Utils2
open CWTools.Validation
open CWTools.Games
open CWTools.Common
open CWTools.Localisation.CK2Localisation
open CWTools.Utilities.Utils
open CWTools.Utilities.Position
open CWTools.Utilities
open System.IO
open CWTools.Validation.Common.CommonValidation
open CWTools.Common.CK2Constants
open CWTools.Process.Scopes.CK2
open CWTools.Process.Scopes.Scopes
open System.Text
open CWTools.Games.LanguageFeatures
open CWTools.Process
open CWTools.Process.ProcessCore
open System
open CWTools.Games.Helpers
open CWTools.Rules
open CWTools.Parser
open CWTools.Process.Localisation

type CK2Settings = GameSetupSettings<CK2Lookup>

module CK2GameFunctions =
    type GameObject = GameObject<ComputedData, CK2Lookup>

    let createLocDynamicSettings (lookup: Lookup) =
        let eventtargets =
            (lookup.varDefInfo.TryFind "event_target"
             |> Option.defaultValue [||]
             |> Array.map (fun (s, _) -> s, scopeManager.AnyScope))

        let definedvars =
            (lookup.varDefInfo.TryFind "variable"
             |> Option.defaultValue [||]
             |> Array.map fst)

        { scriptedLocCommands = lookup.scriptedLoc |> Array.map (fun s -> s, [ scopeManager.AnyScope ])
          eventTargets = eventtargets
          setVariables = definedvars |> IgnoreCaseStringSet }

    let updateScriptedLoc (game: GameObject) =
        let rawLocs =
            game.Resources.AllEntities()
            |> Seq.choose (function
                | struct (f, _) when f.filepath.Contains("customizable_localisation") -> Some f.entity
                | _ -> None)
            |> Seq.collect _.Nodes
            |> Seq.map (fun l -> l.TagText "name")
            |> Array.ofSeq

        game.Lookup.embeddedScriptedLoc <-
            game.Settings.embedded.cachedRuleMetadata
            |> Option.map _.scriptedLoc
            |> Option.defaultValue [||]

        game.Lookup.scriptedLoc <- rawLocs

    let updateModifiers (game: GameObject) =
        game.Lookup.coreModifiers <- game.Settings.embedded.modifiers

    let updateLandedTitles (game: GameObject) =
        let fNode =
            fun (t: Node) result ->
                match t.Key with
                | x when x.StartsWith "e_" && t.TagText "landless" == "yes" -> ((TitleType.Empire, true), x) :: result
                | x when x.StartsWith "e_" -> ((TitleType.Empire, false), x) :: result
                | x when x.StartsWith "k_" && t.TagText "landless" == "yes" -> ((TitleType.Kingdom, true), x) :: result
                | x when x.StartsWith "k_" -> ((TitleType.Kingdom, false), x) :: result
                | x when x.StartsWith "d_" ->
                    match t.TagText "landless", t.TagText "mercenary", t.TagText "holy_order" with
                    | "yes", "yes", _
                    | "yes", _, "yes" -> ((TitleType.Duchy_Hired, true), x) :: result
                    | "yes", _, _ -> ((TitleType.Duchy_Normal, true), x) :: result
                    | _, "yes", _
                    | _, _, "yes" -> ((TitleType.Duchy_Hired, false), x) :: result
                    | _ -> ((TitleType.Duchy_Normal, false), x) :: result
                | x when x.StartsWith "c_" && t.TagText "landless" == "yes" -> ((TitleType.County, true), x) :: result
                | x when x.StartsWith "c_" -> ((TitleType.County, false), x) :: result
                | x when x.StartsWith "b_" && t.TagText "landless" == "yes" -> ((TitleType.Barony, true), x) :: result
                | x when x.StartsWith "b_" -> ((TitleType.Barony, false), x) :: result
                | _ -> result

        let titleEntities =
            (EntitySet(game.Resources.AllEntities())).GlobMatchChildren("**/landed_titles/**/*.txt")

        let titles = titleEntities |> List.collect (foldNode7 fNode)

        let inner
            (ells, es, klls, ks, dnlls, dns, dhlls, dhs, clls, cs, blls, bs)
            (k: TitleType * bool, value: string)
            =
            match k with
            | TitleType.Empire, true -> (value :: ells, es, klls, ks, dnlls, dns, dhlls, dhs, clls, cs, blls, bs)
            | TitleType.Empire, false -> (ells, value :: es, klls, ks, dnlls, dns, dhlls, dhs, clls, cs, blls, bs)
            | TitleType.Kingdom, true -> (ells, es, value :: klls, ks, dnlls, dns, dhlls, dhs, clls, cs, blls, bs)
            | TitleType.Kingdom, false -> (ells, es, klls, value :: ks, dnlls, dns, dhlls, dhs, clls, cs, blls, bs)
            | TitleType.Duchy_Normal, true -> (ells, es, klls, ks, value :: dnlls, dns, dhlls, dhs, clls, cs, blls, bs)
            | TitleType.Duchy_Normal, false -> (ells, es, klls, ks, dnlls, value :: dns, dhlls, dhs, clls, cs, blls, bs)
            | TitleType.Duchy_Hired, true ->
                (ells, es, klls, ks, dnlls, dns, value :: value :: dhlls, dhs, clls, cs, blls, bs)
            | TitleType.Duchy_Hired, false -> (ells, es, klls, ks, dnlls, dns, dhlls, dhs, clls, cs, blls, bs)
            | TitleType.County, true -> (ells, es, klls, ks, dnlls, dns, dhlls, dhs, value :: clls, cs, blls, bs)
            | TitleType.County, false -> (ells, es, klls, ks, dnlls, dns, dhlls, dhs, clls, value :: cs, blls, bs)
            | TitleType.Barony, true -> (ells, es, klls, ks, dnlls, dns, dhlls, dhs, clls, cs, value :: blls, bs)
            | TitleType.Barony, false -> (ells, es, klls, ks, dnlls, dns, dhlls, dhs, clls, cs, blls, value :: bs)
            | _ -> (ells, es, klls, ks, dnlls, dns, dhlls, dhs, clls, cs, blls, bs)

        let ells, es, klls, ks, dnlls, dns, dhlls, dhs, clls, cs, blls, bs =
            titles |> List.fold inner ([], [], [], [], [], [], [], [], [], [], [], [])

        game.Lookup.CK2LandedTitles <-
            ((TitleType.Empire, true), ells)
            :: ((TitleType.Empire, false), es)
            :: ((TitleType.Kingdom, true), klls)
            :: ((TitleType.Kingdom, false), ks)
            :: ((TitleType.Duchy_Normal, true), dnlls)
            :: ((TitleType.Duchy_Normal, false), dns)
            :: ((TitleType.Duchy_Hired, true), dhlls)
            :: ((TitleType.Duchy_Hired, false), dhs)
            :: ((TitleType.County, true), clls)
            :: ((TitleType.County, false), cs)
            :: ((TitleType.Barony, true), blls)
            :: [ ((TitleType.Barony, false), bs) ]
            |> Map.ofList

    let createLandedTitleTypes (lookup: CK2Lookup) (map: Map<_, _>) =
        let ells =
            lookup.CK2LandedTitles.[TitleType.Empire, true]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "empire"; "landless" ])
            |> Seq.toArray

        let es =
            lookup.CK2LandedTitles.[TitleType.Empire, false]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "empire"; "landed" ])
            |> Seq.toArray

        let klls =
            lookup.CK2LandedTitles.[TitleType.Kingdom, true]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "kingdom"; "landless" ])
            |> Seq.toArray

        let ks =
            lookup.CK2LandedTitles.[TitleType.Kingdom, false]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "kingdom"; "landed" ])
            |> Seq.toArray

        let dllns =
            lookup.CK2LandedTitles.[TitleType.Duchy_Normal, true]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "duchy"; "duchy_normal"; "landless" ])
            |> Seq.toArray

        let dns =
            lookup.CK2LandedTitles.[TitleType.Duchy_Normal, false]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "duchy"; "duchy_normal"; "landed" ])
            |> Seq.toArray

        let dllhs =
            lookup.CK2LandedTitles.[TitleType.Duchy_Hired, true]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "duchy"; "duchy_hired"; "landless" ])
            |> Seq.toArray

        let dhs =
            lookup.CK2LandedTitles.[TitleType.Duchy_Hired, false]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "duchy"; "duchy_hired"; "landed" ])
            |> Seq.toArray

        let clls =
            lookup.CK2LandedTitles.[TitleType.County, true]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "county"; "landless" ])
            |> Seq.toArray

        let cs =
            lookup.CK2LandedTitles.[TitleType.County, false]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "county"; "landed" ])
            |> Seq.toArray

        let blls =
            lookup.CK2LandedTitles.[TitleType.Barony, true]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "barony"; "landless" ])
            |> Seq.toArray

        let bs =
            lookup.CK2LandedTitles.[TitleType.Barony, false]
            |> Seq.map (fun e -> createTypeDefInfo false e range.Zero [] [ "barony"; "landed" ])
            |> Seq.toArray

        map
        |> Map.add "title.empire" (Array.concat [| es; ells |])
        |> Map.add "title.kingdom" (Array.concat [| ks; klls |])
        |> Map.add "title.duchy" (Array.concat [| dllns; dns; dllhs; dhs |])
        |> Map.add "title.duchy_hired" (Array.concat [| dllhs; dhs |])
        |> Map.add "title.duchy_normal" (Array.concat [| dllns; dns |])
        |> Map.add "title.county" (Array.concat [| clls; cs |])
        |> Map.add "title.barony" (Array.concat [| blls; bs |])
        |> Map.add "title.landless" (Array.concat [| ells; klls; dllns; dllhs; clls; blls |])
        |> Map.add "title.landed" (Array.concat [| es; ks; dns; dhs; cs; bs |])
        |> Map.add "title" (Array.concat [| es; ells; ks; klls; dns; dllns; dhs; dllhs; cs; clls; bs; blls |])

    let updateProvinces (game: GameObject) =
        game.Lookup.CK2provinces <- loadDefinitionCsvProvinces game.Resources

    let updateScriptedEffects (lookup: Lookup) (rules: RootRule array) (embeddedSettings: EmbeddedSettings) =
        let effects =
            rules
            |> Array.choose (function
                | AliasRule("effect", r) -> Some r
                | _ -> None)

        let ruleToEffect (r, o) =
            let name =
                match r with
                | LeafRule(SpecificField(SpecificValue n), _) -> StringResource.stringManager.GetStringForID n.normal
                | NodeRule(SpecificField(SpecificValue n), _) -> StringResource.stringManager.GetStringForID n.normal
                | _ -> ""

            DocEffect(
                name,
                o.requiredScopes,
                o.pushScope,
                EffectType.Effect,
                o.description |> Option.defaultValue "",
                ""
            )

        (effects |> Array.map ruleToEffect |> Array.map (fun e -> e :> Effect))

    let updateScriptedTriggers (lookup: Lookup) (rules: RootRule array) (embeddedSettings: EmbeddedSettings) =
        let effects =
            rules
            |> Array.choose (function
                | AliasRule("trigger", r) -> Some r
                | _ -> None)

        let ruleToTrigger (r, o) =
            let name =
                match r with
                | LeafRule(SpecificField(SpecificValue n), _) -> StringResource.stringManager.GetStringForID n.normal
                | NodeRule(SpecificField(SpecificValue n), _) -> StringResource.stringManager.GetStringForID n.normal
                | _ -> ""

            DocEffect(
                name,
                o.requiredScopes,
                o.pushScope,
                EffectType.Trigger,
                o.description |> Option.defaultValue "",
                ""
            )

        (effects |> Array.map ruleToTrigger |> Array.map (fun e -> e :> Effect))

    let addModifiersAsTypes (lookup: Lookup) (typesMap: Map<string, TypeDefInfo array>) =
        typesMap.Add(
            "modifier",
            lookup.coreModifiers
            |> Array.map (fun m -> createTypeDefInfo false m.tag range.Zero [] [])
        )

    let loadConfigRulesHook rules (lookup: Lookup) embedded =
        let ts = updateScriptedTriggers lookup rules embedded
        let es = updateScriptedEffects lookup rules embedded
        let ls = updateEventTargetLinks embedded |> List.toArray
        lookup.allCoreLinks <- Seq.concat [| ts; es; ls |] |> Seq.toList
        Array.append rules (Hooks.addModifiersWithScopes lookup)

    let refreshConfigBeforeFirstTypesHook (lookup: CK2Lookup) _ _ =
        let modifierEnums =
            { key = "modifiers"
              values = lookup.coreModifiers |> Array.map _.tag
              description = "Modifiers"
              valuesWithRange = lookup.coreModifiers |> Array.map (fun m -> m.tag, None) }

        let provinceEnums =
            { key = "provinces"
              description = "provinces"
              values = lookup.CK2provinces
              valuesWithRange = lookup.CK2provinces |> Array.map (fun x -> x, None) }

        lookup.enumDefs <-
            lookup.enumDefs
            |> Map.add modifierEnums.key (modifierEnums.description, modifierEnums.valuesWithRange)
            |> Map.add provinceEnums.key (provinceEnums.description, provinceEnums.valuesWithRange)

    let refreshConfigAfterFirstTypesHook (lookup: CK2Lookup) _ (embeddedSettings: EmbeddedSettings) =
        lookup.typeDefInfo <- createLandedTitleTypes lookup lookup.typeDefInfo |> addModifiersAsTypes lookup

        lookup.allCoreLinks <-
            lookup.triggers
            @ lookup.effects
            @ updateEventTargetLinks embeddedSettings
            @ addDataEventTargetLinks lookup embeddedSettings false

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
        updateLandedTitles (game)
        updateProvinces (game)

    let createEmbeddedSettings embeddedFiles cachedResourceData (configs: (string * string) list) cachedRuleMetadata =
        initializeScopesAndModifierCategories configs defaultScopeInputs defaultModifiersInputs

        let ck2Mods = getActualModifiers configs

        let ck2LocCommands =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "localisation.cwt")
            |> Option.map (fun (fn, ft) -> UtilityParser.loadLocCommands fn ft)
            |> Option.defaultValue ([], [], [])

        let ck2EventTargetLinks =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "links.cwt")
            |> Option.map (fun (fn, ft) ->
                UtilityParser.loadEventTargetLinks
                    scopeManager.AnyScope
                    (scopeManager.ParseScope())
                    scopeManager.AllScopes
                    fn
                    ft)
            |> Option.defaultValue (CWTools.Process.Scopes.CK2.scopedEffects () |> List.map SimpleLink)

        let featureSettings = getFeatureSettings configs

        let triggers, effects = ([], [])

        { triggers = triggers
          effects = effects
          modifiers = ck2Mods
          embeddedFiles = embeddedFiles
          cachedResourceData = cachedResourceData
          localisationCommands = Legacy ck2LocCommands
          eventTargetLinks = ck2EventTargetLinks
          cachedRuleMetadata = cachedRuleMetadata
          featureSettings = featureSettings }

    let initGame (setupSettings: CK2Settings) =
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
              initialLookup = CK2Lookup()
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
                initialLookup = CK2Lookup() }

        let legacyLocDataTypes =
            settings.embedded.localisationCommands
            |> function
                | Legacy(c, v, links) -> (c, v, links)
                | _ -> ([], [], [])

        let processLocalisationFunction lookup =
            (createLocalisationFunctions CK2.locStaticSettings createLocDynamicSettings legacyLocDataTypes lookup)

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
              defaultLang = CK2 CK2Lang.Default
              oneToOneScopesNames = oneToOneScopesNames
              loadConfigRulesHook = loadConfigRulesHook
              refreshConfigBeforeFirstTypesHook = refreshConfigBeforeFirstTypesHook
              refreshConfigAfterFirstTypesHook = refreshConfigAfterFirstTypesHook
              refreshConfigAfterVarDefHook = refreshConfigAfterVarDefHook
              locFunctions = processLocalisationFunction }

        let game =
            GameObject.CreateGame
                ((settings,
                  "crusader kings ii",
                  scriptFolders,
                  Compute.computeCK2Data,
                  Compute.computeCK2DataUpdate,
                  (CK2LocalisationService >> (fun f -> f :> ILocalisationAPICreator)),
                  processLocalisationFunction,
                  defaultContext,
                  noneContext,
                  Encoding.UTF8,
                  Encoding.GetEncoding(1252),
                  validationSettings,
                  Hooks.globalLocalisation,
                  (fun _ _ -> ()),
                  ".csv",
                  rulesManagerSettings,
                  setupSettings.debugSettings))
                afterInit

        let defaultLang =
            settings.validation.langs
            |> Array.tryHead
            |> Option.defaultValue (CK2 CK2Lang.English)

        (game, defaultLang)

open CK2GameFunctions

type CK2Game(setupSettings: CK2Settings) =
    inherit CWToolsGameBase<CK2ComputedData, CK2Lookup>(initGame setupSettings)
