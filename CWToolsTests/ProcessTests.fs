module ProcessTests

open System.Collections.Frozen
open Expecto
open FParsec
open CWTools.Common
open CWTools.Process
open CWTools.Parser
open CWTools.Rules
// open CWTools.Rules.RulesParser
open CWTools.Games
open System.IO
open CWTools.Common.STLConstants
open CWTools.Utilities.Position
open CWTools.Validation
open CWTools.Utilities.Utils
open CWTools.Utilities.Utils2
open CWTools.Utilities
open CWTools.Games.Files
open CWTools.Games.Stellaris

open CWTools.Process.Scopes.STL
open CWTools.Process.Scopes
open CWTools.Process.Scopes.Scopes
open CWTools.Rules.RulesWrapper
open LogCaptureTest


let emptyStellarisSettings rootDirectory =
    { rootDirectories = [| WD { name = "test"; path = rootDirectory } |]
      modFilter = None
      validation =
        { validateVanilla = false
          experimental = true
          langs = [| STL STLLang.English |] }
      rules = None
      embedded = FromConfig([], [])
      scriptFolders = None
      excludeGlobPatterns = None
      maxFileSize = None
      debugSettings = DebugSettings.Default
      vanillaPath = None }

let emptyEmbeddedSettings =
    { triggers = []
      effects = []
      modifiers = [||]
      embeddedFiles = []
      cachedResourceData = []
      localisationCommands = Legacy([], [], [])
      eventTargetLinks = []
      cachedRuleMetadata = None
      featureSettings = UtilityParser.FeatureSettings.Default }

let emptyDataTypesLazy =
    lazy
        { DataTypeParser.JominiLocDataTypes.promotes = Map.empty
          DataTypeParser.JominiLocDataTypes.confidentFunctions = Map.empty
          DataTypeParser.JominiLocDataTypes.functions = Map.empty
          DataTypeParser.JominiLocDataTypes.dataTypes = Map.empty
          DataTypeParser.JominiLocDataTypes.dataTypeNames = Set.empty }

let specificField = RulesParser.specificField
let optionalMany = RulesParser.optionalMany
let optionalSingle = RulesParser.optionalSingle
let requiredSingle = RulesParser.requiredSingle
let defaultFloat = RulesParser.defaultFloat
let defaultInt = RulesParser.defaultInt
let parseConfig = RulesParser.parseConfig

let dynamicSettings _ =
    { CWTools.Process.Localisation.LegacyLocDynamicsSettings.scriptedLocCommands = []
      CWTools.Process.Localisation.LegacyLocDynamicsSettings.eventTargets = []
      CWTools.Process.Localisation.LegacyLocDynamicsSettings.setVariables = IgnoreCaseStringSet() }

let processLocalisationLazy =
    lazy
        ((Helpers.createLocalisationFunctions
            CWTools.Process.Localisation.STL.locStaticSettings
            dynamicSettings
            ([], [], ([], []))
            (STLLookup()))
         |> fst)

let validateLocalisationLazy =
    lazy
        ((Helpers.createLocalisationFunctions
            CWTools.Process.Localisation.STL.locStaticSettings
            dynamicSettings
            ([], [], ([], []))
            (STLLookup()))
         |> snd)

[<Tests>]
let legacyLocalisationCommandTests =
    let validate command =
        let staticSettings: CWTools.Process.Localisation.LegacyLocStaticSettings =
            { questionMarkVariable = true
              usesVariableCommands = false
              parameterVariables = true
              locPrimaryScopes = [ "From", id ]
              scopedLocEffectsMap = EffectMap()
              commands = []
              variableCommands = [] }

        CWTools.Process.Localisation.ChangeLocScope.createLegacyLocalisationCommandValidator
            staticSettings
            (dynamicSettings ())
            defaultContext
            command

    testList
        "legacy localisation commands"
        [ testCase "empty command segments do not throw"
          <| fun () ->
              [ "From..From.GetName"; ".From"; "From."; "?" ]
              |> List.iter (fun command ->
                  match validate command with
                  | CWTools.Process.Localisation.LocNotFound "" -> ()
                  | result -> failtestf "Expected an empty segment in %A to be invalid, got %A" command result)

          testCase "lowercase variable fallback is preserved"
          <| fun () ->
              match validate "myVariable" with
              | CWTools.Process.Localisation.Found "variable_fallback" -> ()
              | result -> failtestf "Expected lowercase variable fallback, got %A" result ]

let createStarbaseLazy =
    lazy
        (let owner =
            NewRule(LeafRule(specificField "owner", ScopeField [ scopeManager.AnyScope ]), requiredSingle)

         let size =
             NewRule(LeafRule(specificField "size", ValueField(ValueType.Enum "size")), requiredSingle)

         let moduleR =
             NewRule(LeafRule(specificField "module", ValueField(ValueType.Enum "module")), optionalMany)

         let building =
             NewRule(LeafRule(specificField "building", ValueField(ValueType.Enum "building")), optionalMany)

         let effect =
             NewRule(
                 NodeRule(
                     specificField "effect",
                     [| (LeafRule(AliasField "effect", AliasField "effect")), optionalMany |]
                 ),
                 { optionalSingle with
                     replaceScopes =
                         Some
                             { froms = None
                               root = Some(scopeManager.ParseScope () "country")
                               this = Some(scopeManager.ParseScope () "country")
                               prevs = None } }
             )

         let rule =
             NewRule(
                 NodeRule(specificField "create_starbase", [| owner; size; moduleR; building; effect |]),
                 optionalMany
             )

         rule)

let createStarbaseAliasLazy = lazy AliasRule("effect", createStarbaseLazy.Value)

let createStarbaseEnumsLazy =
    lazy
        ([ ("size", ("size", [ "medium"; "large" ]))
           ("module", ("module", [ "trafficControl" ]))
           ("building", ("building", [ "crew" ])) ]
         |> Map.ofList)

let createStarbaseTypeDefLazy =
    lazy
        { name = "create_starbase"
          nameField = None
          pathOptions =
            { paths = [| "events" |]
              pathStrict = false
              pathFile = None
              pathExtension = None }
          conditions = None
          subtypes = []
          typeKeyFilter = None
          rootCompletionFromSubtypes = false
          skipRootKey = []
          warningOnly = false
          type_per_file = false
          localisation = []
          modifiers = []
          startsWith = None
          unique = false
          graphRelatedTypes = []
          keyPrefix = None
          shouldBeReferenced = RefNotRequired
          unknownKeyHandling = UnknownKeyIgnore
          obsoleteKeys = Map.empty }

let buildingLazy =
    lazy
        (let inner =
            [| NewRule(LeafRule(specificField "allow", ScalarField ScalarValue), requiredSingle)
               NewRule(LeafRule(specificField "empire_unique", ValueField ValueType.Bool), optionalSingle) |]

         NewRule(NodeRule(specificField "building", inner), optionalMany))

let shipsizeLazy =
    lazy
        (let inner =
            [| NewRule(LeafRule(specificField "formation_priority", defaultInt), optionalSingle)
               NewRule(LeafRule(specificField "max_speed", defaultFloat), requiredSingle)
               NewRule(LeafRule(specificField "acceleration", defaultFloat), requiredSingle)
               NewRule(LeafRule(specificField "rotation_speed", defaultFloat), requiredSingle)
               NewRule(LeafRule(specificField "collision_radius", defaultFloat), optionalSingle)
               NewRule(LeafRule(specificField "max_hitpoints", defaultInt), requiredSingle)
               NewRule(NodeRule(specificField "modifier", [||]), optionalSingle)
               NewRule(LeafRule(specificField "size_multiplier", defaultInt), requiredSingle)
               NewRule(LeafRule(specificField "fleet_slot_size", defaultInt), requiredSingle)
               NewRule(NodeRule(specificField "section_slots", [||]), optionalSingle)
               NewRule(LeafRule(specificField "num_target_locators", defaultInt), requiredSingle)
               NewRule(LeafRule(specificField "is_space_station", ValueField ValueType.Bool), requiredSingle)
               NewRule(LeafRule(specificField "icon_frame", defaultInt), requiredSingle)
               NewRule(LeafRule(specificField "base_buildtime", defaultInt), requiredSingle)
               NewRule(LeafRule(specificField "can_have_federation_design", ValueField ValueType.Bool), requiredSingle)
               NewRule(LeafRule(specificField "enable_default_design", ValueField ValueType.Bool), requiredSingle)
               NewRule(
                   LeafRule(specificField "default_behavior", TypeField(TypeType.Simple "ship_behavior")),
                   requiredSingle
               )
               NewRule(NodeRule(specificField "prerequisites", [||]), optionalSingle)
               NewRule(LeafRule(specificField "combat_disengage_chance", defaultFloat), optionalSingle)
               NewRule(LeafRule(specificField "has_mineral_upkeep", ValueField ValueType.Bool), requiredSingle)
               NewRule(LeafRule(specificField "class", ScalarField ScalarValue), requiredSingle)
               NewRule(LeafRule(specificField "construction_type", ScalarField ScalarValue), requiredSingle)
               NewRule(LeafRule(specificField "required_component_set", ScalarField ScalarValue), requiredSingle) |]

         NewRule(NodeRule(specificField "ship_size", inner), optionalMany))

let shipBehaviorTypeLazy =
    lazy
        { name = "ship_behavior"
          nameField = Some "name"
          pathOptions =
            { paths = [| "common/ship_behaviors" |]
              pathStrict = false
              pathFile = None
              pathExtension = None }
          conditions = None
          subtypes = []
          typeKeyFilter = None
          rootCompletionFromSubtypes = false
          skipRootKey = []
          warningOnly = false
          type_per_file = false
          localisation = []
          modifiers = []
          startsWith = None
          unique = false
          shouldBeReferenced = RefNotRequired
          unknownKeyHandling = UnknownKeyIgnore
          obsoleteKeys = Map.empty
          graphRelatedTypes = []
          keyPrefix = None }

let shipSizeTypeLazy =
    lazy
        { name = "ship_size"
          pathOptions =
            { paths = [| "common/ship_sizes" |]
              pathStrict = false
              pathFile = None
              pathExtension = None }
          nameField = None
          conditions = None
          subtypes = []
          typeKeyFilter = None
          rootCompletionFromSubtypes = false
          skipRootKey = []
          warningOnly = false
          type_per_file = false
          localisation = []
          modifiers = []
          startsWith = None
          unique = false
          shouldBeReferenced = RefNotRequired
          unknownKeyHandling = UnknownKeyIgnore
          obsoleteKeys = Map.empty
          graphRelatedTypes = []
          keyPrefix = None }
//  type[ship_behavior] = {
//      path = "game/common/ship_behaviors"
//      name_field = "name"
//  }
//  type[leader_trait] = {
//      path = "game/common/traits"
//      conditions = {
//          leader_trait = yes
//      }
//  }
//  type[species_trait] = {
//      path = "game/common/traits"
//  }


let effectMap = EffectMap()

[<Tests>]
let testc =
    testList
        "config parse"
        [ testWithCapturedLogs "simple parse"
          <| fun () ->
              let config =
                  "create_starbase = {\n\
                          ## cardinality = 1..1\n\
                          owner = scalar\n\
                          ## cardinality = 1..1\n\
                          size = scalar\n\
                          ## cardinality = 0..100\n\
                          module = scalar\n\
                          ## cardinality = 0..100\n\
                          building = scalar\n\
                          ## cardinality = 0..1\n\
                          effect = effect\n\
                          }"

              let rules, _, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let Typerules =
                  rules
                  |> List.choose (function
                      | TypeRule(_, rs) -> Some(rs)
                      | _ -> None)

              let input =
                  "create_starbase = {\n\
                            owner = this \n\
                            owner = this \n\
                            size = large \n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let apply =
                      RuleValidationService(
                          RulesWrapper(rules |> List.toArray),
                          [],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let errors = apply.ApplyNodeRule(Typerules |> Array.ofList, node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) ->
                      Expect.equal es.Length 1 $"Following lines are not expected to have an error %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test error_unknown_keys reports unknown type keys"
          <| fun () ->
              let config =
                  "types = {\n\
                          type[game_rule] = {\n\
                          path = \"game/common/game_rules\"\n\
                          error_unknown_keys = yes\n\
                          ## type_key_filter = can_declare_war\n\
                          subtype[can_declare_war] = {\n\
                          }\n\
                          ## type_key_filter = can_add_claim\n\
                          subtype[can_add_claim] = {\n\
                          }\n\
                          }\n\
                          }\n\
                          game_rule = {\n\
                          }"

              let rules, types, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let input =
                  "can_declare_war = {\n\
                            }\n\
                            can_declar_war = {\n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let apply =
                      RuleValidationService(
                          RulesWrapper(rules |> List.toArray),
                          types,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let errors =
                      apply.ManualRuleValidate("common/game_rules/test.txt", node)

                  match errors with
                  | OK -> Expect.isTrue false "Expected an unknown key error for can_declar_war"
                  | Invalid(_, es) ->
                      Expect.equal es.Length 1 $"Expected exactly one unknown key error %A{es}"

                      Expect.stringContains
                          (es |> List.head).message
                          "is not a known game_rule key"
                          "Error message should explain the unknown key"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test error_unknown_keys suggest mode only flags near misses"
          <| fun () ->
              let config =
                  "types = {\n\
                          type[on_action] = {\n\
                          path = \"game/common/on_actions\"\n\
                          error_unknown_keys = suggest\n\
                          ## type_key_filter = on_game_start\n\
                          subtype[on_game_start] = {\n\
                          }\n\
                          ## type_key_filter = on_monthly_pulse\n\
                          subtype[on_monthly_pulse] = {\n\
                          }\n\
                          }\n\
                          }\n\
                          on_action = {\n\
                          }"

              let rules, types, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let input =
                  "on_game_start = {\n\
                            }\n\
                            on_gamestart = {\n\
                            }\n\
                            on_my_totally_custom_action = {\n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let apply =
                      RuleValidationService(
                          RulesWrapper(rules |> List.toArray),
                          types,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let errors =
                      apply.ManualRuleValidate("common/on_actions/test.txt", node)

                  match errors with
                  | OK -> Expect.isTrue false "Expected a suggestion for on_gamestart"
                  | Invalid(_, es) ->
                      Expect.equal
                          es.Length
                          1
                          $"Custom on_action keys must not be flagged; only the near miss should be %A{es}"

                      let error = es |> List.head
                      Expect.stringContains error.message "did you mean 'on_game_start'" "Should suggest the close key"
                      Expect.equal error.severity Severity.Information "Suggestion should be information severity"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test obsolete_keys reports removed and renamed keys"
          <| fun () ->
              let config =
                  "types = {\n\
                          type[on_action] = {\n\
                          path = \"game/common/on_actions\"\n\
                          error_unknown_keys = suggest\n\
                          should_be_used = unless_subtyped\n\
                          obsolete_keys = {\n\
                          on_planet_conquer = \"removed from the game\"\n\
                          on_planet_zero_pops = \"renamed to on_colony_zero_pops\"\n\
                          }\n\
                          ## type_key_filter = on_game_start\n\
                          subtype[on_game_start] = {\n\
                          }\n\
                          }\n\
                          }\n\
                          on_action = {\n\
                          }"

              let rules, types, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let input =
                  "on_planet_conquer = {\n\
                            }\n\
                            on_my_totally_custom_action = {\n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let apply =
                      RuleValidationService(
                          RulesWrapper(rules |> List.toArray),
                          types,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let errors =
                      apply.ManualRuleValidate("common/on_actions/test.txt", node)

                  match errors with
                  | OK -> Expect.isTrue false "Expected an obsolete key warning for on_planet_conquer"
                  | Invalid(_, es) ->
                      Expect.equal es.Length 1 $"Only the obsolete key should be flagged %A{es}"

                      let error = es |> List.head
                      Expect.stringContains error.message "obsolete on_action key" "Should explain the key is obsolete"
                      Expect.stringContains error.message "removed from the game" "Should carry the configured message"
                      Expect.equal error.severity Severity.Warning "Obsolete key in open key set should be a warning"
              | Failure(e, _, _) -> Expect.isTrue false e

              let lookup = STLLookup()
              lookup.typeDefs <- types
              lookup.typeDefInfo <-
                  Map.ofList
                      [ "on_action",
                        [| { id = "on_planet_conquer"
                             validate = true
                             range = range.Zero
                             explicitLocalisation = []
                             subtypes = [] } |] ]

              let emptySet = EntitySet<STLComputedData>(Seq.empty)

              let unusedErrors =
                  CWTools.Validation.Common.CommonValidation.validateUnusuedTypes lookup emptySet emptySet

              Expect.equal unusedErrors OK "Obsolete on_action keys should not also be reported as unused"

          ]

let leftScopeLazy =
    lazy
        RootRule.AliasRule(
            "effect",
            (NodeRule(
                (ScopeField [ (scopeManager.ParseScope () "Any") ]),
                [| LeafRule((AliasField "effect"), (AliasField "Effect")), optionalMany |]
             ),
             optionalMany)
        )

let eopEffectLazy =
    lazy
        RootRule.AliasRule(
            "effect",
            (NodeRule(
                SpecificField(SpecificValue(StringResource.stringManager.InternIdentifierToken "every_owned_planet")),
                [| LeafRule((AliasField "effect"), (AliasField "Effect")), optionalMany |]
             ),
             { optionalMany with
                 pushScope = Some(scopeManager.ParseScope () "Planet") })
        )

let logEffectLazy =
    lazy
        RootRule.AliasRule(
            "effect",
            (LeafRule(
                NewField.SpecificField(SpecificValue(StringResource.stringManager.InternIdentifierToken "log")),
                ValueField(ValueType.Bool)
             ),
             { optionalMany with
                 pushScope = Some(scopeManager.ParseScope () "Planet") })
        )

[<Tests>]
let testsv =
    testList
        "config validate"
        [ testCase "stellaris default scopes include colony fallback"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))

              Expect.equal
                  ((scopeManager.ParseScope () "colony").ToString())
                  "Colony"
                  "colony should not fall back to Any when scopes.cwt is unavailable"

          testCase "scope context uses nested replace_scope from type rules"
          <| fun () ->
              let scopesConfig =
                  "scopes = {\n\
                       Planet = { aliases = { planet } }\n\
                       Colony = { aliases = { colony } }\n\
                   }\n"

              let config =
                  "types = {\n\
                       type[colony_automation] = {\n\
                           path = \"game/common/colony_automation\"\n\
                       }\n\
                   }\n\
                   ## push_scope = planet\n\
                   colony_automation = {\n\
                       ## replace_scope = { this = colony root = colony }\n\
                       available = {\n\
                           alias_name[trigger] = alias_match_left[trigger]\n\
                       }\n\
                   }\n"

              UtilityParser.initializeScopes (Some("scopes.cwt", scopesConfig)) None

              let rules, types, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "colony.cwt"
                      config

              let input =
                  "auto_colony = {\n\
                       available = {\n\
                           has_designation = col_adf_ring_city\n\
                       }\n\
                   }\n"

              match CKParser.parseString input "common/colony_automation/test.txt" with
              | Success(r, _, _) ->
                  let node =
                      STLProcess.shipProcess.ProcessNode () "root" range.Zero r

                  let entity =
                      { filepath = "common/colony_automation/test.txt"
                        logicalpath = "common/colony_automation/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Other
                        overwrite = Overwrite.No }

                  let rulesWrapper = RulesWrapper(rules |> List.toArray)

                  let validationService =
                      RuleValidationService(
                          rulesWrapper,
                          types,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let infoService =
                      InfoService(
                          rulesWrapper,
                          types,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          validationService,
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  match infoService.GetInfo(mkPos 3 13, entity) with
                  | Some(context, _) ->
                      Expect.equal context.Root (scopeManager.ParseScope () "Colony") "ROOT should use replace_scope"
                      Expect.sequenceEqual context.Scopes [ scopeManager.ParseScope () "Colony" ] "THIS should use replace_scope"
                  | None -> failtest "info failed"
              | Failure(e, _, _) -> failtest e

          testWithCapturedLogs "create_starbase"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = root \n\
                            size = large \n\
                            module = trafficControl \n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let enums =
                      [ ("size", ("size", [ "medium"; "large" ]))
                        ("module", ("module", [ "trafficControl" ])) ]
                      |> Map.ofList
                      |> Map.toSeq
                      |> Seq.map (fun (k, (d, s)) -> k, (d, createStringSet s))
                      |> Map.ofSeq

                  let rules =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [],
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let errors = rules.ApplyNodeRule([| createStarbaseLazy.Value |], node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) -> Expect.isEmpty es $"should be empty: %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "create_starbase fail"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = root \n\
                            size = fake \n\
                            module = faker \n\
                            unknown = test
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let enums =
                      createStarbaseEnumsLazy.Value
                      |> Map.toSeq
                      |> Seq.map (fun (k, (d, s)) -> k, (d, createStringSet s))
                      |> Map.ofSeq

                  let rules =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [],
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let errors = rules.ApplyNodeRule([| createStarbaseLazy.Value |], node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) ->
                      Expect.equal es.Length 3 $"Following lines are not expected to have an error %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "create_starbase min count"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let enums =
                      [ ("size", [ "medium"; "large" ]) ]
                      |> Map.ofList
                      |> Map.toSeq
                      |> Seq.map (fun (k, s) -> k, createStringSet s)
                      |> Map.ofSeq

                  let rules =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let errors = rules.ApplyNodeRule([| createStarbaseLazy.Value |], node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) ->
                      Expect.equal 2 es.Length $"Following lines are not expected to have an error %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "create_starbase max count"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = this \n\
                            owner = this \n\
                            size = large \n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let enums =
                      [ ("size", ("size", [ "medium"; "large" ])) ]
                      |> Map.ofList
                      |> Map.toSeq
                      |> Seq.map (fun (k, (d, s)) -> k, (d, createStringSet s))
                      |> Map.ofSeq

                  let rules =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [],
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let errors = rules.ApplyNodeRule([| createStarbaseLazy.Value |], node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) ->
                      Expect.equal es.Length 1 $"Following lines are not expected to have an error %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "type suffix pattern validation"
          <| fun () ->
              let config =
                  "planet_class = {\n\
                          ## cardinality = 0..1\n\
                          entity = \"\"\n\
                          ## cardinality = 0..1\n\
                          ## type_suffix_pattern = _$_entity\n\
                          entity = <model_entity>\n\
                          }"

              let rules, _, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let typeRules =
                  rules
                  |> List.choose (function
                      | TypeRule(_, rs) -> Some rs
                      | _ -> None)
                  |> Array.ofList

              let typesMap =
                  [ "model_entity", createStringSet [ "desert_planet_01_entity"; "continental_planet_02_entity" ] ]
                  |> Map.ofList
                  |> fun m -> m.ToFrozenDictionary()

              let apply =
                  RuleValidationService(
                      RulesWrapper(rules |> List.toArray),
                      [],
                      typesMap,
                      FrozenDictionary.Empty,
                      FrozenDictionary.Empty,
                      [||],
                      FrozenSet.Empty,
                      effectMap,
                      effectMap,
                      (scopeManager.ParseScope () "Any"),
                      changeScope,
                      defaultContext,
                      STL STLLang.Default,
                      processLocalisationLazy.Value,
                      validateLocalisationLazy.Value
                  )

              let validate input =
                  match CKParser.parseString input "test" with
                  | Success(r, _, _) ->
                      let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                      apply.ApplyNodeRule(typeRules, node)
                  | Failure(e, _, _) -> failtest e

              Expect.equal
                  (validate
                      "planet_class = {\n\
                          entity = desert_planet\n\
                      }")
                  OK
                  "desert_planet should resolve through desert_planet_01_entity"

              Expect.equal
                  (validate
                      "planet_class = {\n\
                          entity = desert_planet_01_entity\n\
                      }")
                  OK
                  "exact model_entity values should remain legal"

              Expect.equal
                  (validate
                      "planet_class = {\n\
                          entity = \"\"\n\
                      }")
                  OK
                  "empty entity should remain legal"

              match
                  validate
                      "planet_class = {\n\
                          entity = desert\n\
                      }"
              with
              | OK -> failtest "desert should not match desert_planet_01_entity by prefix only"
              | Invalid _ -> ()
          testWithCapturedLogs "type prefix from dynamic scope values"
          <| fun () ->
              let config =
                  "planet_entity = {\n\
                          ## cardinality = 0..1\n\
                          ## type_prefix_from = graphical_culture\n\
                          entity = <model_entity>\n\
                          ## cardinality = 0..1\n\
                          graphical_culture = scalar\n\
                          }"

              let rules, _, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let typeRules =
                  rules
                  |> List.choose (function
                      | TypeRule(_, rs) -> Some rs
                      | _ -> None)
                  |> Array.ofList

              let typesMap =
                  [ "graphical_culture", createStringSet [ "mammalian_01"; "reptilian_01" ]
                    "model_entity", createStringSet [ "mammalian_01_habitat_phase_03_entity" ] ]
                  |> Map.ofList
                  |> fun m -> m.ToFrozenDictionary()

              let apply =
                  RuleValidationService(
                      RulesWrapper(rules |> List.toArray),
                      [],
                      typesMap,
                      FrozenDictionary.Empty,
                      FrozenDictionary.Empty,
                      [||],
                      FrozenSet.Empty,
                      effectMap,
                      effectMap,
                      (scopeManager.ParseScope () "Any"),
                      changeScope,
                      defaultContext,
                      STL STLLang.Default,
                      processLocalisationLazy.Value,
                      validateLocalisationLazy.Value
                  )

              let validate input =
                  match CKParser.parseString input "test" with
                  | Success(r, _, _) ->
                      let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                      apply.ApplyNodeRule(typeRules, node)
                  | Failure(e, _, _) -> failtest e

              Expect.equal
                  (validate
                      "planet_entity = {\n\
                          entity = habitat_phase_03_entity\n\
                          graphical_culture = root\n\
                      }")
                  OK
                  "scope graphical culture should try known graphical culture prefixes"

              Expect.equal
                  (validate
                      "planet_entity = {\n\
                          entity = habitat_phase_03_entity\n\
                          graphical_culture = mammalian_01\n\
                      }")
                  OK
                  "explicit matching graphical culture should resolve the prefixed entity"

              match
                  validate
                      "planet_entity = {\n\
                          entity = habitat_phase_03_entity\n\
                          graphical_culture = reptilian_01\n\
                      }"
              with
              | OK -> failtest "explicit known graphical culture should not try unrelated prefixes"
              | Invalid _ -> ()

              match
                  validate
                      "planet_entity = {\n\
                          entity = habitat_phase_03_entity\n\
                          graphical_culture = no\n\
                      }"
              with
              | OK -> failtest "explicit no should disable type prefix fallback"
              | Invalid _ -> ()
          testWithCapturedLogs "create_starbase effect in effect"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = this \n\
                            size = large \n\
                            effect = {\n\
                            create_starbase = {\
                            owner = this \n size = large\n\
                            }\
                            }\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let enums =
                      [ ("size", ("size", [ "medium"; "large" ])) ]
                      |> Map.ofList
                      |> Map.toSeq
                      |> Seq.map (fun (k, (d, s)) -> k, (d, createStringSet s))
                      |> Map.ofSeq

                  let rules =
                      RuleValidationService(
                          RulesWrapper
                              [| TypeRule("create_starbase", createStarbaseLazy.Value)
                                 createStarbaseAliasLazy.Value |],
                          [],
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let errors = rules.ApplyNodeRule([| createStarbaseLazy.Value |], node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) ->
                      Expect.equal es.Length 0 $"Following lines are not expected to have an error %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "test rhs completion"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = this \n\
                            size = large \n\
                            }"
              // let resource = makeEntityResourceInput filepath filetext
              // match resourceManager.ManualProcessResource resource, infoService with
              // |Some e, Some info ->

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let enums =
                      [ ("size", ("size", [ "medium"; "large" ])) ]
                      |> Map.ofList
                      |> Map.toSeq
                      |> Seq.map (fun (k, (d, s)) -> k, (d, createStringSet s))
                      |> Map.ofSeq

                  let comp =
                      CompletionService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          [],
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          [],
                          STL STLLang.Default,
                          emptyDataTypesLazy.Value,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let pos = mkPos 3 8

                  let suggestions =
                      comp.Complete(pos, entity, None, None)
                      |> Seq.map (function
                          | CompletionResponse.Simple(c, _, _) -> c
                          | Snippet(l, _, _, _, _) -> l
                          | Detailed _ -> failwith "todo")
                      |> Seq.sort

                  let expected = [ "medium"; "large" ] |> Seq.sort
                  Expect.sequenceEqual suggestions expected "Completion should match"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "test lhs completion"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = this \n\
                            size \n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let comp =
                      CompletionService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          [],
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          [],
                          STL STLLang.Default,
                          emptyDataTypesLazy.Value,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let pos = mkPos 3 3

                  let suggestions =
                      comp.Complete(pos, entity, None, None)
                      |> Seq.map (function
                          | Simple(c, _, _) -> c
                          | Snippet(l, _, _, _, _) -> l
                          | Detailed _ -> failwith "todo")
                      |> Seq.sort

                  let expected = [ "size"; "owner"; "building"; "effect"; "module" ] |> Seq.sort
                  Expect.sequenceEqual suggestions expected "Completion should match"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test root completion"
          <| fun () ->
              let input =
                  "\n\
                            #test\n\
                            \n\
                            create_starbase = {\n\
                            owner = this \n\
                            }\n"

              let pos = mkPos 1 0
              let split = input.Split('\n')

              let filetext =
                  split
                  |> Array.mapi (fun i s ->
                      if i = (pos.Line - 1) then
                          log $"%s{s}"
                          let s = s.Insert(pos.Column, magicCharString) in
                          log $"%s{s}"
                          s
                      else
                          s)
                  |> String.concat "\n"

              match CKParser.parseString filetext "test.txt" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let comp =
                      CompletionService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          [],
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          [],
                          STL STLLang.Default,
                          emptyDataTypesLazy.Value,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let suggestions =
                      comp.Complete(pos, entity, None, None)
                      |> Seq.map (function
                          | Simple(c, _, _) -> c
                          | Snippet(l, _, _, _, _) -> l
                          | Detailed _ -> failwith "todo")
                      |> Seq.sort

                  let expected = [ "create_starbase"; "create_starbase" ] |> Seq.sort
                  Expect.sequenceEqual suggestions expected "Completion should match"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test scalar completion type hint"
          <| fun () ->
              let input =
                  "fire_on_action = {\n\
                            on_action = o\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let onAction =
                      NewRule(
                          LeafRule(specificField "on_action", ScalarField ScalarValue),
                          { requiredSingle with
                              completionType = Some "on_action" }
                      )

                  let fireOnAction =
                      NewRule(NodeRule(specificField "fire_on_action", [| onAction |]), optionalMany)

                  let typeinfo =
                      [ "on_action", createStringSet [ "on_game_start"; "custom_on_action" ] ]
                      |> Map.ofList

                  let comp =
                      CompletionService(
                          RulesWrapper [| TypeRule("fire_on_action", fireOnAction) |],
                          [ { createStarbaseTypeDefLazy.Value with name = "fire_on_action" } ],
                          typeinfo.ToFrozenDictionary(),
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          [],
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          [],
                          STL STLLang.Default,
                          emptyDataTypesLazy.Value,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let pos = mkPos 2 13

                  let suggestions =
                      comp.Complete(pos, entity, None, None)
                      |> Seq.map (function
                          | Simple(c, _, _) -> c
                          | Snippet(l, _, _, _, _) -> l
                          | Detailed _ -> failwith "todo")
                      |> Seq.sort

                  let expected = [ "custom_on_action"; "on_game_start" ] |> Seq.sort
                  Expect.sequenceEqual suggestions expected "Completion should match"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test on_action root subtype completion"
          <| fun () ->
              let configtext =
                  [ "./testfiles/configtests/config/on_actions.cwt",
                    "types = {\n\
                          ## root_completion = subtypes\n\
                          type[on_action] = {\n\
                              path = \"game/common/on_actions\"\n\
                              ## type_key_filter = on_game_start\n\
                              subtype[on_game_start] = { }\n\
                              ## type_key_filter = on_monthly_pulse\n\
                              subtype[on_monthly_pulse] = { }\n\
                          }\n\
                      }" ]

              let folder = "./testfiles/configtests/completiontests"
              let settings = emptyStellarisSettings folder

              let settings =
                  { settings with
                      embedded = FromConfig([], [])
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let input = "on"
              let pos = mkPos 1 2

              let suggestions =
                  stl.Complete pos "common/on_actions/test.txt" input
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.toList

              Expect.contains suggestions "on_game_start" "Completion should include vanilla on_action key"
              Expect.contains suggestions "on_monthly_pulse" "Completion should include vanilla on_action key"
              Expect.isFalse (suggestions |> List.contains "on_action") "Subtype-only root completion should not suggest the type name"

          testWithCapturedLogs "test test ship_behavior"
          <| fun () ->
              let input =
                  "ship_size = {\n\
                            default_behavior = s \n\
                            }"

              let behaviours =
                  "ship_behavior = {\n\
                              name = \"default\"\n\
                              }\n\
                              ship_behavior = {\n\
                              name = \"swarm\"\n\
                              }"

              match
                  CKParser.parseString input "common/ship_sizes/test.txt",
                  CKParser.parseString behaviours "common/ship_behaviors/test.txt"
              with
              | Success(r, _, _), Success(b, _, _) ->
                  let bnode =
                      (STLProcess.shipProcess.ProcessNode () "root" (mkZeroFile "common/ship_behaviors/test.txt") b)

                  let be =
                      { entity = bnode
                        rawEntity = bnode
                        filepath = "/test/stellaris/common/ship_behaviors/test.txt"
                        logicalpath = "common/ship_behaviors/test.txt"
                        validate = false
                        entityType = EntityType.ShipBehaviors
                        overwrite = Overwrite.No }

                  let ruleapplicator =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let typeinfo =
                      RulesHelpers.getTypesFromDefinitions
                          (Some ruleapplicator)
                          [ shipBehaviorTypeLazy.Value; shipSizeTypeLazy.Value ]
                          [| be |]
                      |> Map.toSeq
                      |> Seq.map (fun (k, s) -> k, createStringSet (s |> Array.map _.id))
                      |> Map.ofSeq
                  // eprintfn "%A" typeinfo
                  let node =
                      (STLProcess.shipProcess.ProcessNode () "root" (mkZeroFile "common/ship_sizes/test.txt") r)

                  let entity =
                      { filepath = "common/ship_sizes/test.txt"
                        logicalpath = "common/ship_sizes/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let pos = mkPos 2 20

                  let comp =
                      CompletionService(
                          RulesWrapper [| TypeRule("ship_size", shipsizeLazy.Value) |],
                          [ shipBehaviorTypeLazy.Value; shipSizeTypeLazy.Value ],
                          typeinfo.ToFrozenDictionary(),
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          [],
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          [],
                          STL STLLang.Default,
                          emptyDataTypesLazy.Value,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let res = comp.Complete(pos, entity, None, None)
                  // eprintfn "res4 %A" res
                  let suggestions =
                      res
                      |> Seq.map (function
                          | Simple(c, _, _) -> c
                          | Snippet(l, _, _, _, _) -> l
                          | Detailed _ -> failwith "todo")
                      |> Seq.sort

                  let expected = [ "default"; "swarm" ] |> Seq.sort
                  Expect.sequenceEqual suggestions expected "Completion should match"

              | ParserResult.Success _, ParserResult.Failure _ -> failwith "todo"
              | ParserResult.Failure _, ParserResult.Success _ -> failwith "todo"
              | ParserResult.Failure _, ParserResult.Failure _ -> failwith "todo"

          ptestCase "test scope at pos simple nodes"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                         effect = {\n\
                         every_owned_planet = { \n\
                         }\n\
                         }\n\
                         }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let rules =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value); eopEffectLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let infoService =
                      InfoService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value); eopEffectLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          rules,
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )
                  // let comp = CompletionService([TypeRule ("create_starbase", RulesParser.createStarbaseLazy.Value)], [RulesParser.createStarbaseTypeDefLazy.Value], Map.empty, Map.empty, [], Set.empty, [], [])
                  let pos = mkPos 3 23
                  let suggestions = infoService.GetInfo(pos, entity)

                  match suggestions with
                  | None -> Expect.isTrue false "info failed"
                  | Some(context, _) ->
                      let scopes = context.Scopes

                      let expected =
                          [ (scopeManager.ParseScope () "Planet")
                            (scopeManager.ParseScope () "Country") ]

                      Expect.sequenceEqual scopes expected "Scopes should match"
              | Failure(e, _, _) -> Expect.isTrue false e
          ptestCase "test scope at pos prev"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                         effect = {\n\
                         every_owned_planet = {\n\
                         prev = { \n\
                         }\n\
                         }\n\
                         }\n\
                         }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let rules =
                      RuleValidationService(
                          RulesWrapper
                              [| TypeRule("create_starbase", createStarbaseLazy.Value)
                                 eopEffectLazy.Value
                                 leftScopeLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let infoService =
                      InfoService(
                          RulesWrapper
                              [| TypeRule("create_starbase", createStarbaseLazy.Value)
                                 eopEffectLazy.Value
                                 leftScopeLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          rules,
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )
                  // let comp = CompletionService([TypeRule ("create_starbase", RulesParser.createStarbaseLazy.Value)], [RulesParser.createStarbaseTypeDefLazy.Value], Map.empty, Map.empty, [], Set.empty, [], [])
                  let pos = mkPos 4 9
                  let suggestions = infoService.GetInfo(pos, entity)

                  match suggestions with
                  | None -> Expect.isTrue false "info failed"
                  | Some(context, _) ->
                      let scopes = context.Scopes

                      let expected =
                          [ (scopeManager.ParseScope () "Country")
                            (scopeManager.ParseScope () "Planet")
                            (scopeManager.ParseScope () "Country") ]

                      Expect.sequenceEqual scopes expected "Scopes should match"
              | Failure(e, _, _) -> Expect.isTrue false e
          ptestCase "test scope at pos leaf"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                         effect = {\n\
                         every_owned_planet = {\n\
                         log = yes \n\
                         }\n\
                         }\n\
                         }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let rules =
                      RuleValidationService(
                          RulesWrapper
                              [| TypeRule("create_starbase", createStarbaseLazy.Value)
                                 eopEffectLazy.Value
                                 leftScopeLazy.Value
                                 logEffectLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          (scopeManager.ParseScope () "Any"),
                          changeScope,
                          defaultContext,
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let infoService =
                      InfoService(
                          RulesWrapper
                              [| TypeRule("create_starbase", createStarbaseLazy.Value)
                                 eopEffectLazy.Value
                                 leftScopeLazy.Value
                                 logEffectLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          rules,
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )
                  // let comp = CompletionService([TypeRule ("create_starbase", RulesParser.createStarbaseLazy.Value)], [RulesParser.createStarbaseTypeDefLazy.Value], Map.empty, Map.empty, [], Set.empty, [], [])
                  let pos = mkPos 4 2
                  let suggestions = infoService.GetInfo(pos, entity)

                  match suggestions with
                  | None -> Expect.isTrue false "info failed"
                  | Some(context, _) ->
                      let scopes = context.Scopes

                      let expected =
                          [ (scopeManager.ParseScope () "Planet")
                            (scopeManager.ParseScope () "Country") ]

                      Expect.sequenceEqual scopes expected "Scopes should match"

                  let pos = mkPos 4 8
                  let suggestions = infoService.GetInfo(pos, entity)

                  match suggestions with
                  | None -> Expect.isTrue false "info failed"
                  | Some(context, _) ->
                      let scopes = context.Scopes

                      let expected =
                          [ (scopeManager.ParseScope () "Planet")
                            (scopeManager.ParseScope () "Country") ]

                      Expect.sequenceEqual scopes expected "Scopes should match"

              | Failure(e, _, _) -> Expect.isTrue false e

          ]


[<Tests>]
let testsConfig =
    testList
        "full config"
        [ testWithCapturedLogs "basic"
          <| fun () ->
              let configtext =
                  [ "./testfiles/configtests/config/test.cwt",
                    File.ReadAllText "./testfiles/configtests/config/test.cwt" ]

              let configtext =
                  ("./testfiles/validationtests/trigger_docs.log",
                   File.ReadAllText "./testfiles/validationtests/trigger_docs.log")
                  :: configtext

              let configtext =
                  ("./testfiles/validationtests/setup.log", File.ReadAllText "./testfiles/validationtests/setup.log")
                  :: configtext

              let folder = "./testfiles/configtests/completiontests"
              // let triggers, effects = parseDocsFile "./testfiles/validationtests/trigger_docs_2.0.4.txt" |> (function |Success(p, _, _) -> DocsParser.processDocs (scopeManager.ParseScopes) p)
              // let modifiers = SetupLogParser.parseLogsFile "./testfiles/validationtests/setup.log" |> (function |Success(p, _, _) -> SetupLogParser.processLogs p)
              let settings = emptyStellarisSettings folder

              let settings =
                  { settings with
                      embedded = FromConfig([], [])
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              //let stl = STLGame(folder, Files(scopeManager.ParseScope() "All"), "", triggers, effects, modifiers, [], [configtext], [STL STLLang.English], false, true, true)

              let input =
                  "ship_size = {\n\
                            default_behavior =  \n\
                            }"

              let pos = mkPos 2 20
              // let suggestions = stl.Complete pos "common/ship_sizes/test.txt" input
              let suggestions = stl.Complete pos "common/ship_sizes/test.txt" input
              //eprintfn "%A" suggestions
              let suggestions =
                  suggestions
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.sort

              let expected = [ "default"; "swarm" ] |> Seq.sort
              Expect.sequenceEqual suggestions expected "Completion should match"

          testWithCapturedLogs "basic with config load"
          <| fun () ->
              let configtext =
                  [ "./testfiles/configtests/config/test.cwt",
                    File.ReadAllText "./testfiles/configtests/config/test.cwt" ]

              let configtext =
                  ("./testfiles/validationtests/trigger_docs.log",
                   File.ReadAllText "./testfiles/validationtests/trigger_docs.log")
                  :: configtext

              let configtext =
                  ("./testfiles/validationtests/setup.log", File.ReadAllText "./testfiles/validationtests/setup.log")
                  :: configtext

              let folder = "./testfiles/configtests/completiontests"
              // let triggers, effects = parseDocsFile "./testfiles/validationtests/trigger_docs_2.0.4.txt" |> (function |Success(p, _, _) -> DocsParser.processDocs (scopeManager.ParseScopes) p)
              // let modifiers = SetupLogParser.parseLogsFile "./testfiles/validationtests/setup.log" |> (function |Success(p, _, _) -> SetupLogParser.processLogs p)
              let settings = emptyStellarisSettings folder

              let settings =
                  { settings with
                      embedded = FromConfig([], [])
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>

              let input =
                  "ship_size = {\n\
                            default_behavior = s \n\
                            }"

              let pos = mkPos 2 20
              let pos2 = mkPos 2 5

              let _ =
                  stl.Complete pos2 "common/ship_sizes/test.txt" input
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.sort

              let suggestions =
                  stl.Complete pos "common/ship_sizes/test.txt" input
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.sort

              let expected = [ "default"; "swarm" ] |> Seq.sort
              Expect.sequenceEqual suggestions expected "Completion should match"

          testWithCapturedLogs "shipsize prerequisits"
          <| fun () ->
              let configtext =
                  [ "./testfiles/configtests/config/test.cwt",
                    File.ReadAllText "./testfiles/configtests/config/test.cwt" ]

              let configtext =
                  ("./testfiles/validationtests/trigger_docs.log",
                   File.ReadAllText "./testfiles/validationtests/trigger_docs.log")
                  :: configtext

              let configtext =
                  ("./testfiles/validationtests/setup.log", File.ReadAllText "./testfiles/validationtests/setup.log")
                  :: configtext

              let folder = "./testfiles/configtests/completiontests"
              // let triggers, effects = parseDocsFile "./testfiles/validationtests/trigger_docs_2.0.4.txt" |> (function |Success(p, _, _) -> DocsParser.processDocs (scopeManager.ParseScopes) p)
              // let modifiers = SetupLogParser.parseLogsFile "./testfiles/validationtests/setup.log" |> (function |Success(p, _, _) -> SetupLogParser.processLogs p)
              let settings = emptyStellarisSettings folder

              let settings =
                  { settings with
                      embedded = FromConfig([], [])
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>

              let input =
                  "ship_size = {\n\
                            prerequisites = {\n\
                            \n\
                            }\n\
                            }"

              let pos = mkPos 3 0

              let suggestions =
                  stl.Complete pos "common/ship_sizes/test.txt" input
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.sort

              let expected = [ "tech_one"; "tech_two" ] |> Seq.sort
              Expect.sequenceEqual suggestions expected "Completion should match"

          testWithCapturedLogs "shipsize enum"
          <| fun () ->
              let configtext =
                  [ "./testfiles/configtests/config/test.cwt",
                    File.ReadAllText "./testfiles/configtests/config/test.cwt" ]

              let configtext =
                  ("./testfiles/validationtests/trigger_docs.log",
                   File.ReadAllText "./testfiles/validationtests/trigger_docs.log")
                  :: configtext

              let configtext =
                  ("./testfiles/validationtests/setup.log", File.ReadAllText "./testfiles/validationtests/setup.log")
                  :: configtext

              let folder = "./testfiles/configtests/completiontests"
              // let triggers, effects = parseDocsFile "./testfiles/validationtests/trigger_docs_2.0.4.txt" |> (function |Success(p, _, _) -> DocsParser.processDocs (scopeManager.ParseScopes) p)
              // let modifiers = SetupLogParser.parseLogsFile "./testfiles/validationtests/setup.log" |> (function |Success(p, _, _) -> SetupLogParser.processLogs p)
              let settings = emptyStellarisSettings folder

              let settings =
                  { settings with
                      embedded = FromConfig([], [])
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>

              let input =
                  "ship_size = {\n\
                            class = \n\
                            }"

              let pos = mkPos 2 8

              let suggestions =
                  stl.Complete pos "common/ship_sizes/test.txt" input
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.sort

              let expected =
                  [ "shipclass_military"
                    "shipclass_transport"
                    "shipclass_military_station"
                    "shipclass_starbase" ]
                  |> Seq.sort

              Expect.sequenceEqual suggestions expected "Completion should match" ]
//
// [<Tests>]
// let miscTests =
//     testList "miscTests" [
//         ftestWithCapturedLogs "concurrentParse" <| fun () ->
//             let filepath = "./testfiles/configtests/config/test.cwt"
//             let filetext = File.ReadAllText filepath
//             let inner i =
//                 printfn "%A" i
//                 match CKParser.parseString filetext filepath with
//                 | Success (statements, _, _) ->
//                     simpleProcess.ProcessNode() filepath (mkZeroFile filepath) statements |> ignore
//                 | _ -> ()
//             Array.create 10000 0 |> Array.Parallel.iteri (fun i _ -> inner i)
//
//     ]

[<Tests>]
let dynamicParameterScanTests =
    testList
        "dynamic parameter scanning"
        [ testCase "scripted_effect $PARAM$ extraction"
          <| fun () ->
              let input =
                  "test_effect = {\n\
                            set_variable = { which = $AMOUNT$ value = 5 }\n\
                            add_resource = { energy = $ENERGY|10$ }\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                  let ps = Compute.EU4.getScriptedEffectParams node
                  Expect.contains ps "AMOUNT" $"should extract AMOUNT, got %A{ps}"
                  Expect.contains ps "ENERGY" $"should strip default from $ENERGY|10$, got %A{ps}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testCase "script_value $PARAM$ extraction"
          <| fun () ->
              let input =
                  "test_value = {\n\
                            value = $BASE$\n\
                            multiply = $FACTOR|2$\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                  let ps = Compute.EU4.getScriptValueParams node
                  Expect.contains ps "BASE" $"should extract BASE, got %A{ps}"
                  Expect.contains ps "FACTOR" $"should strip default from $FACTOR|2$, got %A{ps}"
              | Failure(e, _, _) -> Expect.isTrue false e ]

[<Tests>]
let nestedEventTargetTests =
    let mkScriptedEffect (node: Node) =
        ScriptedEffect(
            node.KeyId,
            [],
            EffectType.Effect,
            "",
            STLProcess.findAllSavedGlobalEventTargets node |> Set.toList,
            STLProcess.findAllSavedEventTargets node |> Set.toList,
            STLProcess.findAllUsedEventTargets node |> Set.toList,
            STLProcess.findAllFiredOnActions node |> Set.toList
        )

    let parseRoot (input: string) =
        match CKParser.parseString input "test.txt" with
        | Success(r, _, _) -> STLProcess.shipProcess.ProcessNode () "root" range.Zero r
        | Failure(e, _, _) -> failtest e

    let buildEffects (input: string) =
        let root = parseRoot input
        let rawEffects = root.Children |> List.map (fun n -> n, ([]: string list))
        let effects = root.Children |> List.map (mkScriptedEffect >> fun e -> e :> Effect)
        STLProcess.addNestedEventTargetsToEffects rawEffects effects

    let savedTargetsOf (name: string) (effects: Effect list) =
        effects
        |> List.pick (function
            | :? ScriptedEffect as se when se.Name.GetString() == name -> Some se.SavedEventTargets
            | _ -> None)

    let globalTargetsOf (name: string) (effects: Effect list) =
        effects
        |> List.pick (function
            | :? ScriptedEffect as se when se.Name.GetString() == name -> Some se.GlobalEventTargets
            | _ -> None)

    testList
        "nested scripted effect event targets"
        [ testCase "event target existence suffix is not part of the saved target key"
          <| fun () ->
              let input =
                  "test_effect = {\n\
                            event_target:wg_dragon_own_country? = { set_country_flag = checked }\n\
                            exists = event_target:wg_dragon_own_country?\n\
                            is_same_value = event_target:other_target?\n\
                            }"

              let node = parseRoot input
              let used = STLProcess.findAllUsedEventTargets node
              let exists = STLProcess.findAllExistsEventTargets node

              Expect.contains
                  used
                  "wg_dragon_own_country"
                  $"used event target should drop existence suffix, got %A{used}"

              Expect.contains used "other_target" $"value event target should drop existence suffix, got %A{used}"
              Expect.contains exists "wg_dragon_own_country" $"exists target should drop existence suffix, got %A{exists}"
              Expect.isFalse
                  (Set.contains "wg_dragon_own_country?" used)
                  $"used event target should not include '?' in the key, got %A{used}"

              Expect.isFalse
                  (Set.contains "wg_dragon_own_country?" exists)
                  $"exists event target should not include '?' in the key, got %A{exists}"

          testCase "save via nested parameterised call propagates to caller"
          <| fun () ->
              // Mirrors vanilla cosmic storms: try_spawn calls choose_location
              // with EVENT_TARGET_NAME, which does save_event_target_as = $EVENT_TARGET_NAME$
              let input =
                  "choose_location = {\n\
                            random_system = {\n\
                            save_event_target_as = $EVENT_TARGET_NAME$\n\
                            }\n\
                            }\n\
                            try_spawn = {\n\
                            choose_location = {\n\
                            EVENT_TARGET_NAME = new_storm_location\n\
                            }\n\
                            spawn_thing = {\n\
                            position = event_target:new_storm_location\n\
                            }\n\
                            }"

              let saved = buildEffects input |> savedTargetsOf "try_spawn"

              Expect.contains
                  saved
                  "new_storm_location"
                  $"caller should be credited with the nested parameterised save, got %A{saved}"
          testCase "parameter chains resolve across two levels of nesting"
          <| fun () ->
              let input =
                  "saver = {\n\
                            save_event_target_as = $TARGET$\n\
                            }\n\
                            wrapper = {\n\
                            saver = {\n\
                            TARGET = $NAME$\n\
                            }\n\
                            }\n\
                            caller = {\n\
                            wrapper = {\n\
                            NAME = my_target\n\
                            }\n\
                            }"

              let effects = buildEffects input
              let wrapperSaved = effects |> savedTargetsOf "wrapper"
              let callerSaved = effects |> savedTargetsOf "caller"

              Expect.contains
                  wrapperSaved
                  "$NAME$"
                  $"wrapper should keep the unresolved placeholder, got %A{wrapperSaved}"

              Expect.contains
                  callerSaved
                  "my_target"
                  $"caller should resolve the full parameter chain, got %A{callerSaved}"
          testCase "leaf call without params propagates concrete saves"
          <| fun () ->
              let input =
                  "save_it = {\n\
                            save_event_target_as = concrete_target\n\
                            }\n\
                            outer = {\n\
                            save_it = yes\n\
                            }"

              let saved = buildEffects input |> savedTargetsOf "outer"

              Expect.contains
                  saved
                  "concrete_target"
                  $"leaf-style call should propagate concrete saves, got %A{saved}"
          testCase "global save via nested parameterised call propagates to caller"
          <| fun () ->
              // Mirrors vanilla shroud leaders: hire_effect does
              // save_global_event_target_as = $GLOBAL_EVENT_TARGET$
              let input =
                  "hire_effect = {\n\
                            save_global_event_target_as = $GLOBAL_EVENT_TARGET$\n\
                            }\n\
                            outer_effect = {\n\
                            hire_effect = {\n\
                            GLOBAL_EVENT_TARGET = ganthuata\n\
                            }\n\
                            }"

              let globals = buildEffects input |> globalTargetsOf "outer_effect"

              Expect.contains
                  globals
                  "ganthuata"
                  $"caller should be credited with the nested global save, got %A{globals}"
          testCase "call-site substitution credits parameterised saves in effect blocks"
          <| fun () ->
              let input =
                  "hire_effect = {\n\
                            save_global_event_target_as = $GLOBAL_EVENT_TARGET$\n\
                            }\n\
                            event_block = {\n\
                            hidden_effect = {\n\
                            hire_effect = {\n\
                            GLOBAL_EVENT_TARGET = ganthuata\n\
                            }\n\
                            }\n\
                            }"

              let root = parseRoot input

              let hireEffect =
                  root.Children
                  |> List.find (fun n -> n.Key == "hire_effect")
                  |> mkScriptedEffect

              let effectsByName = Map.ofList [ hireEffect.Name.lower, hireEffect ]

              let eventBlock = root.Children |> List.find (fun n -> n.Key == "event_block")

              let saves =
                  CWTools.Validation.Stellaris.STLEventValidation.findSubstitutedCallSaves effectsByName eventBlock

              Expect.contains
                  saves
                  "ganthuata"
                  $"call-site scan should substitute the global save parameter, got %A{saves}" ]
