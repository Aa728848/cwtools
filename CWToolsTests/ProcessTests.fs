module ProcessTests
open TestHelpers

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

          testWithCapturedLogs "forbid_quoted_values inherits into aliased blocks"
          <| fun () ->
              let config =
                  "## forbid_quoted_values = { from }\n\
                  alias[effect:create_species] = {\n\
                          ## cardinality = 0..1\n\
                          name = scalar\n\
                          ## cardinality = 0..1\n\
                          traits = {\n\
                              ## cardinality = 0..1\n\
                              ideal_planet_class = scope[any]\n\
                          }\n\
                  }\n\
                  test_event = {\n\
                          ## cardinality = 0..1\n\
                          effect = {\n\
                              alias_name[effect] = alias_match_left[effect]\n\
                          }\n\
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
                      | TypeRule(_, rs) -> Some(rs)
                      | _ -> None)
                  |> Array.ofList

              let service =
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

              let validate createSpeciesBody =
                  match CKParser.parseString $"test_event = {{ effect = {{ create_species = {{ {createSpeciesBody} }} }} }}" "test" with
                  | Success(r, _, _) ->
                      let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                      service.ApplyNodeRule(typeRules, node)
                  | Failure(e, _, _) -> failtest e

              match validate "name = \"from\"" with
              | OK -> failtest "Quoted from in create_species should be reported"
              | Invalid(_, es) ->
                  Expect.equal es.Length 1 $"Only quoted from should be flagged %A{es}"
                  let error = es |> List.head
                  Expect.stringContains error.message "use from instead" "Should suggest removing the quotes"
                  Expect.equal error.severity Severity.Error "Quoted from should be an error"

              match validate "name = from" with
              | OK -> ()
              | Invalid(_, es) -> failtest $"Unquoted from should be valid %A{es}"

              match validate "name = \"Local Name\"" with
              | OK -> ()
              | Invalid(_, es) -> failtest $"Other quoted values should stay valid %A{es}"

              match validate "traits = { ideal_planet_class = \"from\" }" with
              | OK -> failtest "Quoted from in a nested create_species rule should be reported"
              | Invalid(_, es) ->
                  Expect.equal es.Length 1 $"Only nested quoted from should be flagged %A{es}"
                  Expect.stringContains (es |> List.head).message "use from instead" "Nested errors should suggest removing the quotes"

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

