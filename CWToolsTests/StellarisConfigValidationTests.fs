module StellarisConfigValidationTests

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

          testWithCapturedLogs "value_set values inside value clauses are collected and completed"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))

              let config =
                  "types = {\n\
                       type[ship_size] = {\n\
                           path = \"game/common/ship_sizes\"\n\
                       }\n\
                   }\n\
                   ship_size = {\n\
                       ## cardinality = 0..1\n\
                       ship_roles = {\n\
                           ## cardinality = 0..inf\n\
                           value_set[ship_size_ship_roles]\n\
                       }\n\
                       ## cardinality = 0..1\n\
                       triggered_ship_roles = {\n\
                           ## cardinality = 0..inf\n\
                           {\n\
                               name = value_set[ship_size_ship_roles]\n\
                           }\n\
                       }\n\
                       ## cardinality = 0..inf\n\
                       roles = value[ship_size_ship_roles]\n\
                   }\n"

              let rules, types, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "ship_sizes.cwt"
                      config

              let input =
                  "ship_size = {\n\
                       ship_roles = { carrier }\n\
                       triggered_ship_roles = {\n\
                           {\n\
                               name = artillery\n\
                           }\n\
                           {\n\
                               name = artillery_stealth\n\
                           }\n\
                       }\n\
                       roles = car\n\
                   }\n"

              match CKParser.parseString input "common/ship_sizes/test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r

                  let entity =
                      { filepath = "common/ship_sizes/test.txt"
                        logicalpath = "common/ship_sizes/test.txt"
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

                  let definedVars = infoService.GetDefinedVariables entity

                  let collected =
                      match Map.tryFind "ship_size_ship_roles" definedVars with
                      | Some values -> values |> Seq.map fst |> List.ofSeq |> List.sort
                      | None -> []

                  Expect.sequenceEqual
                      collected
                      [ "artillery"; "artillery_stealth"; "carrier" ]
                      "value_set values inside value clauses should be collected"

                  let varMap =
                      definedVars
                      |> Map.map (fun _ values -> values |> Seq.map fst |> createStringSet)
                      |> fun map -> map.ToFrozenDictionary()

                  let comp =
                      CompletionService(
                          rulesWrapper,
                          types,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          varMap,
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
                      comp.Complete(mkPos 11 10, entity, None, None)
                      |> Seq.map (function
                          | CompletionResponse.Simple(c, _, _) -> c
                          | Snippet(l, _, _, _, _) -> l
                          | Detailed(l, _, _, _) -> l)
                      |> List.ofSeq

                  Expect.containsAll
                      suggestions
                      [ "artillery"; "artillery_stealth"; "carrier" ]
                      "value[ship_size_ship_roles] should complete collected values"
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

          testWithCapturedLogs "test completion before an existing root"
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

                  let expected = [ "size"; "owner"; "building"; "effect"; "module" ] |> Seq.sort
                  Expect.sequenceEqual
                      suggestions
                      expected
                      "Completion recovery before an existing root should use that root's fields"
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

          testWithCapturedLogs "test partial on_action root completes configured subtype keys"
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

              Expect.contains suggestions "on_game_start" "Configured on_action keys should be offered at the file root"
              Expect.contains suggestions "on_monthly_pulse" "All configured subtype keys should remain available for client filtering"
              Expect.isFalse (suggestions |> List.contains "events") "Root completion must not return on_action child fields"

          testWithCapturedLogs "test on_action completion after stray root close stays at root"
          <| fun () ->
              let configtext =
                  [ "./testfiles/configtests/config/on_actions.cwt",
                    "types = {\n\
                          ## root_completion = subtypes\n\
                          type[on_action] = {\n\
                              path = \"game/common/on_actions\"\n\
                              ## type_key_filter = on_monthly_pulse\n\
                              subtype[on_monthly_pulse] = { }\n\
                          }\n\
                      }\n\
                      on_action = {\n\
                          events = { scalar = scalar }\n\
                          random_events = { scalar = scalar }\n\
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
              let input = "on_monthly_pulse = {\n    events = { test.1 }\n}\n}"
              let labels =
                  stl.Complete (mkPos 4 1) "common/on_actions/test.txt" input
                  |> List.map (function
                      | Simple(label, _, _)
                      | Detailed(label, _, _, _)
                      | Snippet(label, _, _, _, _) -> label)

              Expect.isFalse (labels |> List.contains "events") "A stray root close must not reopen the previous on_action RHS"
              Expect.isFalse (labels |> List.contains "random_events") "Root recovery must not return on_action child fields"

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

          testCase "test scope at pos simple nodes"
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
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseRule ()); eopEffectRule () |],
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
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseRule ()); eopEffectRule () |],
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
                  // let comp = CompletionService([TypeRule ("create_starbase", RulesParser.createStarbaseRule ())], [RulesParser.createStarbaseTypeDefLazy.Value], Map.empty, Map.empty, [], Set.empty, [], [])
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
          testCase "test scope at pos prev"
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
                              [| TypeRule("create_starbase", createStarbaseRule ())
                                 eopEffectRule ()
                                 leftScopeRule () |],
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
                              [| TypeRule("create_starbase", createStarbaseRule ())
                                 eopEffectRule ()
                                 leftScopeRule () |],
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
                  // let comp = CompletionService([TypeRule ("create_starbase", RulesParser.createStarbaseRule ())], [RulesParser.createStarbaseTypeDefLazy.Value], Map.empty, Map.empty, [], Set.empty, [], [])
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
          testCase "test scope at pos leaf"
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
                              [| TypeRule("create_starbase", createStarbaseRule ())
                                 eopEffectRule ()
                                 leftScopeRule ()
                                 logEffectRule () |],
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
                              [| TypeRule("create_starbase", createStarbaseRule ())
                                 eopEffectRule ()
                                 leftScopeRule ()
                                 logEffectRule () |],
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
                  // let comp = CompletionService([TypeRule ("create_starbase", RulesParser.createStarbaseRule ())], [RulesParser.createStarbaseTypeDefLazy.Value], Map.empty, Map.empty, [], Set.empty, [], [])
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
              | Failure(e, _, _) -> Expect.isTrue false e
          testCase "scripted_effect [[PARAM]content] extraction at start"
          <| fun () ->
              let input =
                  "test_effect = {\n\
                            [[ag_failed]\n\
                                set_variable = { which = result value = -1 }\n\
                            ]\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                  let ps = Compute.EU4.getScriptedEffectParams node
                  Expect.contains ps "ag_failed" $"should extract ag_failed from [[ag_failed], got %A{ps}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testCase "scripted_effect [[PARAM]content] extraction embedded in string"
          <| fun () ->
              let input =
                  "test_effect = {\n\
                            set_variable = { which = result[[ag_failed]_failed] value = 1 }\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                  let ps = Compute.EU4.getScriptedEffectParams node
                  Expect.contains ps "ag_failed" $"should extract ag_failed from embedded [[ag_failed]_failed], got %A{ps}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testCase "scripted_effect [[!PARAM]content] negated extraction"
          <| fun () ->
              let input =
                  "test_effect = {\n\
                            [[!no_effect]\n\
                                do_something = yes\n\
                            ]\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                  let ps = Compute.EU4.getScriptedEffectParams node
                  Expect.contains ps "no_effect" $"should extract no_effect from [[!no_effect], got %A{ps}"
              | Failure(e, _, _) -> Expect.isTrue false e ]

