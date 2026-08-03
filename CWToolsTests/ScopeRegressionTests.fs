module ScopeRegressionTests

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
let eu4MetascriptRegressionTests =
    let parseEntity text =
        let logicalPath = "common/scripted_effects/test.txt"

        match CKParser.parseString text logicalPath with
        | Success(statements, _, _) ->
            let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero statements

            { filepath = logicalPath
              logicalpath = logicalPath
              rawEntity = node
              entity = node
              validate = true
              entityType = EntityType.ScriptedEffects
              overwrite = Overwrite.No }
        | Failure(error, _, _) -> failwith error

    let parseEffect text =
        (parseEntity text).entity.Nodes |> Seq.exactlyOne

    testList
        "EU4 metascript regression"
        [ testCase "incremental recompute refreshes bracket parameters"
          <| fun () ->
              let initial =
                  parseEntity
                      "my_scripted_effect = { set_global_flag = $prefix$_test_flag }"

              let data = Compute.EU4.computeEU4Data (fun () -> None) initial
              Expect.contains
                  (data.ScriptedEffectParams |> Option.defaultValue [])
                  "prefix"
                  "Initial parameter scan should include dollar parameters"

              let updated =
                  parseEntity
                      "my_scripted_effect = { set_global_flag = $prefix$_test_flag [[extra_flag] set_global_flag = extra_test_flag ] }"

              Compute.EU4.computeEU4DataUpdate (fun () -> None) updated data

              Expect.contains
                  (data.ScriptedEffectParams |> Option.defaultValue [])
                  "extra_flag"
                  "Incremental recompute should refresh bracket parameters"

          testCase "Stellaris incremental recompute refreshes parameters"
          <| fun () ->
              let initial =
                  parseEntity
                      "my_scripted_effect = { set_global_flag = $initial_param$ }"

              let data = Compute.STL.computeSTLData (fun () -> None) initial

              let updated =
                  parseEntity
                      "my_scripted_effect = { set_global_flag = $updated_param$ }"

              Compute.STL.computeSTLDataUpdate (fun () -> None) updated data

              Expect.contains
                  (data.ScriptedEffectParams |> Option.defaultValue [])
                  "updated_param"
                  "Stellaris incremental recompute should refresh scripted parameters"
              Expect.isFalse
                  ((data.ScriptedEffectParams |> Option.defaultValue []) |> List.contains "initial_param")
                  "Stellaris incremental recompute should discard removed scripted parameters"

          testCase "Jomini incremental recompute refreshes parameters"
          <| fun () ->
              let initial =
                  parseEntity
                      "my_scripted_effect = { set_global_flag = $initial_param$ }"

              let data = Compute.Jomini.computeJominiData (fun () -> None) initial

              let updated =
                  parseEntity
                      "my_scripted_effect = { set_global_flag = $updated_param$ }"

              Compute.Jomini.computeJominiDataUpdate (fun () -> None) updated data

              Expect.contains
                  (data.ScriptedEffectParams |> Option.defaultValue [])
                  "updated_param"
                  "Jomini incremental recompute should refresh scripted parameters"
              Expect.isFalse
                  ((data.ScriptedEffectParams |> Option.defaultValue []) |> List.contains "initial_param")
                  "Jomini incremental recompute should discard removed scripted parameters"

          testCase "same-leaf conditional strips its glued closing bracket"
          <| fun () ->
              let effect =
                  parseEffect
                      "set_modifier_scripted_effect = { set_country_flag = used_example_effect_flag [[macro]add_country_modifier = example_macro_modifier] }"

              let expanded =
                  CWTools.Validation.Common.CommonValidation.applyBracketConditionals
                      [ "macro", "enabled" ]
                      effect.AllArray

              let modifierLeaves =
                  expanded
                  |> Array.choose (function
                      | LeafC leaf when leaf.Key = "add_country_modifier" -> Some leaf
                      | _ -> None)

              Expect.hasLength modifierLeaves 1 "A non-no EU4 macro value should include the conditional leaf"
              Expect.equal
                  modifierLeaves.[0].ValueText
                  "example_macro_modifier"
                  "The structural closing bracket must not remain in the modifier value"

              let inactiveEffect =
                  parseEffect
                      "set_modifier_scripted_effect = { set_country_flag = used_example_effect_flag [[macro]add_country_modifier = example_macro_modifier] }"

              let inactive =
                  CWTools.Validation.Common.CommonValidation.applyBracketConditionals
                      [ "macro", "no" ]
                      inactiveEffect.AllArray

              Expect.isFalse
                  (inactive
                   |> Array.exists (function
                       | LeafC leaf when leaf.Key = "add_country_modifier" -> true
                       | _ -> false))
                  "EU4 macro = no should omit the conditional leaf"

          testCase "definition validation strips a same-leaf structural close"
          <| fun () ->
              let effect =
                  parseEffect
                      "set_modifier_scripted_effect = { [[macro]add_country_modifier = example_macro_modifier] }"

              let leaf = effect.Leaves |> Seq.exactlyOne
              let key, _, validationLeaf = RuleValidationHelpers.normalizeConditionalLeaf leaf

              Expect.equal key "add_country_modifier" "Validation should use the conditional leaf's real key"
              Expect.equal
                  validationLeaf.ValueText
                  "example_macro_modifier"
                  "Definition validation should not receive the structural closing bracket" ]

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

    let usedTargetsOf (name: string) (effects: Effect list) =
        effects
        |> List.pick (function
            | :? ScriptedEffect as se when se.Name.GetString() == name -> Some se.UsedEventTargets
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

          testCase "global save under owner existence guard is collected"
          <| fun () ->
              let input =
                  "fleet_event = {\n\
                            id = ai_action.6\n\
                            immediate = {\n\
                            owner? = { save_global_event_target_as = kuat_friendly_faction }\n\
                            }\n\
                            }"

              let node = parseRoot input
              let globals = STLProcess.findAllSavedGlobalEventTargets node

              Expect.contains
                  globals
                  "kuat_friendly_faction"
                  $"owner? global save should be collected, got %A{globals}"
          testCase "global saved event target satisfies guarded event-chain usage"
          <| fun () ->
              let input =
                  "event = {\n\
                            id = ai_action.14\n\
                            trigger = {\n\
                            exists = event_target:kuat_friendly_faction\n\
                            any_galaxy_fleet = {\n\
                            controller? = { is_at_war_with = event_target:kuat_friendly_faction }\n\
                            }\n\
                            }\n\
                            immediate = {\n\
                            event_target:kuat_friendly_faction = { clear_orders = yes }\n\
                            }\n\
                            }\n\
                            fleet_event = {\n\
                            id = ai_action.6\n\
                            immediate = {\n\
                            owner? = { save_global_event_target_as = kuat_friendly_faction }\n\
                            set_automatic_fleet_avaliable = { FRIENDLY_TARGET = event_target:kuat_friendly_faction }\n\
                            }\n\
                            }"

              let root = parseRoot input
              let events = root.Children

              let globals =
                  events
                  |> List.map STLProcess.findAllSavedGlobalEventTargets
                  |> List.fold Set.union Set.empty

              let result =
                  CWTools.Validation.Stellaris.STLEventValidation.checkEventChain [] [] [] globals events

              Expect.equal result OK $"global target should suppress CW220/CW221, got %A{result}"
          testCase "legacy optional scopes work in dotted event target chains"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))

              let parseScope name = scopeManager.ParseScope () name
              let country = parseScope "Country"
              let planet = parseScope "Planet"
              let galacticObject = parseScope "GalacticObject"
              let star = parseScope "Star"
              let ship = parseScope "Ship"

              let mkLink (name: string) (inputs: Scope list) (target: Scope) =
                  ScopedEffect(name, inputs, target, EffectType.Link, "", "", false) :> Effect

              let links =
                  EffectMap.FromList
                      [ mkLink "owner" [ planet; galacticObject; star; ship ] country
                        mkLink "solar_system" [ planet; star ] galacticObject
                        mkLink "star" [ galacticObject ] star
                        mkLink "event_target:surveyed_planet" scopeManager.AllScopes planet ]

              let resolve root current (key: string) =
                  let context =
                      { Root = root
                        From = []
                        FromDepth = 0
                        FromDepthStack = []
                        Scopes = [ current ] }

                  match
                      changeScope.Invoke(
                          false,
                          true,
                          links,
                          EffectMap(),
                          [],
                          createStringSet [],
                          System.ReadOnlySpan<char>(key.ToCharArray()),
                          context
                      )
                  with
                  | NewScope(context, _, _) -> context.CurrentScope
                  | other -> failtestf "%s should resolve as a legacy scope chain, got %A" key other

              Expect.equal (resolve country planet "owner?") country "owner? should behave like owner"
              Expect.equal (resolve planet ship "root.owner?") country "root.owner? should strip the optional marker"
              Expect.equal
                  (resolve country planet "event_target:target_system.star.owner?")
                  country
                  "event target scope chains should allow optional legacy links"
              Expect.equal
                  (resolve country ship "event_target:surveyed_planet")
                  planet
                  "a known saved event target should resolve to its exact scope"
              Expect.equal
                  (resolve country ship "event_target:surveyed_planet.owner")
                  country
                  "links after a known saved event target should use its exact scope"
              Expect.equal
                  (resolve country ship "event_target:unknown_target")
                  scopeManager.AnyScope
                  "an unknown event target should keep the conservative Any fallback"

              let lookup = Lookup()

              lookup.savedEventTargets <-
                  ResizeArray(
                      [ "unique_planet", range.Zero, planet
                        "unique_planet", range.Zero, planet
                        "ambiguous_target", range.Zero, planet
                        "ambiguous_target", range.Zero, country
                        "partially_known_target", range.Zero, ship
                        "partially_known_target", range.Zero, scopeManager.AnyScope ]
                  )

              let savedLinks = STLGameFunctions.savedEventTargetLinks lookup
              Expect.equal
                  savedLinks.Length
                  1
                  "only targets whose every save has one known project-wide scope should get an exact link"
              Expect.equal (savedLinks[0].Name.GetString()) "event_target:unique_planet" "the exact link should use event_target syntax"

              match savedLinks[0] with
              | :? ScopedEffect as link -> Expect.equal link.Target (Some planet) "the exact link should retain the saved scope"
              | other -> failtestf "saved event target link should be scoped, got %A" other
          testWithCapturedLogs "an unresolved FROM save prevents an exact saved event target scope"
          <| fun () ->
              let root =
                  Path.Combine(Path.GetTempPath(), "cwtools-ambiguous-event-target-" + System.Guid.NewGuid().ToString("N"))

              let eventsDir = Path.Combine(root, "events")
              Directory.CreateDirectory(eventsDir) |> ignore
              let eventFile = Path.Combine(eventsDir, "ambiguous_event_target_events.txt")
              let eventText =
                  "namespace = ambiguous_target\n\
                   country_event = {\n\
                       id = ambiguous_target.1\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       immediate = {\n\
                           from = {\n\
                               save_event_target_as = current_marauder_diplomacy\n\
                           }\n\
                       }\n\
                   }\n\
                   country_event = {\n\
                       id = ambiguous_target.2\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       immediate = {\n\
                           owner_species = {\n\
                               save_event_target_as = current_marauder_diplomacy\n\
                           }\n\
                       }\n\
                   }\n\
                   country_event = {\n\
                       id = ambiguous_target.3\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       trigger = {\n\
                           event_target:current_marauder_diplomacy = {\n\
                               has_country_flag = marauder_country_scope_marker\n\
                           }\n\
                       }\n\
                   }"

              File.WriteAllText(eventFile, eventText)

              try
                  let configText = configFilesFromDir (Path.Combine(stellarisConfigRoot.Value, "config"))

                  let settings =
                      { emptyStellarisSettings root with
                          rules =
                              Some
                                  { ruleFiles = configText
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stlGame = STLGame(settings)
                  let stl = stlGame :> IGame<STLComputedData>
                  let savedScopes =
                      stlGame.Lookup.savedEventTargets
                      |> Seq.choose (fun (name, _, scope) ->
                          if name == "current_marauder_diplomacy" then Some(scope.ToString()) else None)
                      |> Set.ofSeq

                  Expect.contains savedScopes "Any" "the unresolved FROM save should be retained as unknown scope evidence"
                  Expect.contains savedScopes "Species" "the owner_species save should retain its exact Species scope"
                  let marker = "marauder_country_scope_marker"
                  let markerIndex = eventText.IndexOf(marker, System.StringComparison.Ordinal)
                  Expect.isGreaterThan markerIndex -1 "the event-target scope marker should exist"
                  let before = eventText.Substring(0, markerIndex)
                  let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
                  let lastLineBreak = before.LastIndexOf('\n')
                  let column = if lastLineBreak < 0 then markerIndex else markerIndex - lastLineBreak - 1
                  let context = stl.ScopesAtPos (mkPos line column) eventFile eventText

                  Expect.isSome context "the ambiguous event target should have a scope context"
                  Expect.equal
                      (context.Value.CurrentScope.ToString())
                      "Any"
                      "an unresolved save must prevent a different save from fixing the target to Species"

                  let wrongScopeErrors =
                      stl.ValidationErrors()
                      |> List.filter (fun error ->
                          System.String.Equals(
                              Path.GetFullPath(error.range.FileName),
                              Path.GetFullPath(eventFile),
                              System.StringComparison.OrdinalIgnoreCase
                          )
                          && error.message.Contains("has_country_flag", System.StringComparison.OrdinalIgnoreCase)
                          && (error.code = "CW243" || error.code = "CW245"))

                  Expect.isEmpty
                      wrongScopeErrors
                      $"the conservatively unknown target should not report a Species/Country mismatch: %A{wrongScopeErrors}"
              finally
                  if Directory.Exists(root) then Directory.Delete(root, true)
          testCase "event target parameter values normalize after substitution"
          <| fun () ->
              let input =
                  "inner_effect = {\n\
                            event_target:$OWNER$ = { clear_orders = yes }\n\
                            exists = event_target:$OWNER$\n\
                            }\n\
                            outer_effect = {\n\
                            inner_effect = { OWNER = event_target:kuat_friendly_faction }\n\
                            }"

              let used = buildEffects input |> usedTargetsOf "outer_effect"

              Expect.contains
                  used
                  "kuat_friendly_faction"
                  $"scope-valued parameter should normalize to the saved target key, got %A{used}"

              Expect.isFalse
                  (List.contains "event_target:kuat_friendly_faction" used)
                  $"scope-valued parameter should not keep a nested event_target prefix, got %A{used}"
          testWithCapturedLogs "STL game validation accepts global target saved in legacy optional scope"
          <| fun () ->
              let root =
                  Path.Combine(Path.GetTempPath(), "cwtools-event-target-" + System.Guid.NewGuid().ToString("N"))

              let eventsDir = Path.Combine(root, "events")
              let scriptedEffectsDir = Path.Combine(root, "common", "scripted_effects")
              Directory.CreateDirectory(eventsDir) |> ignore
              Directory.CreateDirectory(scriptedEffectsDir) |> ignore
              let eventFile = Path.Combine(eventsDir, "kuat_action_event.txt")
              let effectFile = Path.Combine(scriptedEffectsDir, "kuat_effects.txt")
              let eventText =
                  "event = {\n\
                            id = ai_action.14\n\
                            hide_window = yes\n\
                            is_triggered_only = yes\n\
                            trigger = {\n\
                            exists = event_target:kuat_friendly_faction\n\
                            any_galaxy_fleet = {\n\
                            exists = controller\n\
                            controller? = { is_at_war_with = event_target:kuat_friendly_faction }\n\
                            }\n\
                            }\n\
                            immediate = {\n\
                            event_target:kuat_friendly_faction = { clear_orders = yes }\n\
                            kuat_exe_auto_fleet_action = { OWNER = event_target:kuat_friendly_faction }\n\
                            }\n\
                            }\n\
                            fleet_event = {\n\
                            id = ai_action.6\n\
                            hide_window = yes\n\
                            is_triggered_only = yes\n\
                            immediate = {\n\
                            owner? = { save_global_event_target_as = kuat_friendly_faction }\n\
                            set_automatic_fleet_avaliable = { FRIENDLY_TARGET = event_target:kuat_friendly_faction }\n\
                            }\n\
                            }"
              let effectText =
                  "kuat_exe_auto_fleet_action = {\n\
                            event_target:$OWNER$ = { clear_orders = yes }\n\
                            exists = event_target:$OWNER$\n\
                            }"

              File.WriteAllText(eventFile, eventText)
              File.WriteAllText(effectFile, effectText)

              try
                  let configText = configFilesFromDir (Path.Combine(stellarisConfigRoot.Value, "config"))

                  let settings =
                      { emptyStellarisSettings root with
                          rules =
                              Some
                                  { ruleFiles = configText
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>
                  let eventTargetErrors phase errors =
                      errors
                      |> List.filter (fun e ->
                          (e.code = "CW220" || e.code = "CW221")
                          && e.message.Contains("kuat_friendly_faction"))
                      |> fun matches ->
                          Expect.isEmpty matches $"{phase} should not report kuat_friendly_faction as unsaved: %A{matches}"

                  stl.ValidationErrors() |> eventTargetErrors "full validation"
                  stl.UpdateFile false eventFile (Some eventText) |> eventTargetErrors "UpdateFile validation"
              finally
                  if Directory.Exists(root) then Directory.Delete(root, true)
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
          testWithCapturedLogs "parameterized and wrapped event target saves preserve scope"
          <| fun () ->
              let root =
                  Path.Combine(Path.GetTempPath(), "cwtools-event-target-scope-" + System.Guid.NewGuid().ToString("N"))

              let eventsDir = Path.Combine(root, "events")
              let scriptedEffectsDir = Path.Combine(root, "common", "scripted_effects")
              Directory.CreateDirectory(eventsDir) |> ignore
              Directory.CreateDirectory(scriptedEffectsDir) |> ignore
              let eventFile = Path.Combine(eventsDir, "event_target_scope_events.txt")
              let effectFile = Path.Combine(scriptedEffectsDir, "event_target_scope_effects.txt")
              let eventText =
                  "namespace = target_scope\n\
                   country_event = {\n\
                       id = target_scope.1\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       immediate = {\n\
                           save_parameterized_target = { TARGET = parameter_country_target }\n\
                           save_parameterized_global_target = { TARGET = parameter_global_country_target }\n\
                           save_wrapped_planet_target = { TARGET = wrapped_planet_target }\n\
                           event_target:parameter_country_target = {\n\
                               set_country_flag = parameter_country_scope_marker\n\
                           }\n\
                           event_target:parameter_global_country_target = {\n\
                               set_country_flag = parameter_global_country_scope_marker\n\
                           }\n\
                           event_target:wrapped_planet_target = {\n\
                               set_planet_flag = wrapped_planet_scope_marker\n\
                           }\n\
                       }\n\
                   }"
              let effectText =
                  "save_parameterized_target = {\n\
                       save_event_target_as = $TARGET$\n\
                   }\n\
                   save_parameterized_global_target = {\n\
                       save_global_event_target_as = $TARGET$\n\
                   }\n\
                   save_wrapped_planet_target = {\n\
                       random_owned_planet = {\n\
                           save_parameterized_target = { TARGET = $TARGET$ }\n\
                       }\n\
                   }"

              File.WriteAllText(eventFile, eventText)
              File.WriteAllText(effectFile, effectText)

              let posOf (needle: string) =
                  let marker = eventText.IndexOf(needle, System.StringComparison.Ordinal)
                  Expect.isGreaterThan marker -1 $"scope marker {needle} was not found"
                  let before = eventText.Substring(0, marker)
                  let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
                  let lastLineBreak = before.LastIndexOf('\n')
                  let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
                  mkPos line column

              try
                  let configText = configFilesFromDir (Path.Combine(stellarisConfigRoot.Value, "config"))

                  let settings =
                      { emptyStellarisSettings root with
                          rules =
                              Some
                                  { ruleFiles = configText
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>

                  let expectScope expected marker =
                      let context = stl.ScopesAtPos (posOf marker) eventFile eventText
                      Expect.isSome context $"{marker} should have a scope context"
                      Expect.equal
                          (context.Value.CurrentScope.ToString())
                          expected
                          $"{marker} should resolve through the saved event target"

                  expectScope "Country" "parameter_country_scope_marker"
                  expectScope "Country" "parameter_global_country_scope_marker"
                  expectScope "Planet" "wrapped_planet_scope_marker"
              finally
                  if Directory.Exists(root) then Directory.Delete(root, true)
          testWithCapturedLogs "parameterized and nested inline scripts preserve event target scope"
          <| fun () ->
              let root =
                  Path.Combine(Path.GetTempPath(), "cwtools-inline-event-target-scope-" + System.Guid.NewGuid().ToString("N"))

              let eventsDir = Path.Combine(root, "events")
              let inlineScriptsDir = Path.Combine(root, "common", "inline_scripts", "event_target_scope")
              Directory.CreateDirectory(eventsDir) |> ignore
              Directory.CreateDirectory(inlineScriptsDir) |> ignore
              let eventFile = Path.Combine(eventsDir, "inline_event_target_scope_events.txt")
              let directFile = Path.Combine(inlineScriptsDir, "save_target.txt")
              let globalFile = Path.Combine(inlineScriptsDir, "save_global_target.txt")
              let planetFile = Path.Combine(inlineScriptsDir, "save_planet_target.txt")
              let eventText =
                  "namespace = inline_target_scope\n\
                   country_event = {\n\
                       id = inline_target_scope.1\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       immediate = {\n\
                           inline_script = {\n\
                               script = event_target_scope/save_target\n\
                               TARGET = inline_country_target\n\
                           }\n\
                           inline_script = {\n\
                               script = event_target_scope/save_global_target\n\
                               TARGET = inline_global_country_target\n\
                           }\n\
                           inline_script = {\n\
                               script = event_target_scope/save_planet_target\n\
                               TARGET = inline_planet_target\n\
                           }\n\
                           event_target:inline_country_target = {\n\
                               set_country_flag = inline_country_scope_marker\n\
                           }\n\
                           event_target:inline_global_country_target = {\n\
                               set_country_flag = inline_global_country_scope_marker\n\
                           }\n\
                           event_target:inline_planet_target = {\n\
                               set_planet_flag = inline_planet_scope_marker\n\
                           }\n\
                       }\n\
                   }"

              File.WriteAllText(eventFile, eventText)
              File.WriteAllText(directFile, "save_event_target_as = $TARGET$")
              File.WriteAllText(globalFile, "save_global_event_target_as = $TARGET$")
              File.WriteAllText(
                  planetFile,
                  "random_owned_planet = {\n\
                       inline_script = {\n\
                           script = event_target_scope/save_target\n\
                           TARGET = $TARGET$\n\
                       }\n\
                   }"
              )

              let posOf (needle: string) =
                  let marker = eventText.IndexOf(needle, System.StringComparison.Ordinal)
                  Expect.isGreaterThan marker -1 $"scope marker {needle} was not found"
                  let before = eventText.Substring(0, marker)
                  let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
                  let lastLineBreak = before.LastIndexOf('\n')
                  let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
                  mkPos line column

              try
                  let configText = configFilesFromDir (Path.Combine(stellarisConfigRoot.Value, "config"))

                  let settings =
                      { emptyStellarisSettings root with
                          rules =
                              Some
                                  { ruleFiles = configText
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>

                  let expectScope expected marker =
                      let context = stl.ScopesAtPos (posOf marker) eventFile eventText
                      Expect.isSome context $"{marker} should have a scope context"
                      Expect.equal
                          (context.Value.CurrentScope.ToString())
                          expected
                          $"{marker} should resolve through the inline-script event target"

                  expectScope "Country" "inline_country_scope_marker"
                  expectScope "Country" "inline_global_country_scope_marker"
                  expectScope "Planet" "inline_planet_scope_marker"
              finally
                  if Directory.Exists(root) then Directory.Delete(root, true)
          testWithCapturedLogs "embedded empty inline parameter preserves saved system target scope"
          <| fun () ->
              let root =
                  Path.Combine(Path.GetTempPath(), "cwtools-inline-system-target-scope-" + System.Guid.NewGuid().ToString("N"))

              let eventsDir = Path.Combine(root, "events")
              let inlineScriptsDir = Path.Combine(root, "common", "inline_scripts", "event_target_scope")
              Directory.CreateDirectory(eventsDir) |> ignore
              Directory.CreateDirectory(inlineScriptsDir) |> ignore
              let eventFile = Path.Combine(eventsDir, "inline_system_target_scope_events.txt")
              let inlineFile = Path.Combine(inlineScriptsDir, "system_target.txt")

              let eventText =
                  "namespace = inline_system_target_scope\n\
                   country_event = {\n\
                       id = inline_system_target_scope.pollution\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       immediate = { save_event_target_as = portal_system }\n\
                   }\n\
                   inline_script = {\n\
                       script = event_target_scope/system_target\n\
                       CURRENT = \"\"\n\
                   }\n\
                   namespace = inline_system_target_scope_2\n\
                   inline_script = {\n\
                       script = event_target_scope/system_target\n\
                       CURRENT = _2\n\
                   }\n\
                   namespace = inline_system_target_scope_3\n\
                   inline_script = {\n\
                       script = event_target_scope/system_target\n\
                       CURRENT = _3\n\
                   }"

              let inlineText =
                  "country_event = {\n\
                       id = inline_system_target_scope$CURRENT$.1\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       immediate = {\n\
                           random_system = {\n\
                               save_global_event_target_as = portal$CURRENT$_system\n\
                           }\n\
                           if = {\n\
                               limit = {\n\
                                   event_target:portal$CURRENT$_system = {\n\
                                       any_ship_in_system = { always = yes }\n\
                                   }\n\
                               }\n\
                           }\n\
                       }\n\
                   }"

              File.WriteAllText(eventFile, eventText)
              File.WriteAllText(inlineFile, inlineText)

              try
                  let configText = configFilesFromDir (Path.Combine(stellarisConfigRoot.Value, "config"))

                  let embedded = STLGameFunctions.createEmbeddedSettings [] [] configText None
                  let country = scopeManager.ParseScope () "Country"
                  let pollutedTargetLink =
                      ScopedEffect(
                          "event_target:portal_system",
                          scopeManager.AllScopes,
                          country,
                          EffectType.Link,
                          "Deliberately polluted flat target scope",
                          "",
                          true
                      )

                  let settings =
                      { emptyStellarisSettings root with
                          embedded =
                              ManualSettings
                                  { embedded with
                                      eventTargetLinks = SimpleLink pollutedTargetLink :: embedded.eventTargetLinks }
                          rules =
                              Some
                                  { ruleFiles = configText
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stlGame = STLGame(settings)
                  let stl = stlGame :> IGame<STLComputedData>

                  let portalScopes =
                      stlGame.Lookup.savedEventTargets
                      |> Seq.filter (fun (name, _, _) -> name = "portal_system")
                      |> Seq.map (fun (_, _, scope) -> scope.ToString())
                      |> Seq.distinct
                      |> Seq.sort
                      |> Seq.toList

                  Expect.equal
                      portalScopes
                      [ "Country"; "System" ]
                      $"the regression needs an ambiguous flat target index: %A{portalScopes}"

                  let wrongScopeErrors =
                      stl.ValidateFile false eventFile
                      |> List.filter (fun error ->
                          error.code = "CW274"
                          || (error.message.Contains("any_ship_in_system")
                              && error.message.Contains("Country")
                              && error.message.Contains("System")))

                  Expect.isEmpty
                      wrongScopeErrors
                      $"the expanded global target should retain its System save scope: %A{wrongScopeErrors}"
              finally
                  if Directory.Exists(root) then Directory.Delete(root, true)
          testWithCapturedLogs "expanded global target trusts concrete computed save scope"
          <| fun () ->
              let root =
                  Path.Combine(Path.GetTempPath(), "cwtools-inline-computed-save-scope-" + System.Guid.NewGuid().ToString("N"))

              let eventsDir = Path.Combine(root, "events")
              let inlineScriptsDir = Path.Combine(root, "common", "inline_scripts", "event_target_scope")
              Directory.CreateDirectory(eventsDir) |> ignore
              Directory.CreateDirectory(inlineScriptsDir) |> ignore
              let eventFile = Path.Combine(eventsDir, "inline_computed_save_scope_events.txt")
              let inlineFile = Path.Combine(inlineScriptsDir, "computed_save_scope.txt")

              File.WriteAllText(
                  eventFile,
                  "namespace = inline_computed_save_scope\n\
                   inline_script = { script = event_target_scope/computed_save_scope }"
              )

              File.WriteAllText(
                  inlineFile,
                  "country_event = {\n\
                       id = inline_computed_save_scope.1\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       immediate = {\n\
                           save_global_event_target_as = computed_system_target\n\
                           if = {\n\
                               limit = {\n\
                                   event_target:computed_system_target = {\n\
                                       any_ship_in_system = { always = yes }\n\
                                   }\n\
                               }\n\
                           }\n\
                       }\n\
                   }"
              )

              try
                  let configText = configFilesFromDir (Path.Combine(stellarisConfigRoot.Value, "config"))
                  let settings =
                      { emptyStellarisSettings root with
                          rules =
                              Some
                                  { ruleFiles = configText
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stlGame = STLGame(settings)
                  let stl = stlGame :> IGame<STLComputedData>
                  let system = scopeManager.ParseScope () "System"

                  // Reproduce the production split: the flat link and template
                  // positional context say Country, while ComputedData has already
                  // resolved this concrete save site to System.
                  stlGame.Lookup.savedEventTargets <-
                      ResizeArray(
                          stlGame.Lookup.savedEventTargets
                          |> Seq.map (fun (name, position, scope) ->
                              if name = "computed_system_target" then name, position, system
                              else name, position, scope)
                      )

                  let computedScopes =
                      stlGame.Lookup.savedEventTargets
                      |> Seq.filter (fun (name, _, _) -> name = "computed_system_target")
                      |> Seq.map (fun (_, _, scope) -> scope.ToString())
                      |> Seq.distinct
                      |> Seq.toList

                  Expect.equal computedScopes [ "System" ] "the concrete save record should be System"

                  let wrongScopeErrors =
                      stl.ValidateFile false eventFile
                      |> List.filter (fun error ->
                          error.code = "CW274"
                          || (error.message.Contains("any_ship_in_system")
                              && error.message.Contains("Country")
                              && error.message.Contains("System")))

                  Expect.isEmpty
                      wrongScopeErrors
                      $"expanded validation should use the computed save-site scope: %A{wrongScopeErrors}"
              finally
                  if Directory.Exists(root) then Directory.Delete(root, true)
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
                  $"call-site scan should substitute the global save parameter, got %A{saves}"
          testCase "validate clause with conditional parameter prefix matches actual rule"
          <| fun () ->
              let config =
                  "types = {\n\
                       type[scripted_trigger] = {\n\
                           path = \"game/common/scripted_triggers\"\n\
                       }\n\
                   }\n\
                   alias[trigger:distance] = {\n\
                       source = scope[any]\n\
                       type = scalar\n\
                       use_bypasses = bool\n\
                       min_distance = int\n\
                       max_distance = int\n\
                   }\n\
                   scripted_trigger = {\n\
                       alias_name[trigger] = alias_match_left[trigger]\n\
                   }\n"

              let input =
                  "my_trigger = {\n\
                       [[ag_distance_max]distance = {\n\
                           source = root\n\
                           type = euclidean\n\
                           use_bypasses = yes\n\
                           min_distance = 1\n\
                           max_distance = 5\n\
                       }\n\
                   }\n"

              UtilityParser.initializeScopes None None

              let rules, types, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "rules.cwt"
                      config

              match CKParser.parseString input "common/scripted_triggers/test.txt" with
              | Success(r, _, _) ->
                  let node =
                      STLProcess.shipProcess.ProcessNode () "root" range.Zero r

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

                  let errors = validationService.ManualRuleValidate("common/scripted_triggers/test.txt", node)
                  match errors with
                  | OK -> ()
                  | Invalid(_, es) -> failtest $"Expected no errors, but got %A{es}"
              | Failure(err, _, _) -> failwith err ]