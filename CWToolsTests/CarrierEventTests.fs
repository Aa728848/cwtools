module CarrierEventTests

open TestHelpers

open System
open System.IO
open System.Reflection
open CWTools.Common.STLConstants
open CWTools.Games
open CWTools.Games.Stellaris
open CWTools.Parser
open CWTools.Parser.CKPrinter
open CWTools.Parser.DocsParser
open CWTools.Utilities
open CWTools.Utilities.Position
open CWTools.Utilities.Utils
open CWTools
open CWTools.Validation
open Expecto
open Expecto.Logging
open Expecto.Logging.Message
open CWTools.Common
open CWTools.Process
open CWTools.Process.Localisation
open CWTools.Process.ProcessCore
open CWTools.Games.Files
open System.Threading
open System.Globalization
open System.Text
open FParsec
open LogCaptureTest
open MBrace.FsPickler



[<Tests>]
let carrierEventScopeValidationTests =
    testSequenced
    <| testList
        "carrier event scope validation"
        [ testWithCapturedLogs "carrier origins flow through events and common definitions" <| fun () ->
              let folder =
                  Path.Combine(Path.GetTempPath(), "cwtools-carrier-origins-" + Guid.NewGuid().ToString("N"))

              let writeFile (relativePath: string) (text: string) =
                  let path = Path.Combine(folder, relativePath)
                  Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
                  let text = text.TrimStart().Replace("\r\n", "\n")
                  File.WriteAllText(path, text)
                  path, text

              let posOf (needle: string) (text: string) =
                  let marker = text.IndexOf(needle, StringComparison.Ordinal)
                  Expect.isGreaterThan marker -1 $"scope marker {needle} was not found"
                  let before = text.Substring(0, marker)
                  let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
                  let lastLineBreak = before.LastIndexOf('\n')
                  let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
                  mkPos line column

              try
                  let eventPath, eventText =
                      writeFile
                          (Path.Combine("events", "carrier_origin_events.txt"))
                          """
                          namespace = carrier_origin

                          planet_event = {
                              id = carrier_origin.1
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = { carrier_event = { id = carrier_origin.10 } }
                          }

                          planet_event = {
                              id = carrier_origin.3
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = { carrier_event = { id = carrier_origin.50 } }
                          }

                          planet_event = {
                              id = carrier_origin.5
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  carrier = { set_carrier_flag = carrier_from_planet_marker }
                              }
                          }

                          situation_event = {
                              id = carrier_origin.8
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  target = {
                                      set_carrier_flag = situation_event_target_marker
                                      solar_system = {
                                          spawn_planet = {
                                              class = random
                                              location = target
                                          }
                                      }
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_origin.4
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  random_system = {
                                      random_system_planet = { carrier_event = { id = carrier_origin.12 } }
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_origin.7
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  enable_special_project = {
                                      name = carrier_union_project
                                      location = last_created_ambient_object
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_origin.70
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  country_event = {
                                      id = carrier_origin.71
                                      scopes = { from = from }
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_origin.71
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  from = { save_event_target_as = current_marauder_diplomacy }
                              }
                              trigger = {
                                  event_target:current_marauder_diplomacy = {
                                      has_country_flag = marauder_country_scope_marker
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_origin.72
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  save_event_target_as = locally_saved_planet
                                  owner_species = { save_event_target_as = current_marauder_diplomacy }
                              }
                          }

                          country_event = {
                              id = carrier_origin.73
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  random_owned_planet = {
                                      save_event_target_as = locally_saved_planet
                                  }
                                  event_target:locally_saved_planet = {
                                      set_planet_flag = local_planet_target_marker
                                  }
                                  event_target:locally_saved_planet.owner = {
                                      set_country_flag = local_planet_owner_marker
                                      prev = { set_country_flag = dotted_event_target_prev_marker }
                                  }
                                  event_target:locally_saved_planet = {
                                      owner = {
                                          prev = { set_planet_flag = nested_event_target_prev_marker }
                                      }
                                  }
                                  random_system = {
                                      random_system_planet = {
                                          save_event_target_as = prev_stack_planet
                                      }
                                      event_target:prev_stack_planet = {
                                          create_fleet = {
                                              effect = {
                                                  prevprev = { set_star_flag = saved_target_prev_stack_marker }
                                              }
                                          }
                                      }
                                  }
                                  event_target:the_end_of_the_cycle@$OWNER$ = {
                                      set_planet_flag = parameterized_target_marker
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_origin.80
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  random_owned_planet = {
                                      save_event_target_as = chained_planet_target
                                  }
                                  country_event = { id = carrier_origin.81 }
                              }
                          }

                          country_event = {
                              id = carrier_origin.81
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  event_target:chained_planet_target = {
                                      set_planet_flag = chained_planet_target_marker
                                      carrier_event = { id = carrier_origin.86 }
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_origin.82
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  save_event_target_as = chained_planet_target
                              }
                          }

                          country_event = {
                              id = carrier_origin.83
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  random_owned_planet = {
                                      save_global_event_target_as = global_planet_target
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_origin.84
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  event_target:global_planet_target = {
                                      set_planet_flag = global_planet_target_marker
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_origin.85
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  save_event_target_as = global_planet_target
                                  event_target:global_planet_target = {
                                      set_country_flag = local_target_overrides_global_marker
                                  }
                              }
                          }

                          carrier_event = {
                              id = carrier_origin.86
                              hide_window = yes
                              is_triggered_only = yes
                          }

                          country_event = {
                              id = carrier_origin.74
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  from = {
                                      from = {
                                          from = {
                                              set_fleet_flag = nested_fromfromfrom_fleet_marker
                                          }
                                      }
                                      fromfrom = {
                                          set_fleet_flag = mixed_fromfromfrom_fleet_marker
                                      }
                                  }
                                  from.fromfrom = {
                                      set_fleet_flag = dotted_fromfromfrom_fleet_marker
                                  }
                                  fromfrom = {
                                      root = {
                                          from = {
                                              set_country_flag = nested_root_from_reset_marker
                                          }
                                      }
                                  }
                                  fromfrom.root.from = {
                                      set_country_flag = dotted_root_from_reset_marker
                                  }
                                  fromfromfrom = {
                                      set_fleet_flag = direct_fromfromfrom_fleet_marker
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_origin.75
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  fromfromfrom.from = {
                                      set_war_flag = three_plus_one_from_marker
                                  }
                                  from.from.from.from = {
                                      set_war_flag = four_dotted_from_marker
                                  }
                                  fromfromfromfrom = {
                                      set_war_flag = legacy_four_joined_from_marker
                                  }
                                  country_event = {
                                      id = carrier_origin.76
                                      scopes = {
                                          from = from
                                          fromfrom = fromfromfromfrom
                                      }
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_origin.76
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  fromfrom = {
                                      every_war_participant = {
                                          fromfrom = {
                                              set_war_flag = iterator_from_cursor_reset_marker
                                              every_war_participant = {
                                                  set_country_flag = nested_war_participant_marker
                                              }
                                          }
                                      }
                                  }
                                  from = {
                                      capital_scope = {
                                          prev = {
                                              from = {
                                                  set_war_flag = prev_restores_from_cursor_marker
                                              }
                                          }
                                      }
                                  }
                              }
                          }

                          carrier_event = {
                              id = carrier_origin.10
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  set_carrier_flag = planet_chain_marker
                                  carrier_event = { id = carrier_origin.11 }
                              }
                          }

                          carrier_event = {
                              id = carrier_origin.11
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = { set_carrier_flag = transitive_planet_marker }
                          }

                          carrier_event = {
                              id = carrier_origin.12
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = { set_planet_flag = iterator_planet_marker }
                          }

                          ship_event = {
                              id = carrier_origin.2
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = { carrier_event = { id = carrier_origin.20 } }
                          }

                          ship_event = {
                              id = carrier_origin.6
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  carrier = { set_carrier_flag = carrier_from_ship_marker }
                              }
                          }

                          ship_event = {
                              id = carrier_origin.61
                              hide_window = yes
                              is_triggered_only = yes
                          }

                          planet_event = {
                              id = carrier_origin.62
                              hide_window = yes
                              is_triggered_only = yes
                          }

                          carrier_event = {
                              id = carrier_origin.20
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = { set_carrier_flag = ship_chain_marker }
                          }

                          carrier_event = {
                              id = carrier_origin.30
                              hide_window = yes
                              is_triggered_only = yes
                              trigger = { has_carrier_flag = missing_carrier_flag_warning_marker }
                              immediate = {
                                  remove_carrier_flag = missing_removed_carrier_flag_warning_marker
                                  owner? = {
                                      abort_special_project = {
                                          type = carrier_location_project
                                          location = root
                                      }
                                  }
                                  if = {
                                      limit = { carrier_is_type = planet }
                                      set_carrier_flag = narrowed_branch_marker
                                  }
                                  solar_system = {
                                      inline_script = {
                                          script = cosmic_storms/SpawnAtPosition
                                          TYPE = electric_storm
                                      }
                                  }
                              }
                          }

                          carrier_event = {
                              id = carrier_origin.40
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = { set_carrier_flag = planet_on_action_marker }
                          }

                          carrier_event = {
                              id = carrier_origin.41
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  set_carrier_flag = colony_on_action_marker
                                  carrier_from_target_effect = {
                                      GLOBAL_TARGET = carrier_from_country_target
                                  }
                                  event_target:carrier_from_country_target = {
                                      has_country_flag = propagated_from_target_marker
                                  }
                              }
                          }

                          carrier_event = {
                              id = carrier_origin.50
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  set_carrier_flag = explicit_scope_source_marker
                                  carrier_event = {
                                      id = carrier_origin.51
                                      scopes = { from = owner fromfrom = from }
                                  }
                              }
                          }

                          carrier_event = {
                              id = carrier_origin.51
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = { set_carrier_flag = explicit_scope_target_marker }
                          }

                          carrier_event = {
                              id = carrier_origin.60
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  carrier_completion_marker = yes
                                  enable_special_project = {
                                      name = carrier_location_project
                                      location = this
                                  }
                              }
                          }
                          """

                  let projectPath, projectText =
                      writeFile
                          (Path.Combine("common", "special_projects", "carrier_origin_projects.txt"))
                          """
                          special_project = {
                              key = carrier_origin_project
                              cost = 1
                              event_scope = carrier_event
                              on_success = {
                                  set_carrier_flag = project_callback_marker
                                  prev = { set_country_flag = project_prev_marker }
                              }
                              on_fail = { set_country_flag = project_fail_marker }
                          }

                          special_project = {
                              key = carrier_location_project
                              cost = 1
                          }

                          special_project = {
                              key = carrier_union_project
                              cost = 0
                              event_scope = carrier_event
                              on_success = {
                                  ship_event = { id = carrier_origin.61 }
                                  planet_event = { id = carrier_origin.62 }
                              }
                          }

                          special_project = {
                              key = carrier_dynamic_project
                              cost = 1
                              event_scope = ship_event
                              on_fail = {
                                  from = {
                                      from = {
                                          set_planet_flag = special_project_relative_from_marker
                                      }
                                  }
                              }
                          }

                          special_project = {
                              key = country_created_planet_project
                              cost = 1
                              event_scope = planet_event
                              on_success = {
                                  from = { set_country_flag = country_project_creation_scope_marker }
                              }
                          }
                          """

                  let situationPath, situationText =
                      writeFile
                          (Path.Combine("common", "situations", "carrier_origin_situations.txt"))
                          """
                          carrier_origin_situation = {
                              on_start = {
                                  target = { set_carrier_flag = situation_target_marker }
                                  situation_event = { id = carrier_origin.8 }
                              }
                          }

                          carrier_country_target_situation = {
                              on_start = {
                                  target = { set_country_flag = country_situation_target_marker }
                              }
                              monthly_progress = {
                                  base = 0
                                  modifier = {
                                      add = 1
                                      target = { has_country_flag = country_modifier_target_marker }
                                  }
                              }
                          }
                          """

                  let commonCallerPath, commonCallerText =
                      writeFile
                          (Path.Combine("events", "carrier_origin_common_callers.txt"))
                          """
                          namespace = carrier_common

                          planet_event = {
                              id = carrier_common.1
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  enable_special_project = {
                                      name = carrier_origin_project
                                      location = this
                                  }
                                  enable_special_project = {
                                      name = carrier_dynamic_project
                                      location = this
                                  }
                                  start_situation = {
                                      type = carrier_origin_situation
                                      target = this
                                  }
                              }
                          }

                          country_event = {
                              id = carrier_common.2
                              hide_window = yes
                              is_triggered_only = yes
                              immediate = {
                                  enable_special_project = {
                                      name = country_created_planet_project
                                      location = this.capital_star
                                  }
                                  start_situation = {
                                      type = carrier_origin_situation
                                      target = this.capital_star
                                  }
                                  start_situation = {
                                      type = carrier_country_target_situation
                                      target = this
                                  }
                              }
                          }
                          """

                  let scriptedEffectPath, scriptedEffectText =
                      writeFile
                          (Path.Combine("common", "scripted_effects", "carrier_origin_effects.txt"))
                          """
                          carrier_from_target_effect = {
                              if = {
                                  limit = {
                                      exists = event_target:$GLOBAL_TARGET$
                                  }
                                  event_target:$GLOBAL_TARGET$ = {
                                      has_country_flag = scripted_from_target_country_marker
                                  }
                              }
                              from = {
                                  save_global_event_target_as = $GLOBAL_TARGET$
                              }
                          }
                          """

                  let gameRulePath, gameRuleText =
                      writeFile
                          (Path.Combine("common", "game_rules", "carrier_origin_game_rules.txt"))
                          """
                          can_orbital_bombard = {
                              exists = from.owner
                              NOR = {
                                  any_controlled_ship = { is_ship_size = colossus }
                              }
                          }
                          """

                  let buildingPath, buildingText =
                      writeFile
                          (Path.Combine("common", "buildings", "carrier_origin_buildings.txt"))
                          """
                          carrier_origin_building = {
                              allow = {
                                  carrier = {
                                      has_carrier_flag = building_colony_carrier_marker
                                      fleet = { has_fleet_flag = building_carrier_fleet_marker }
                                  }
                              }
                          }
                          """

                  let megastructurePath, megastructureText =
                      writeFile
                          (Path.Combine("common", "megastructures", "carrier_origin_megastructures.txt"))
                          """
                          carrier_origin_megastructure = {
                              on_build_complete = {
                                  from = {
                                      fromfrom = {
                                          set_megastructure_flag = fixed_nested_fromfrom_marker
                                      }
                                  }
                                  from.fromfrom = {
                                      set_megastructure_flag = fixed_dotted_fromfrom_marker
                                  }
                              }
                          }
                          """

                  let _, _ =
                      writeFile
                          (Path.Combine("common", "storm_types", "electric_storm.txt"))
                          """
                          electric_storm = { }
                          """

                  let _, _ =
                      writeFile
                          (Path.Combine("common", "inline_scripts", "cosmic_storms", "SpawnAtPosition.txt"))
                          """
                          create_cosmic_storm = {
                              type = $TYPE$
                              cosmic_storm_start_position = prev
                          }
                          """

                  let onActionPath, onActionText =
                      writeFile
                          (Path.Combine("common", "on_actions", "carrier_origin_on_actions.txt"))
                          """
                          on_colonization_started = {
                              events = { carrier_origin.40 }
                          }
                          on_initialize_advanced_colony = {
                              random_events = { 100 = carrier_origin.41 }
                          }
                          on_custom_diplomacy = {
                              events = { carrier_origin.70 }
                          }
                          on_space_battle_over = {
                              events = { carrier_origin.74 }
                          }
                          on_status_quo = {
                              events = { carrier_origin.75 }
                          }
                          """

                  let docsPath = (Path.Combine(stellarisConfigRoot.Value, "config", "logs", "trigger_docs.log"))
                  let configtext =
                      (docsPath, File.ReadAllText docsPath)
                      :: configFilesFromDir stellarisConfigRoot.Value

                  let settings =
                      { emptyStellarisSettings folder with
                          rules =
                              Some
                                  { ruleFiles = configtext
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stlGame = STLGame(settings)
                  let stl = stlGame :> IGame<STLComputedData>

                  let completionNeedle = "carrier_completion_marker = yes"
                  let completionCursor = posOf completionNeedle eventText
                  let completionText = eventText.Replace(completionNeedle, "")
                  let completionContext = stl.ScopesAtPos completionCursor eventPath completionText
                  Expect.isSome completionContext "carrier_event completion should have a scope context"
                  Expect.isNonEmpty completionContext.Value.Scopes "carrier_event should expose its current scope"
                  Expect.equal
                      (completionContext.Value.Scopes.Head.ToString())
                      "Carrier"
                      "an unresolved carrier_event should retain the synthetic Carrier union"

                  let completions =
                      stl.Complete completionCursor eventPath completionText
                      |> List.map (function
                          | CompletionResponse.Simple(label, score, _) -> label, score
                          | CompletionResponse.Detailed(label, _, score, _) -> label, score
                          | CompletionResponse.Snippet(label, _, _, score, _) -> label, score)

                  let labels = completions |> List.map fst
                  let scoreFor name =
                      completions
                      |> List.tryPick (fun (label, score) -> if label = name then score else None)
                      |> Option.defaultValue -1

                  Expect.contains labels "set_carrier_flag" "carrier-aware effects should complete in carrier_event"
                  Expect.isGreaterThan
                      (scoreFor "set_carrier_flag")
                      20
                      "carrier-aware effects should receive an in-scope completion score"
                  Expect.contains labels "set_planet_flag" "fixture should expose the planet-only effect"
                  Expect.isGreaterThan
                      (scoreFor "set_planet_flag")
                      20
                      "the Carrier union should admit planet-supported effects"
                  Expect.contains labels "set_ship_flag" "fixture should expose the ship-only effect"
                  Expect.isGreaterThan
                      (scoreFor "set_ship_flag")
                      20
                      "the Carrier union should admit ship-supported effects"

                  let expectScope expected needle path text message =
                      let context = stl.ScopesAtPos (posOf needle text) path text
                      Expect.isSome context message
                      Expect.isNonEmpty context.Value.Scopes message
                      Expect.equal (context.Value.Scopes.Head.ToString()) expected message

                  let expectFromScopes expected needle path text message =
                      let context = stl.ScopesAtPos (posOf needle text) path text
                      Expect.isSome context message
                      Expect.equal
                          (context.Value.From |> List.map string)
                          expected
                          message

                  let expectRoot expected needle path text message =
                      let context = stl.ScopesAtPos (posOf needle text) path text
                      Expect.isSome context message
                      Expect.equal (context.Value.Root.ToString()) expected message

                  let expectFromDepth expected needle path text message =
                      let context = stl.ScopesAtPos (posOf needle text) path text
                      Expect.isSome context message
                      Expect.equal context.Value.FromDepth expected message

                  let bombardContext =
                      stl.ScopesAtPos (posOf "NOR =" gameRuleText) gameRulePath gameRuleText
                      |> Option.get

                  Expect.equal (bombardContext.CurrentScope.ToString()) "Fleet" "game_rule THIS should default to ROOT"
                  Expect.equal (bombardContext.Root.ToString()) "Fleet" "can_orbital_bombard ROOT should be Fleet"
                  Expect.equal
                      (bombardContext.From |> List.map string)
                      [ "Planet" ]
                      "can_orbital_bombard FROM should be Planet"

                  let controlledShipContext =
                      stl.ScopesAtPos (posOf "is_ship_size" gameRuleText) gameRulePath gameRuleText
                      |> Option.get

                  Expect.equal
                      (controlledShipContext.CurrentScope.ToString())
                      "Ship"
                      "any_controlled_ship should push each matched Ship"
                  Expect.equal
                      (controlledShipContext.Root.ToString())
                      "Fleet"
                      "scope iteration should preserve the game_rule Fleet ROOT"

                  let validationErrors = stl.ValidationErrors()

                  [ "missing_carrier_flag_warning_marker"
                    "missing_removed_carrier_flag_warning_marker" ]
                  |> List.iter (fun marker ->
                      let missingCarrierFlagDiagnostics =
                          validationErrors
                          |> List.filter (fun error -> error.code = "CW240" && error.message.Contains(marker))

                      Expect.isNonEmpty
                          missingCarrierFlagDiagnostics
                          $"an undefined carrier_flag reference should still report CW240 for {marker}"

                      missingCarrierFlagDiagnostics
                      |> List.iter (fun error ->
                          Expect.equal
                              error.severity
                              Severity.Warning
                              $"an undefined carrier_flag reference should be a warning for {marker}"))

                  let scopeDiagnostics =
                      validationErrors
                      |> List.filter (fun error ->
                          let isIn path =
                              String.Equals(
                                  Path.GetFullPath(error.range.FileName),
                                  Path.GetFullPath(path),
                                  StringComparison.OrdinalIgnoreCase
                              )

                          ((error.code = "CW243" || error.code = "CW245")
                           && [ eventPath
                                projectPath
                                commonCallerPath
                                gameRulePath
                                situationPath
                                buildingPath
                                megastructurePath
                                scriptedEffectPath ]
                              |> List.exists isIn)
                          || (error.code = "CW247" && [ projectPath; megastructurePath ] |> List.exists isIn)
                          || (error.code = "CW274" && isIn eventPath))

                  Expect.isEmpty
                      scopeDiagnostics
                      $"Carrier-aware fixtures should not report scope diagnostics: %A{scopeDiagnostics |> List.collect (fun e -> e.message :: (e.relatedErrors |> Option.defaultValue [] |> List.map _.message))}"

                  let parameterizedTargetCardinalityDiagnostics =
                      validationErrors
                      |> List.filter (fun error ->
                          error.code = "CW242"
                          && error.message.Contains("scripted_effect_params", StringComparison.Ordinal)
                          && String.Equals(
                              Path.GetFullPath(error.range.FileName),
                              Path.GetFullPath(eventPath),
                              StringComparison.OrdinalIgnoreCase
                          ))

                  Expect.isEmpty
                      parameterizedTargetCardinalityDiagnostics
                      "a parameterized event-target key must not require call-site scripted-effect parameters"

                  expectScope
                      "Carrier"
                      "building_colony_carrier_marker"
                      buildingPath
                      buildingText
                      "a building's Colony carrier should remain the Planet-or-Ship union"
                  expectFromDepth
                      3
                      "nested_fromfromfrom_fleet_marker"
                      eventPath
                      eventText
                      "three nested FROM switches should advance three positions in the on_action FROM chain"
                  expectScope
                      "Fleet"
                      "building_carrier_fleet_marker"
                      buildingPath
                      buildingText
                      "the Carrier union should accept a fleet link supported by Ship"
                  expectScope
                      "Megastructure"
                      "fixed_nested_fromfrom_marker"
                      megastructurePath
                      megastructureText
                      "a nested FROMFROM in an object callback should use its fixed named slot"
                  expectScope
                      "Megastructure"
                      "fixed_dotted_fromfrom_marker"
                      megastructurePath
                      megastructureText
                      "a dotted FROM.FROMFROM path should use the same fixed callback slot"
                  expectScope "Any" "carrier_from_planet_marker" eventPath eventText "Planet.carrier should resolve to Any"
                  expectScope "Any" "carrier_from_ship_marker" eventPath eventText "Ship.carrier should resolve to Any"
                  expectScope
                      "Planet"
                      "situation_event_target_marker"
                      eventPath
                      eventText
                      "a situation_event target should inherit the creating situation's target scope"

                  expectScope
                      "Carrier"
                      "carrier_origin.61"
                      projectPath
                      projectText
                      "carrier-scoped special-project on_success should keep THIS as the Planet-or-Ship union"
                  expectScope
                      "Carrier"
                      "carrier_origin.62"
                      projectPath
                      projectText
                      "Carrier on_success should allow both Ship and Planet event calls"
                  expectFromScopes
                      [ "Country" ]
                      "carrier_origin.61"
                      projectPath
                      projectText
                      "special-project enabling scope should remain FROM without replacing Carrier THIS"

                  expectScope "Planet" "planet_chain_marker" eventPath eventText "planet callers should narrow carrier_event"
                  let planetPos = posOf "planet_chain_marker" eventText
                  let planetContext = stl.ScopesAtPos planetPos eventPath eventText |> Option.get
                  let inference =
                      (stl :?> IScopeInferenceProvider).ScopeInferenceAtPos planetPos eventPath eventText planetContext
                  Expect.isSome inference "query_scope should expose Carrier host provenance"
                  Expect.equal inference.Value.certainty "exact" "a unique Planet caller should be reported as exact"
                  Expect.contains inference.Value.candidates "Planet" "Carrier provenance should list Planet as a candidate"
                  Expect.contains inference.Value.candidates "Ship" "Carrier provenance should list Ship as a candidate"
                  Expect.isTrue
                      (inference.Value.evidence |> List.exists (fun item -> item.Contains("Planet caller", StringComparison.Ordinal)))
                      "Carrier provenance should cite the caller that narrowed the event"
                  expectFromScopes [ "Planet" ] "planet_chain_marker" eventPath eventText "direct event calls should seed FROM"
                  expectScope "Planet" "transitive_planet_marker" eventPath eventText "carrier_event chains should retain their origin"
                  expectFromScopes
                      [ "Planet"; "Planet" ]
                      "transitive_planet_marker"
                      eventPath
                      eventText
                      "carrier_event chains should advance FROM and FROMFROM"
                  expectScope
                      "Planet"
                      "iterator_planet_marker"
                      eventPath
                      eventText
                      "scope-changing iterators should narrow carrier_event callers"
                  expectFromScopes
                      [ "Country" ]
                      "iterator_planet_marker"
                      eventPath
                      eventText
                      "event calls inside iterators should default FROM to the firing event ROOT"
                  expectScope "Ship" "ship_chain_marker" eventPath eventText "ship callers should narrow carrier_event"
                  expectFromScopes [ "Ship" ] "ship_chain_marker" eventPath eventText "ship event calls should seed a Ship FROM"
                  expectScope "Planet" "narrowed_branch_marker" eventPath eventText "carrier_is_type should narrow its guarded branch"
                  expectScope "Planet" "planet_on_action_marker" eventPath eventText "planet on_actions should seed carrier_event"
                  expectScope "Carrier" "colony_on_action_marker" eventPath eventText "colony on_actions should preserve the planet-or-ship union"
                  expectFromScopes
                      [ "Country" ]
                      "colony_on_action_marker"
                      eventPath
                      eventText
                      "on_action replace_scope should seed the carrier event FROM chain"
                  expectScope
                      "Any"
                      "save_global_event_target_as"
                      scriptedEffectPath
                      scriptedEffectText
                      "an unbound scripted-effect FROM should remain unresolved in the standalone definition"
                  expectFromDepth
                      1
                      "save_global_event_target_as"
                      scriptedEffectPath
                      scriptedEffectText
                      "the standalone scripted-effect definition should preserve its relative FROM depth"
                  let propagatedTargetScopes =
                      stlGame.Lookup.savedEventTargets
                      |> Seq.choose (fun (name, _, scope) ->
                          if name == "carrier_from_country_target" then Some(scope.ToString()) else None)
                      |> Set.ofSeq

                  let propagatedTargetEvidence =
                      stlGame.Lookup.savedEventTargets
                      |> Seq.choose (fun (name, position, scope) ->
                          if name == "carrier_from_country_target" then
                              Some(scope.ToString(), position.FileName, position.StartLine)
                          else
                              None)
                      |> Seq.toList

                  Expect.equal
                      propagatedTargetScopes
                      (Set.singleton "Country")
                      $"scripted-effect expansion should register only the call-site FROM scope for the parameterized target: %A{propagatedTargetEvidence}"
                  expectScope
                      "Country"
                      "propagated_from_target_marker"
                      eventPath
                      eventText
                      "a parameterized target saved from a Carrier caller's FROM should retain the Country scope"
                  let marauderContext =
                      stl.ScopesAtPos (posOf "marauder_country_scope_marker" eventText) eventPath eventText

                  Expect.isSome marauderContext "the event-local saved target should have a scope context"
                  Expect.equal
                      (marauderContext.Value.CurrentScope.ToString())
                      "Country"
                      "on_action FROM should flow through scopes.from and resolve the local target as Country"
                  Expect.isNonEmpty marauderContext.Value.From "the called country event should inherit a FROM chain"
                  Expect.equal
                      (marauderContext.Value.From.Head.ToString())
                      "Country"
                      "the called event's immediate FROM should be the on_action source country"
                  expectScope
                      "Planet"
                      "local_planet_target_marker"
                      eventPath
                      eventText
                      "rule-driven iterators should retain their saved target scope"
                  expectScope
                      "Country"
                      "local_planet_owner_marker"
                      eventPath
                      eventText
                      "event-local target fallback should not replace a target chain's final scope"
                  expectScope
                      "Country"
                      "dotted_event_target_prev_marker"
                      eventPath
                      eventText
                      "a dotted event-target path should expose only the outer scope through PREV"
                  expectScope
                      "Planet"
                      "nested_event_target_prev_marker"
                      eventPath
                      eventText
                      "equivalent nested scope blocks should retain their intermediate PREV frame"
                  expectScope
                      "Planet"
                      "chained_planet_target_marker"
                      eventPath
                      eventText
                      "non-global event targets should propagate only along their event call chain"
                  expectScope
                      "Planet"
                      "global_planet_target_marker"
                      eventPath
                      eventText
                      "global event targets should remain available outside the event call chain"
                  expectScope
                      "Country"
                      "local_target_overrides_global_marker"
                      eventPath
                      eventText
                      "a local event target should override the same global target name in its event chain"
                  expectScope
                      "Fleet"
                      "nested_fromfromfrom_fleet_marker"
                      eventPath
                      eventText
                      "three nested FROM switches should resolve the on_action FROMFROMFROM fleet"
                  expectScope
                      "Fleet"
                      "direct_fromfromfrom_fleet_marker"
                      eventPath
                      eventText
                      "direct FROMFROMFROM should resolve to the same on_action fleet scope"
                  expectScope
                      "Fleet"
                      "mixed_fromfromfrom_fleet_marker"
                      eventPath
                      eventText
                      "nested FROM then FROMFROM should equal FROMFROMFROM"
                  expectScope
                      "Fleet"
                      "dotted_fromfromfrom_fleet_marker"
                      eventPath
                      eventText
                      "FROM.FROMFROM should equal the corresponding nested scope blocks"
                  expectScope
                      "Country"
                      "nested_root_from_reset_marker"
                      eventPath
                      eventText
                      "ROOT should reset the FROM path before a nested FROM switch"
                  expectScope
                      "Country"
                      "dotted_root_from_reset_marker"
                      eventPath
                      eventText
                      "FROMFROM.ROOT.FROM should resolve the event root's first FROM"
                  expectScope
                      "War"
                      "three_plus_one_from_marker"
                      eventPath
                      eventText
                      "FROMFROMFROM.FROM should resolve the fourth source"
                  expectScope
                      "War"
                      "four_dotted_from_marker"
                      eventPath
                      eventText
                      "four dotted FROM links should resolve the fourth source"
                  expectScope
                      "War"
                      "legacy_four_joined_from_marker"
                      eventPath
                      eventText
                      "the four-joined FROM spelling used by vanilla should remain compatible"
                  expectScope
                      "War"
                      "iterator_from_cursor_reset_marker"
                      eventPath
                      eventText
                      "a non-FROM iterator should start a new FROM cursor while preserving the event slots"
                  expectScope
                      "War"
                      "prev_restores_from_cursor_marker"
                      eventPath
                      eventText
                      "PREV should restore the FROM cursor belonging to the previous scope frame"
                  expectScope "Planet" "explicit_scope_target_marker" eventPath eventText "explicit event scopes should retain the proven Carrier host"
                  expectFromScopes
                      [ "Country"; "Planet" ]
                      "explicit_scope_target_marker"
                      eventPath
                      eventText
                      "carrier_event scopes should remap FROM and FROMFROM in the caller context"
                  expectScope "Planet" "project_callback_marker" projectPath projectText "special project location should narrow carrier callbacks"
                  expectRoot
                      "Planet"
                      "project_callback_marker"
                      projectPath
                      projectText
                      "successful special-project callbacks should use the event scope as ROOT"
                  expectFromScopes
                      [ "Planet" ]
                      "project_callback_marker"
                      projectPath
                      projectText
                      "special project callbacks should use the project location as FROM"
                  expectScope
                      "Country"
                      "country_project_creation_scope_marker"
                      projectPath
                      projectText
                      "special-project FROM should use the enabling scope rather than its separate location"
                  expectScope
                      "Country"
                      "project_prev_marker"
                      projectPath
                      projectText
                      "successful special project callbacks should expose the owner country as PREV"
                  expectScope "Country" "project_fail_marker" projectPath projectText "special project failure callbacks should use the owner country"
                  expectRoot
                      "Country"
                      "project_fail_marker"
                      projectPath
                      projectText
                      "failed special-project callbacks should use the project owner as ROOT"
                  expectFromScopes
                      [ "Planet"; "Planet" ]
                      "project_fail_marker"
                      projectPath
                      projectText
                      "special project failure callbacks should preserve project scope and creation scope as FROM/FROMFROM"
                  expectScope
                      "Planet"
                      "special_project_relative_from_marker"
                      projectPath
                      projectText
                      "special-project callbacks should keep runtime FROM paths relative"
                  expectFromDepth
                      2
                      "special_project_relative_from_marker"
                      projectPath
                      projectText
                      "two nested FROM switches in a special-project callback should advance two runtime positions"
                  expectScope "Planet" "situation_target_marker" situationPath situationText "situation targets should use start_situation target provenance"
                  expectScope
                      "Country"
                      "country_situation_target_marker"
                      situationPath
                      situationText
                      "start_situation target = this should retain the caller's Country scope"
                  expectScope
                      "Country"
                      "country_modifier_target_marker"
                      situationPath
                      situationText
                      "monthly_progress target should resolve the Situation's proven Country target"
              finally
                  if Directory.Exists folder then
                      Directory.Delete(folder, true) ]

