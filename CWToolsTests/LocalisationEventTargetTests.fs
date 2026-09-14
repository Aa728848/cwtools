module LocalisationEventTargetTests

open TestHelpers

open Expecto
open System
open System.IO
open CWTools.Common
open CWTools.Games
open CWTools.Games.Files
open CWTools.Games.Stellaris

/// Regression for the reported false positive: a localisation chain that starts
/// with a saved event target (`[ForceSensitiveLeader.GetName]`) was reported as
/// an unknown command (CW226). The processed localisation is captured while
/// parsing, before the rules refresh builds the event-target index, so it kept a
/// stale LocNotFound for every saved target whose name did not match the
/// lowercase/underscore fallback heuristic.
let private withEventTargetWorkspace (eventText: string) (locText: string) (body: STLGame -> unit) =
    let root =
        Path.Combine(Path.GetTempPath(), "cwtools-loc-event-target-" + Guid.NewGuid().ToString("N"))

    Directory.CreateDirectory(Path.Combine(root, "events")) |> ignore
    Directory.CreateDirectory(Path.Combine(root, "localisation")) |> ignore
    File.WriteAllText(Path.Combine(root, "events", "repro_events.txt"), eventText)
    File.WriteAllText(Path.Combine(root, "localisation", "repro_l_english.yml"), locText)

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

        body (STLGame(settings))
    finally
        if Directory.Exists root then Directory.Delete(root, true)

let private pascalEventTarget =
    "namespace = repro\n\
     country_event = {\n\
         id = repro.430\n\
         hide_window = yes\n\
         is_triggered_only = yes\n\
         immediate = {\n\
             save_event_target_as = ForceSensitiveLeader\n\
         }\n\
     }\n"

let private commandErrorsFor (game: STLGame) (command: string) =
    (game :> IGame<STLComputedData>).LocalisationErrors(true, true)
    |> List.filter (fun error -> error.code = "CW226" && error.message.Contains command)

[<Tests>]
let localisationEventTargetTests =
    testList
        "localisation event targets"
        [ testCase "a saved event target prefix is accepted in localisation chains"
          <| fun () ->
              let locText =
                  "l_english:\n repro.430.desc:0 \"Opens to [ForceSensitiveLeader.GetClass] [ForceSensitiveLeader.GetName]\"\n repro.430.a:0 \"[ForceSensitiveLeader.GetName] is the first of many.\"\n"

              withEventTargetWorkspace pascalEventTarget locText (fun game ->
                  Expect.isTrue
                      (game.Lookup.savedEventTargets
                       |> Seq.exists (fun (name, _, _) -> name = "ForceSensitiveLeader"))
                      "the event target saved by the event must be indexed"

                  Expect.isEmpty
                      (commandErrorsFor game "ForceSensitiveLeader")
                      "a saved event target must not be reported as an unknown command")

          testCase "an unknown command after a saved event target is still reported"
          <| fun () ->
              let locText =
                  "l_english:\n repro.430.desc:0 \"Opens to [ForceSensitiveLeader.BogusCommand]\"\n"

              withEventTargetWorkspace pascalEventTarget locText (fun game ->
                  Expect.isNonEmpty
                      (commandErrorsFor game "BogusCommand")
                      "an unknown chained command must still be reported")

          testCase "an unresolvable PascalCase scope prefix still validates the following commands"
          <| fun () ->
              // Event targets saved by another mod or by vanilla data are outside the
              // workspace index, so the leading segment cannot be resolved. Reporting
              // it as an unknown command only because it is not snake_case made the
              // diagnostic depend on the author's naming style.
              let locText =
                  "l_english:\n repro.430.desc:0 \"Opens to [UnresolvedLeader.GetClass] [UnresolvedLeader.GetName]\"\n"

              withEventTargetWorkspace pascalEventTarget locText (fun game ->
                  Expect.isEmpty
                      (commandErrorsFor game "UnresolvedLeader")
                      "an unresolved scope prefix must not be reported as an unknown command")

          testCase "an unknown command after an unresolvable scope prefix is still reported"
          <| fun () ->
              let locText =
                  "l_english:\n repro.430.desc:0 \"Opens to [UnresolvedLeader.NotReal]\"\n"

              withEventTargetWorkspace pascalEventTarget locText (fun game ->
                  Expect.isNonEmpty
                      (commandErrorsFor game "NotReal")
                      "an unknown chained command after an unresolved prefix must still be reported")

          testCase "an unresolvable single segment command is still reported"
          <| fun () ->
              let locText =
                  "l_english:\n repro.430.desc:0 \"Opens to [UnresolvedLeader]\"\n"

              withEventTargetWorkspace pascalEventTarget locText (fun game ->
                  Expect.isNonEmpty
                      (commandErrorsFor game "UnresolvedLeader")
                      "a bare unknown segment must still be reported") ]
