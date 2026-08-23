module OnActionTests

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
let onActionLivenessTests =
    testWithCapturedLogs "on_action liveness unless_subtyped"
    <| fun () ->
        let configtext =
            "types = {\n\
                type[on_action] = {\n\
                    path = \"game/common/on_actions\"\n\
                    should_be_used = unless_subtyped\n\
                    ## type_key_filter = on_game_start\n\
                    subtype[on_game_start] = { }\n\
                    ## starts_with = on_destroy_planet_with_\n\
                    subtype[dynamic_planet_killer] = { }\n\
                }\n\
                type[country_event] = {\n\
                    path = \"game/events\"\n\
                    name_field = \"id\"\n\
                }\n\
            }\n\
            on_action = {\n\
                ## cardinality = 0..1\n\
                events = {\n\
                    ## cardinality = 0..inf\n\
                    <country_event>\n\
                }\n\
            }\n\
            country_event = {\n\
                ## cardinality = 0..1\n\
                id = scalar\n\
                ## cardinality = 0..1\n\
                immediate = {\n\
                    ## cardinality = 0..inf\n\
                    alias_name[effect] = alias_match_left[effect]\n\
                }\n\
            }\n\
            alias[effect:fire_on_action] = {\n\
                ## severity = warning\n\
                on_action = <on_action>\n\
            }\n"

        let settings = emptyStellarisSettings "./testfiles/onactiontests/gamefiles"

        let settings =
            { settings with
                rules =
                    Some
                        { ruleFiles = [ "test.cwt", configtext ]
                          validateRules = true
                          debugRulesOnly = false
                          debugMode = false } }

        let stl = STLGame(settings) :> IGame<STLComputedData>

        let unusedErrors =
            stl.ValidationErrors() |> List.filter (fun e -> e.code = "CW239")

        Expect.equal
            unusedErrors.Length
            1
            $"Expected exactly one unused on_action (on_test_unused): %A{unusedErrors |> List.map (fun e -> e.message)}"

        let error = unusedErrors |> List.head
        Expect.stringContains error.message "on_test_unused" "The unused on_action should be on_test_unused"
        Expect.equal error.severity Severity.Information "unless_subtyped liveness should be information severity"

        // The editor's incremental path (didChange -> UpdateFile) must also surface it
        let updatePath =
            Path.GetFullPath "./testfiles/onactiontests/gamefiles/common/on_actions/test_actions.txt"

        // Populate the legacy deep cache first; an editor validation must not
        // carry those old global diagnostics into the new document version.
        stl.UpdateFile false updatePath None |> ignore

        let text =
            File.ReadAllText(updatePath)
            + "\non_test_interactive = { invalid_interactive_key = yes }\n"

        let entityBeforePrepare =
            stl.AllEntities()
            |> Seq.find (fun struct (entity, _) -> entity.filepath = updatePath)
            |> fun struct (entity, _) -> entity

        let stagedInteractive = stl.PrepareUpdateFileInteractive updatePath (Some text)

        let entityAfterPrepare =
            stl.AllEntities()
            |> Seq.find (fun struct (entity, _) -> entity.filepath = updatePath)
            |> fun struct (entity, _) -> entity

        Expect.isTrue
            (Object.ReferenceEquals(entityBeforePrepare, entityAfterPrepare))
            "Preparing an editor update must not mutate the live resource map"

        let detachedErrors = stl.ValidateFileInteractive stagedInteractive

        let entityAfterDetachedValidation =
            stl.AllEntities()
            |> Seq.find (fun struct (entity, _) -> entity.filepath = updatePath)
            |> fun struct (entity, _) -> entity

        Expect.isTrue
            (Object.ReferenceEquals(entityBeforePrepare, entityAfterDetachedValidation))
            "Validating a prepared update must not mutate the live resource map"
        Expect.isTrue
            (detachedErrors |> List.exists (fun e -> e.message.Contains "invalid_interactive_key"))
            $"Detached validation should report current-entity CWT errors: %A{detachedErrors |> List.map _.message}"

        Expect.isTrue
            (stl.CommitUpdateFileInteractive stagedInteractive)
            "Prepared editor update should commit"

        let interactiveErrors = stl.ValidateFileInteractive stagedInteractive

        Expect.isEmpty
            (interactiveErrors |> List.filter (fun e -> e.code = "CW239"))
            "Interactive updates should defer old/global lookup diagnostics until the normal validation pass"
        Expect.isTrue
            (interactiveErrors |> List.exists (fun e -> e.message.Contains "invalid_interactive_key"))
            $"Interactive updates should still report current-entity CWT errors: %A{interactiveErrors |> List.map _.message}"

        let compatibilityErrors = stl.UpdateFileInteractive updatePath (Some text)
        Expect.isTrue
            (compatibilityErrors |> List.exists (fun e -> e.message.Contains "invalid_interactive_key"))
            "The compatibility UpdateFileInteractive wrapper should preserve detached validation"

        let updateErrors =
            stl.UpdateFile true updatePath None
            |> List.filter (fun e -> e.code = "CW239")

        Expect.isEmpty
            updateErrors
            "UpdateFile should defer unused-type diagnostics to the global validation domain"

        let globalErrors =
            stl.ValidateFiles [updatePath]
            |> List.filter (fun e -> e.code = "CW239")

        Expect.equal
            globalErrors.Length
            1
            $"Global validation should report the unused on_action: %A{globalErrors |> List.map (fun e -> e.message)}"

[<Tests>]
let dynamicPlanetKillerOnActionTests =
    let writeFile (path: string) (text: string) =
        Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
        File.WriteAllText(path, text.TrimStart().Replace("\r\n", "\n"))

    testSequenced
    <| testList
        "dynamic planet killer on_actions"
        [ testWithCapturedLogs "planet killer component keys generate on_action keys" <| fun () ->
              let folder =
                  Path.Combine(Path.GetTempPath(), "cwtools-dynamic-planet-killer-on-actions-" + Guid.NewGuid().ToString("N"))

              try
                  let rulesPath = Path.Combine(folder, "rules.cwt")
                  let componentsPath = Path.Combine(folder, "common", "component_templates", "planet_killers.txt")
                  let onActionsPath = Path.Combine(folder, "common", "on_actions", "planet_killers.txt")

                  writeFile
                      rulesPath
                      """
types = {
    type[on_action] = {
        path = "game/common/on_actions"
        error_unknown_keys = suggest
        ## starts_with = on_destroy_planet_with_
        subtype[dynamic_planet_killer] = { }
        ## type_key_filter = on_destroy_planet_with_PLANET_KILLER_DELUGE_unqueued
        subtype[on_destroy_planet_with_PLANET_KILLER_DELUGE_unqueued] = { }
    }
    type[component_template] = {
        path = "game/common/component_templates"
    }
}

on_action = {
}

component_template = {
    key = scalar
    type = scalar
}
"""

                  writeFile
                      componentsPath
                      """
ge_deluge_planet_killer = {
    key = "GE_PLANET_KILLER_DELUGE"
    type = planet_killer
}
"""

                  writeFile
                      onActionsPath
                      """
on_destroy_planet_with_GE_PLANET_KILLER_DELUGE = {
}

on_destroy_planet_with_GE_PLANET_KILLER_DELUGE_queued = {
}

on_destroy_planet_with_GE_PLANET_KILLER_DELUGE_unqueued = {
}
"""

                  let settings =
                      { emptyStellarisSettings folder with
                          rules =
                              Some
                                  { ruleFiles = [ rulesPath, File.ReadAllText rulesPath ]
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>
                  let diagnostics = stl.ValidationErrors()

                  let generatedNames =
                      [ "on_destroy_planet_with_GE_PLANET_KILLER_DELUGE"
                        "on_destroy_planet_with_GE_PLANET_KILLER_DELUGE_queued"
                        "on_destroy_planet_with_GE_PLANET_KILLER_DELUGE_unqueued" ]

                  let onActionIds =
                      stl.Types()
                      |> Map.tryFind "on_action"
                      |> Option.defaultValue [||]
                      |> Array.map _.id

                  for name in generatedNames do
                      Expect.contains
                          onActionIds
                          name
                          $"Planet killer component should generate on_action type {name}"

                  let unknownGeneratedOnActions =
                      diagnostics
                      |> List.filter (fun e ->
                          e.code = "CW276"
                          && generatedNames |> List.exists (fun name -> e.message.Contains(name)))

                  Expect.isEmpty
                      unknownGeneratedOnActions
                      $"Generated planet killer on_actions should not be reported as unknown: %A{unknownGeneratedOnActions |> List.map _.message}"
              finally
                  try
                      if Directory.Exists folder then
                          Directory.Delete(folder, true)
                  with _ ->
                      () ]



// [<Tests>]
// let logTests =
//     testList "logs" [
//         testWithCapturedLogs "logFile" <| fun () ->
//             let logs = parseLogsFile "./testfiles/parsertests/setup.log"
//             match logs with
//             |Success((s, m), _, _) ->
//                 s |> List.iter (printfn "%A")
//                 m |> List.iter (printfn "%A")
//                 m |> List.map (fun x -> x.categories) |> List.distinct |> List.sort |> printfn "%A"
//             |Failure(e ,_, _) -> Expect.isFalse true e
//     ]


[<Tests>]
let stagedRefreshTests =
    testList
        "staged refresh"
        [ testWithCapturedLogs "lookup shallow clone and field snapshot"
          <| fun () ->
              let original = Lookup()
              original.scriptedVariables <- [ "@a", "1" ]
              original.typeDefInfo <- Map.ofList [ "t", [||] ]
              let mutable clone = original.ShallowClone()
              clone.scriptedVariables <- [ "@b", "2" ]
              clone.typeDefInfo <- Map.ofList [ "t2", [||] ]
              Expect.equal original.scriptedVariables [ "@a", "1" ] "clone mutation must not touch the original"
              Expect.isTrue (original.typeDefInfo.ContainsKey "t") "original typeDefInfo untouched"
              let snapshot = clone.CreateFieldSnapshot()
              clone <- null
              original.ApplyFieldSnapshot snapshot
              Expect.equal original.scriptedVariables [ "@b", "2" ] "snapshot copies simple fields"
              Expect.isTrue (original.typeDefInfo.ContainsKey "t2") "snapshot copies map fields"
              Expect.isFalse (original.typeDefInfo.ContainsKey "t") "snapshot replaces, not merges"

          testWithCapturedLogs "prepare/commit refresh matches locked refresh"
          <| fun () ->
              let configtext =
                  [ "./testfiles/localisationtests/test.cwt", File.ReadAllText "./testfiles/localisationtests/test.cwt"
                    "./testfiles/localisationtests/localisation.cwt",
                    File.ReadAllText "./testfiles/localisationtests/localisation.cwt" ]

              let settings = emptyStellarisSettings "./testfiles/localisationtests/gamefiles"

              let settings =
                  { settings with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = false
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>

              let sortedTypeIds (types: Map<string, TypeDefInfo array>) =
                  types |> Map.map (fun _ v -> v |> Array.map _.id |> Array.sort)

              let staged = stl.PrepareRefreshCaches()
              Expect.isSome staged "prepare should produce a staged refresh"
              Expect.isTrue (stl.CommitRefreshCaches staged.Value) "commit guards should hold with no interleaved writes"
              let typesAfterStaged = sortedTypeIds (stl.Types())
              let triggersAfterStaged = stl.ScriptedTriggers() |> List.length
              stl.RefreshCaches()
              Expect.equal typesAfterStaged (sortedTypeIds (stl.Types())) "staged refresh must produce the same type index as a locked refresh"
              Expect.equal triggersAfterStaged (stl.ScriptedTriggers() |> List.length) "staged refresh must produce the same trigger set"

              // A second prepare whose guards are invalidated must refuse to commit.
              let staged2 = stl.PrepareRefreshCaches()
              Expect.isSome staged2 "second prepare should succeed"
              stl.RefreshCaches()
              Expect.isFalse (stl.CommitRefreshCaches staged2.Value) "commit must refuse when the live state moved after prepare" ]


[<Tests>]
let paramSlotCompletionTests =
    testList
        "param slot completion"
        [ testWithCapturedLogs "complete at dollar-param value slot in definition"
          <| fun () ->
              let configtext = configFilesFromDir stellarisConfigRoot.Value

              let configtext =
                  ("./testfiles/validationtests/trigger_docs.log",
                   File.ReadAllText "./testfiles/validationtests/trigger_docs.log")
                  :: configtext

              let settings = emptyStellarisSettings "./testfiles/validationtests/eventtests"

              let settings =
                  { settings with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = false
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>

              let defFile =
                  stl.AllEntities()
                  |> Seq.map (fun struct (e, _) -> e.filepath)
                  |> Seq.find (fun f -> f.Replace('\\', '/').EndsWith("common/scripted_effects/test_effects.txt"))

              let defText = File.ReadAllText defFile
              let m = System.Text.RegularExpressions.Regex.Match(defText, "=\\s*\"?\\$war(\\|[^$\\r\\n]*)?\\$")
              Expect.isTrue m.Success "fixture should contain a $war$ value usage"
              let dollarIdx = defText.IndexOf('$', m.Index)
              let mutable line = 0
              let mutable lineStart = 0

              for i in 0 .. dollarIdx - 1 do
                  if defText.[i] = '\n' then
                      line <- line + 1
                      lineStart <- i + 1

              let col = dollarIdx - lineStart
              let pos = mkPos (line + 1) (col + 1)

              let labels =
                  stl.Complete pos defFile defText
                  |> List.map (function
                      | Simple(l, _, _) -> l
                      | Detailed(l, _, _, _) -> l
                      | Snippet(l, _, _, _, _) -> l)

              Expect.contains labels "yes" $"Expected bool completion at the $war$ slot, got %A{labels |> List.truncate 30}" ]
