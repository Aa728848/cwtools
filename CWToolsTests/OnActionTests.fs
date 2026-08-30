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

type private UnknownLookup() =
    inherit Lookup()

[<System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)>]
let private snapshotWithDerivedWeakReferences () =
    let source = IRLookup()
    source.allCoreLinks <- [ Effect("weak-trigger", [], EffectType.Trigger) ]
    source.triggers |> ignore
    source.triggersMap |> ignore
    source.effects |> ignore
    source.effectsMap |> ignore
    source.eventTargetLinks |> ignore
    source.eventTargetLinksMap |> ignore
    source.valueTriggers |> ignore
    source.valueTriggerMap |> ignore
    let derivedFields =
        typeof<Lookup>.GetFields(BindingFlags.Instance ||| BindingFlags.NonPublic ||| BindingFlags.DeclaredOnly)
        |> Array.filter (fun field -> field.Name.StartsWith("_triggers")
                                     || field.Name.StartsWith("_effects")
                                     || field.Name.StartsWith("_eventTargetLinks")
                                     || field.Name.StartsWith("_valueTriggers"))
        |> Array.map (fun field -> WeakReference(field.GetValue source))
    source.CreateFieldSnapshot(), derivedFields


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

          testCase "typed lookup snapshot covers fields, subtypes, identity, and derived caches"
          <| fun () ->
              let source = IRLookup()
              source.onlyScriptedEffects <- [ Effect("scripted_effect", [], EffectType.Effect) ]
              source.onlyScriptedTriggers <- [ Effect("scripted_trigger", [], EffectType.Trigger) ]
              source.rootFolders <- [| WD { path = "root"; name = "root" } |]
              source.staticModifiers <- [| { tag = "static"; categories = [] } |]
              source.coreModifiers <- [| { tag = "core"; category = ModifierCategory(2uy) } |]
              source.embeddedScriptedLoc <- [| "embedded" |]
              source.scriptedLoc <- [| "real" |]
              source.proccessedLoc <- []
              source.technologies <- [ "technology", [ "prerequisite" ] ]
              source.configRules <- [||]
              source.typeDefs <- []
              source.enumDefs <- Map.ofList [ "enum", ("description", [||]) ]
              source.typeDefInfo <- Map.ofList [ "type", [||] ]
              source.typeDefInfoForValidation <- Map.ofList [ "type", [||] ]
              source.varDefInfo <- Map.ofList [ "variable", [||] ]
              source.savedEventTargets <- ResizeArray([ "target", range.Zero, scopeManager.AnyScope ])
              source.scriptedVariables <- [ "@variable", "value" ]
              source.globalScriptedVariableNames <- [ "@variable" ]
              source.ScriptedEffectKeys <- [ "jomini" ]
              source.IRprovinces <- [| "province" |]
              source.IRcharacters <- [| "character" |]
              source.allCoreLinks <-
                  [ Effect("trigger", [], EffectType.Trigger)
                    Effect("effect", [], EffectType.Effect)
                    Effect("link", [], EffectType.Link)
                    Effect("value_trigger", [], EffectType.ValueTrigger) ]

              // Force the source caches so the snapshot must not simply retain them.
              let sourceTriggers = source.triggers
              let sourceTriggerMap = source.triggersMap
              let sourceEffects = source.effects
              let sourceEffectsMap = source.effectsMap
              let sourceLinks = source.eventTargetLinks
              let sourceLinksMap = source.eventTargetLinksMap
              let sourceValueTriggers = source.valueTriggers
              let sourceValueTriggerMap = source.valueTriggerMap

              let snapshot = source.CreateFieldSnapshot()
              let target = IRLookup()
              let targetIdentity = target :> obj
              target.ApplyFieldSnapshot snapshot

              Expect.isTrue (Object.ReferenceEquals(targetIdentity, target)) "apply preserves the target lookup identity"
              Expect.equal target.onlyScriptedEffects source.onlyScriptedEffects "base list field copied"
              Expect.equal target.rootFolders source.rootFolders "base array field copied"
              Expect.equal target.staticModifiers source.staticModifiers "base record array copied"
              Expect.equal target.coreModifiers source.coreModifiers "base modifier array copied"
              Expect.equal target.scriptedLoc source.scriptedLoc "embedded and real localisation fields copied"
              Expect.equal target.technologies source.technologies "base tuple list copied"
              Expect.equal target.enumDefs source.enumDefs "base enum map copied"
              Expect.equal target.typeDefInfo source.typeDefInfo "base type map copied"
              Expect.equal target.savedEventTargets source.savedEventTargets "base mutable collection copied"
              Expect.equal target.scriptedVariables source.scriptedVariables "base scripted variables copied"
              Expect.equal target.globalScriptedVariableNames source.globalScriptedVariableNames "base global names copied"
              Expect.equal target.ScriptedEffectKeys [ "jomini" ] "inherited Jomini field copied"
              Expect.equal target.IRprovinces [| "province" |] "IR province field copied"
              Expect.equal target.IRcharacters [| "character" |] "IR character field copied"
              Expect.equal (target.triggers |> List.map (fun effect -> effect.Name.GetString())) [ "trigger"; "value_trigger" ] "trigger list rebuilt from live links"
              Expect.equal (target.effects |> List.map (fun effect -> effect.Name.GetString())) [ "effect" ] "effect list rebuilt from live links"
              Expect.equal (target.eventTargetLinks |> List.map (fun effect -> effect.Name.GetString())) [ "link" ] "link list rebuilt from live links"
              Expect.equal (target.valueTriggers |> List.map (fun effect -> effect.Name.GetString())) [ "value_trigger" ] "value-trigger list rebuilt from live links"
              Expect.isFalse (Object.ReferenceEquals(sourceTriggerMap, target.triggersMap)) "derived trigger map is not snapshotted"
              Expect.isFalse (Object.ReferenceEquals(sourceEffectsMap, target.effectsMap)) "derived effect map is not snapshotted"
              Expect.isFalse (Object.ReferenceEquals(sourceLinksMap, target.eventTargetLinksMap)) "derived link map is not snapshotted"
              Expect.isFalse (Object.ReferenceEquals(sourceValueTriggerMap, target.valueTriggerMap)) "derived value-trigger map is not snapshotted"

              let retainedSnapshot, derivedWeakReferences = snapshotWithDerivedWeakReferences ()
              GC.Collect()
              GC.WaitForPendingFinalizers()
              GC.Collect()
              Expect.isTrue (derivedWeakReferences |> Array.forall (fun reference -> not reference.IsAlive)) "snapshot must not retain source derived Lazy values"
              GC.KeepAlive retainedSnapshot

              let roundTrip (source: Lookup) (target: Lookup) assertSubtype =
                  source.scriptedVariables <- [ "@roundtrip", source.GetType().Name ]
                  target.scriptedVariables <- [ "@old", target.GetType().Name ]
                  let targetIdentity = target :> obj
                  target.ApplyFieldSnapshot(source.CreateFieldSnapshot())
                  Expect.isTrue (Object.ReferenceEquals(targetIdentity, target)) "roundtrip preserves destination identity"
                  Expect.equal target.scriptedVariables source.scriptedVariables "roundtrip copies base fields"
                  assertSubtype ()

              let baseSource, baseTarget = Lookup(), Lookup()
              roundTrip baseSource baseTarget ignore

              let jominiSource, jominiTarget = JominiLookup(), JominiLookup()
              jominiSource.ScriptedEffectKeys <- [ "jomini-key" ]
              roundTrip jominiSource jominiTarget (fun () -> Expect.equal jominiTarget.ScriptedEffectKeys jominiSource.ScriptedEffectKeys "Jomini fields roundtrip")

              let ck2Source, ck2Target = CK2Lookup(), CK2Lookup()
              ck2Source.CK2LandedTitles <- Map.ofList [ (TitleType.Empire, true), [ "e_roundtrip" ] ]
              ck2Source.CK2provinces <- [| "ck2-province" |]
              roundTrip ck2Source ck2Target (fun () ->
                  Expect.equal ck2Target.CK2LandedTitles ck2Source.CK2LandedTitles "CK2 title fields roundtrip"
                  Expect.equal ck2Target.CK2provinces ck2Source.CK2provinces "CK2 province fields roundtrip")

              let eu4Source, eu4Target = EU4Lookup(), EU4Lookup()
              eu4Source.EU4ScriptedEffectKeys <- [| "eu4-effect" |]
              eu4Source.EU4TrueLegacyGovernments <- [| "eu4-government" |]
              roundTrip eu4Source eu4Target (fun () ->
                  Expect.equal eu4Target.EU4ScriptedEffectKeys eu4Source.EU4ScriptedEffectKeys "EU4 effect fields roundtrip"
                  Expect.equal eu4Target.EU4TrueLegacyGovernments eu4Source.EU4TrueLegacyGovernments "EU4 government fields roundtrip")

              let hoi4Source, hoi4Target = HOI4Lookup(), HOI4Lookup()
              hoi4Source.HOI4provinces <- [| "hoi4-province" |]
              roundTrip hoi4Source hoi4Target (fun () -> Expect.equal hoi4Target.HOI4provinces hoi4Source.HOI4provinces "HOI4 fields roundtrip")

              let stlSource, stlTarget = STLLookup(), STLLookup()
              roundTrip stlSource stlTarget ignore

              let irSource, irTarget = IRLookup(), IRLookup()
              irSource.ScriptedEffectKeys <- [ "ir-effect" ]
              irSource.IRprovinces <- [| "ir-province" |]
              irSource.IRcharacters <- [| "ir-character" |]
              roundTrip irSource irTarget (fun () ->
                  Expect.equal irTarget.ScriptedEffectKeys irSource.ScriptedEffectKeys "IR inherited fields roundtrip"
                  Expect.equal irTarget.IRprovinces irSource.IRprovinces "IR province fields roundtrip"
                  Expect.equal irTarget.IRcharacters irSource.IRcharacters "IR character fields roundtrip")

              let vic2Source, vic2Target = VIC2Lookup(), VIC2Lookup()
              vic2Source.VIC2provinces <- [| "vic2-province" |]
              roundTrip vic2Source vic2Target (fun () -> Expect.equal vic2Target.VIC2provinces vic2Source.VIC2provinces "VIC2 fields roundtrip")

              let knownSubtypes: Lookup array =
                  [| baseSource; jominiSource; ck2Source; eu4Source; hoi4Source; stlSource; irSource; vic2Source |]

              let ignoredDerivedFields =
                  set [ "_triggers"; "_triggersMap"; "_effects"; "_effectsMap"
                        "_eventTargetLinks"; "_eventTargetLinksMap"; "_valueTriggers"; "_valueTriggersMap" ]
              let mutableFields (lookupType: Type) =
                  let rec fields current =
                      if isNull current || current = typeof<obj> then []
                      else
                          let own =
                              current.GetFields(BindingFlags.Instance ||| BindingFlags.NonPublic ||| BindingFlags.Public ||| BindingFlags.DeclaredOnly)
                              |> Array.filter (fun field -> not field.IsInitOnly && not (ignoredDerivedFields.Contains field.Name))
                              |> Array.map _.Name
                              |> Array.toList
                          own @ fields current.BaseType
                  fields lookupType |> Set.ofList
              let expectedFields =
                  set [ "_allCoreLinks"; "onlyScriptedEffects@"; "onlyScriptedTriggers@"; "rootFolders@"
                        "staticModifiers@"; "coreModifiers@"; "embeddedScriptedLoc@"; "_realScriptedLoc@"
                        "proccessedLoc@"; "technologies@"; "configRules@"; "typeDefs@"; "enumDefs@"
                        "typeDefInfo@"; "typeDefInfoForValidation@"; "varDefInfo@"; "extendedConfigMetadata@"
                        "savedEventTargets@"; "scriptedVariables@"; "globalScriptedVariableNames@"
                        "ScriptedEffectKeys@"; "CK2LandedTitles@"; "CK2provinces@"; "EU4ScriptedEffectKeys@"
                        "EU4TrueLegacyGovernments@"; "HOI4provinces@"; "IRprovinces@"; "IRcharacters@"
                        "VIC2provinces@" ]
              let actualFields = knownSubtypes |> Array.collect (fun lookup -> mutableFields (lookup.GetType()) |> Set.toArray) |> Set.ofArray
              Expect.equal actualFields expectedFields "every mutable source field must be represented explicitly"

              let canonicalFields (lookupType: Type) =
                  let rec fields current =
                      if isNull current || current = typeof<obj> then [||]
                      else
                          Array.append
                              (current.GetFields(BindingFlags.Instance ||| BindingFlags.NonPublic ||| BindingFlags.Public ||| BindingFlags.DeclaredOnly)
                               |> Array.filter (fun field -> not field.IsInitOnly && not (ignoredDerivedFields.Contains field.Name)))
                              (fields current.BaseType)
                  fields lookupType

              let assertCanonicalFieldsRoundTrip (source: Lookup) (destination: Lookup) =
                  let destinationIdentity = destination :> obj
                  destination.ApplyFieldSnapshot(source.CreateFieldSnapshot())
                  Expect.isTrue (Object.ReferenceEquals(destinationIdentity, destination)) $"{source.GetType().Name} apply preserves destination identity"

                  for field in canonicalFields (source.GetType()) do
                      let sourceValue = field.GetValue source
                      let destinationValue = field.GetValue destination
                      Expect.equal destinationValue sourceValue $"{source.GetType().Name}.{field.Name} is copied"

                      if not field.FieldType.IsValueType && not (isNull sourceValue) then
                          Expect.isTrue
                              (Object.ReferenceEquals(sourceValue, destinationValue))
                              $"{source.GetType().Name}.{field.Name} remains structurally shared"

              let freshTargets: Lookup array =
                  [| Lookup(); JominiLookup(); CK2Lookup(); EU4Lookup(); HOI4Lookup(); STLLookup(); IRLookup(); VIC2Lookup() |]

              Array.iter2 assertCanonicalFieldsRoundTrip knownSubtypes freshTargets

              let mismatched = Lookup()
              mismatched.scriptedVariables <- [ "@sentinel", "unchanged" ]
              Expect.throws (fun () -> mismatched.ApplyFieldSnapshot snapshot) "snapshot subtype mismatch must fail"
              Expect.equal mismatched.scriptedVariables [ "@sentinel", "unchanged" ] "subtype guard must run before applying base fields"

              let unknown = UnknownLookup()
              Expect.throws (fun () -> unknown.CreateFieldSnapshot() |> ignore) "unknown Lookup subtype must fail"

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
              let liveTypesBeforeReject = sortedTypeIds (stl.Types())
              let liveTriggersBeforeReject = stl.ScriptedTriggers() |> List.map (fun effect -> effect.Name.GetString())
              Expect.isFalse (stl.CommitRefreshCaches staged2.Value) "commit must refuse when the live state moved after prepare"
              Expect.equal (sortedTypeIds (stl.Types())) liveTypesBeforeReject "rejected snapshot must not publish staged types"
              Expect.equal (stl.ScriptedTriggers() |> List.map (fun effect -> effect.Name.GetString())) liveTriggersBeforeReject "rejected snapshot must not publish staged links" ]


[<Tests>]
let lazyRefreshTests =
    let createGame (files: (string * string) list) =
        let root = Path.Combine(Path.GetTempPath(), "cwtools-lazy-refresh-" + Guid.NewGuid().ToString("N"))
        for relativePath, text in files do
            let path = Path.Combine(root, relativePath)
            Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
            File.WriteAllText(path, text)

        let configText = configFilesFromDir (Path.Combine(stellarisConfigRoot.Value, "config"))
        let settings =
            { emptyStellarisSettings root with
                rules =
                    Some
                        { ruleFiles = configText
                          validateRules = false
                          debugRulesOnly = false
                          debugMode = false } }
        root, STLGame(settings)

    let semanticFacts (game: STLGame) =
        let variables =
            game.Lookup.varDefInfo
            |> Map.map (fun _ values -> values |> Array.map fst |> Array.sort)
        let eventTargets =
            game.Lookup.savedEventTargets
            |> Seq.map (fun (name, _, scope) -> name, scope.ToString())
            |> Seq.sort
            |> Seq.toArray
        variables, eventTargets

    testList
        "lazy refresh"
        [ testWithCapturedLogs "events-only refresh preserves facts without creating computed data"
          <| fun () ->
              let root, concrete =
                  createGame
                      [ Path.Combine("events", "lazy_events.txt"),
                        "namespace = lazy\ncountry_event = { id = lazy.1 hide_window = yes is_triggered_only = yes immediate = { save_event_target_as = lazy_target set_variable = { which = lazy_variable value = 1 } } }" ]
              let game = concrete :> IGame<STLComputedData>
              try
                  let beforeFacts = semanticFacts concrete
                  let beforeVariables, beforeTargets = beforeFacts
                  Expect.contains beforeVariables.["variable"] "lazy_variable" "fixture must contribute the defined variable"
                  Expect.isTrue (beforeTargets |> Array.exists (fun (name, _) -> name = "lazy_target")) "fixture must contribute the saved event target"
                  game.RefreshCaches()
                  Expect.equal (semanticFacts concrete) beforeFacts "compact refresh facts must match the established semantics"
                  let stats = concrete.LastLazyRefreshStats |> Option.get
                  Expect.equal stats.newlyCreated 0 "events-only refresh must not create computed-data values"
                  Expect.equal stats.afterRefreshCreated stats.beforeCreated "refresh itself must leave lazy creation unchanged"
                  Expect.equal stats.afterRecomputeCreated 0 "post-publication recompute must install fresh uncreated lazies"
              finally
                  (concrete :> IDisposable).Dispose()
                  if Directory.Exists root then Directory.Delete(root, true)

          testWithCapturedLogs "mixed refresh creates fewer computed values than total entities"
          <| fun () ->
              let root, concrete =
                  createGame
                      [ Path.Combine("events", "lazy_mixed_events.txt"),
                        "namespace = lazy_mixed\ncountry_event = { id = lazy_mixed.1 hide_window = yes is_triggered_only = yes immediate = { lazy_save = { TARGET = mixed_target } } }"
                        Path.Combine("common", "scripted_effects", "lazy_mixed_effects.txt"),
                        "lazy_save = { save_event_target_as = $TARGET$ set_variable = { which = mixed_variable value = 1 } }" ]
              let game = concrete :> IGame<STLComputedData>
              try
                  let firstLazy = game.AllEntities() |> Seq.head |> fun struct (_, data) -> data
                  firstLazy.Force() |> ignore
                  let beforeFacts = semanticFacts concrete
                  let beforeVariables, beforeTargets = beforeFacts
                  Expect.contains beforeVariables.["variable"] "mixed_variable" "scripted expansion must contribute the defined variable"
                  Expect.isTrue (beforeTargets |> Array.exists (fun (name, _) -> name = "mixed_target")) "scripted expansion must contribute the saved event target"
                  game.RefreshCaches()
                  Expect.equal (semanticFacts concrete) beforeFacts "mixed compact refresh facts must remain semantically equivalent"
                  let stats = concrete.LastLazyRefreshStats |> Option.get
                  Expect.isLessThan stats.newlyCreated stats.total "refresh must create fewer computed values than the entity total"
                  Expect.equal stats.afterRecomputeCreated 0 "recompute must replace mixed old lazies without forcing replacements"
              finally
                  (concrete :> IDisposable).Dispose()
                  if Directory.Exists root then Directory.Delete(root, true) ]

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
