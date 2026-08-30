module ContractTests

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
let crossGameIncrementalCapabilityTests =
    test "all game adapters expose cross-game incremental capabilities" {
        let adapters =
            [ typeof<CWTools.Games.Stellaris.STLGame>
              typeof<CWTools.Games.HOI4.HOI4Game>
              typeof<CWTools.Games.EU4.EU4Game>
              typeof<CWTools.Games.EU5.EU5Game>
              typeof<CWTools.Games.CK2.CK2Game>
              typeof<CWTools.Games.CK3.CK3Game>
              typeof<CWTools.Games.IR.IRGame>
              typeof<CWTools.Games.VIC2.VIC2Game>
              typeof<CWTools.Games.VIC3.VIC3Game>
              typeof<CWTools.Games.Custom.CustomGame> ]

        for adapter in adapters do
            Expect.isTrue
                (typeof<IIncrementalTypeIndex>.IsAssignableFrom adapter)
                $"{adapter.Name} must expose staged type-index refresh"
            Expect.isTrue
                (typeof<IIncrementalLocalisation>.IsAssignableFrom adapter)
                $"{adapter.Name} must expose incremental localisation refresh and deletion"
            Expect.isTrue
                (typeof<ISemanticDeltaProvider>.IsAssignableFrom adapter)
                $"{adapter.Name} must expose a semantic contribution signature"
    }

[<Tests>]
let carrierScopeContractTests =
    let makeCarrierEntity logicalpath text =
        match CKParser.parseString text logicalpath with
        | Success(statements, _, _) ->
            let node = STLProcess.shipProcess.ProcessNode () "root" (mkZeroFile logicalpath) statements
            { filepath = logicalpath
              logicalpath = logicalpath
              rawEntity = node
              entity = node
              validate = true
              entityType = EntityType.Other
              overwrite = Overwrite.No }
        | Failure(error, _, _) -> failwith error

    testList
        "carrier scope contracts"
        [ test "carrier inherits contracts supported by either planet or ship" {
              let planet = Scope(10uy)
              let ship = Scope(11uy)
              let carrier = Scope(12uy)
              let country = Scope(13uy)
              let normalize = STLGameFunctions.normalizeCarrierScopeSet planet ship carrier

              Expect.sequenceEqual
                  (normalize [ planet; ship; country ])
                  [ planet; ship; country; carrier ]
                  "shared planet/ship contracts should accept carrier"

              Expect.sequenceEqual
                  (normalize [ planet; carrier; country ])
                  [ planet; country; carrier ]
                  "planet contracts should accept the Carrier union"

              Expect.sequenceEqual
                  (normalize [ ship; carrier; country ])
                  [ ship; country; carrier ]
                  "ship contracts should accept the Carrier union" }

          test "carrier invalidation classifies semantic contributors" {
              Expect.isFalse
                  (ResourceManagerEager.isCarrierRelevantPath "common/buildings/example.txt")
                  "ordinary definition files should keep the current Carrier snapshot"
              Expect.isTrue
                  (ResourceManagerEager.isCarrierRelevantPath "common/on_actions/example.txt")
                  "on_action changes can alter Carrier event callers"
              Expect.isTrue
                  (ResourceManagerEager.isCarrierRelevantPath "events/example.txt")
                  "root-level event paths must be classified without a leading slash"
              Expect.isTrue
                  (ResourceManagerEager.isCarrierRelevantNodeKey "country_event")
                  "event calls and definitions contribute to Carrier propagation"
              Expect.isTrue
                  (ResourceManagerEager.isCarrierRelevantNodeKey "start_situation")
                  "situation target propagation contributes to Carrier inference"
              Expect.isFalse
                  (ResourceManagerEager.isCarrierRelevantNodeKey "planet_modifier")
                  "unrelated keys should not advance the Carrier epoch" }

          test "carrier contribution fingerprint ignores formatting but tracks semantics" {
              let baseline =
                  makeCarrierEntity "events/test.txt" "country_event = { id = test.1 }"
              let commentOnly =
                  makeCarrierEntity "events/test.txt" "# formatting\ncountry_event = { id = test.1 }"
              let changed =
                  makeCarrierEntity "events/test.txt" "country_event = { id = test.2 }"

              Expect.equal
                  (CarrierContribution.semanticFingerprint baseline)
                  (CarrierContribution.semanticFingerprint commentOnly)
                  "comments and positions must not invalidate the Carrier snapshot"
              Expect.notEqual
                  (CarrierContribution.semanticFingerprint baseline)
                  (CarrierContribution.semanticFingerprint changed)
                  "event identity changes must invalidate the Carrier snapshot" }

          test "carrier scheduler keeps only the newest A-B-C request" {
              let scheduled = System.Collections.Generic.Queue<unit -> unit>()
              let mutable captured = "A"
              let builds = ResizeArray<string>()
              let gate =
                  STLGameFunctions.CarrierSnapshotBuildGate<string, string, string>(
                      (fun () -> struct (builds.Count, [| captured |])),
                      (fun _ key _ entities cancellationToken ->
                          cancellationToken.ThrowIfCancellationRequested()
                          let result = $"%s{key}:%s{entities[0]}"
                          builds.Add result
                          result),
                      schedule = scheduled.Enqueue)

              let a = gate.Request "A"
              captured <- "B"
              let b = gate.Request "B"
              captured <- "C"
              let c = gate.Request "C"

              Expect.equal scheduled.Count 1 "only A may occupy the scheduler"
              Expect.isTrue b.retry.Value.IsCompleted "C must release the superseded B retry"
              Expect.isFalse c.retry.Value.IsCompleted "C waits for the active A owner to exit"
              scheduled.Dequeue() ()
              Expect.isTrue a.task.Value.IsCanceled "A is cancelled when B supersedes it"
              Expect.isTrue c.retry.Value.IsCompleted "A exit releases the newest C retry"

              let cBuild = gate.Request "C"
              Expect.equal scheduled.Count 1 "the newest request starts exactly once"
              scheduled.Dequeue() ()
              Expect.equal cBuild.task.Value.Result "C:C" "C captures the newest entity view"
              let published = gate.Request "C"
              Expect.equal published.exact (Some "C:C") "only C is published"
              Expect.sequenceEqual builds [ "C:C" ] "neither stale A nor superseded B may build"
              (gate :> IDisposable).Dispose() }

          test "carrier scheduler coalesces same-key callers" {
              let scheduled = System.Collections.Generic.Queue<unit -> unit>()
              let mutable captures = 0
              let gate =
                  STLGameFunctions.CarrierSnapshotBuildGate<int, int, int>(
                      (fun () ->
                          captures <- captures + 1
                          struct (captures, [| captures |])),
                      (fun _ key _ entities _ -> key + entities[0]),
                      schedule = scheduled.Enqueue)

              let first = gate.Request 10
              let second = gate.Request 10
              Expect.equal captures 1 "same-key callers share one captured entity view"
              Expect.equal scheduled.Count 1 "same-key callers schedule one worker"
              Expect.isTrue
                  (obj.ReferenceEquals(first.task.Value, second.task.Value))
                  "same-key callers observe the same completion task"
              scheduled.Dequeue() ()
              Expect.equal first.task.Value.Result 11 "the shared build completes normally"
              Expect.equal (gate.Request 10).exact (Some 11) "the shared result is published once"
              (gate :> IDisposable).Dispose() }

          test "carrier invalidation is a publication barrier" {
              use started = new ManualResetEventSlim(false)
              use release = new ManualResetEventSlim(false)
              let mutable result = "old"
              let gate =
                  STLGameFunctions.CarrierSnapshotBuildGate<int, unit, string>(
                      (fun () -> struct (0, [| () |])),
                      (fun _ _ _ _ _ ->
                          started.Set()
                          release.Wait()
                          result),
                      schedule = (fun work -> System.Threading.Tasks.Task.Run(Action work) |> ignore))

              let stale = gate.Request 1
              Expect.isTrue (started.Wait(TimeSpan.FromSeconds 2.0)) "the stale build must start"
              gate.Invalidate()
              release.Set()
              Expect.throwsT<AggregateException>
                  (fun () -> stale.task.Value.Wait())
                  "the invalidated worker completes as cancelled"
              result <- "new"
              let afterBarrier = gate.Request 1
              Expect.isNone afterBarrier.exact "invalidation must bar publication of the old result"
              Expect.equal afterBarrier.task.Value.Result "new" "the next generation builds afresh"
              Expect.equal (gate.Request 1).exact (Some "new") "only the new generation is published"
              (gate :> IDisposable).Dispose() }

          test "carrier shutdown cancels and joins an active build" {
              use started = new ManualResetEventSlim(false)
              let gate =
                  STLGameFunctions.CarrierSnapshotBuildGate<int, unit, int>(
                      (fun () -> struct (0, [| () |])),
                      (fun _ _ _ _ cancellationToken ->
                          started.Set()
                          cancellationToken.WaitHandle.WaitOne() |> ignore
                          cancellationToken.ThrowIfCancellationRequested()
                          1))

              let active = gate.Request 1
              Expect.isTrue (started.Wait(TimeSpan.FromSeconds 2.0)) "the active build must start"
              let shutdown = gate.ShutdownAsync()
              Expect.isTrue (shutdown.Wait(TimeSpan.FromSeconds 2.0)) "shutdown waits for worker cancellation"
              Expect.isTrue active.task.Value.IsCanceled "the active caller observes cancellation"
              Expect.throwsT<ObjectDisposedException>
                  (fun () -> gate.Request 1 |> ignore)
                  "shutdown rejects new work"
              (gate :> IDisposable).Dispose() }

          test "carrier shutdown preserves active build faults" {
              use started = new ManualResetEventSlim(false)
              use release = new ManualResetEventSlim(false)
              let failure = InvalidOperationException("carrier build failed")
              let gate =
                  STLGameFunctions.CarrierSnapshotBuildGate<int, unit, int>(
                      (fun () -> struct (0, [| () |])),
                      (fun _ _ _ _ _ ->
                          started.Set()
                          release.Wait()
                          raise failure))

              gate.Request 1 |> ignore
              Expect.isTrue (started.Wait(TimeSpan.FromSeconds 2.0)) "the faulting build must start"
              let shutdown = gate.ShutdownAsync()
              release.Set()
              let observed =
                  try
                      shutdown.GetAwaiter().GetResult()
                      None
                  with :? InvalidOperationException as error ->
                      Some error
              Expect.isSome observed "shutdown must surface a worker fault"
              Expect.equal observed.Value.Message failure.Message "shutdown preserves the original fault"
              Expect.throwsT<InvalidOperationException>
                  (fun () -> (gate :> IDisposable).Dispose())
                  "synchronous disposal preserves the same fault" } ]

[<Tests>]
let localValidationContractTests =
    testList
        "local validation contracts"
        [ test "audited local validators cannot enumerate the workspace view" {
              let validator: StructureValidator<STLComputedData> =
                  fun workspace _changed ->
                      workspace.All |> ignore
                      OK
              let local = ValidationCore.toLocalStructureValidator validator
              let changed = EntitySet<STLComputedData>(Seq.empty)

              Expect.throws
                  (fun () -> local changed |> ignore)
                  "misclassified project-wide validators must fail before a hot-path enumeration" }

          test "audited local validators receive changed entities normally" {
              let validator: StructureValidator<STLComputedData> =
                  fun _workspace _changed -> OK
              let local = ValidationCore.toLocalStructureValidator validator
              let changed = EntitySet<STLComputedData>(Seq.empty)

              Expect.equal (local changed) OK "a validator that ignores the workspace view remains local" } ]

[<Tests>]
let nameSuggestionTests =
    testList
        "name suggestions"
        [ test "levenshtein cutoff is case insensitive" {
              Expect.equal
                  (NameSuggestion.levenshteinWithin 1 "Planet" "plant")
                  (ValueSome 1)
                  "one deletion should be within the cutoff"

              Expect.equal
                  (NameSuggestion.levenshteinWithin 2 "country" "planet")
                  ValueNone
                  "distant names should stop outside the cutoff" }

          test "closest suggestion reuses the same distance semantics" {
              Expect.equal
                  (NameSuggestion.suggestClosest "planrt" [ "country"; "planet"; "fleet" ])
                  (Some "planet")
                  "the closest candidate should still be selected" } ]

[<Tests>]
let stringResourceManagerTests =
    testList
        "string resource manager"
        [ test "parallel first use allocates one exact token" {
              let manager = StringResourceManager()

              let tokens =
                  Array.Parallel.init 10000 (fun _ -> manager.InternIdentifierToken "ConcurrentKey")

              Expect.isTrue
                  (tokens |> Array.forall ((=) tokens[0]))
                  "parallel callers should receive the same token"

              Expect.equal manager.StringCount 2 "only exact and lowercase keys should be retained"
              Expect.equal manager.IntCount 2 "racing factories must not leak integer mappings"
              Expect.equal manager.TokenIdCounter 2 "racing factories must not consume unused IDs" }

          test "deserialized manager rebuilds insertion locks" {
              let manager = StringResourceManager()
              let original = manager.InternIdentifierToken "MixedCase"
              let serializer = FsPickler.CreateBinarySerializer(picklerResolver = Serializer.picklerCache)
              let restored = manager |> serializer.Pickle |> serializer.UnPickle<StringResourceManager>
              let existing = restored.InternIdentifierToken "MixedCase"
              let variant = restored.InternIdentifierToken "MIXEDCASE"
              Expect.equal existing original "existing tokens should survive serialization"
              Expect.equal variant.lower original.lower "new case variants should reuse the lowercase token" } ]

[<Tests>]
let scriptedTriggerScopeInferenceTests =
    testSequenced
    <| testList
        "scripted trigger scope inference"
        [ test "fixed-width scope intersections preserve strict and relaxed inference" {
              let inputs =
                  Array.init 130 (fun i ->
                      let name = sprintf "scope_%03d" i

                      { ScopeInput.name = name
                        aliases = [ name ]
                        isSubscopeOf = []
                        dataTypeName = None })

              try
                  scopeManager.ReInit(inputs, [||])
                  let parseScope name = scopeManager.ParseScope () name
                  let low = parseScope "scope_003"
                  let shared = parseScope "scope_068"
                  let high = parseScope "scope_120"
                  let token name = StringResource.stringManager.InternIdentifierToken name
                  let vanilla = Collections.Generic.Dictionary<StringToken, Scope list>()
                  vanilla[(token "left").normal] <- [ low; shared ]
                  vanilla[(token "right").normal] <- [ shared; high ]
                  let noNewEffects: Map<StringToken, Scope list> = Map.empty
                  let noScopedEffects: Map<StringToken, Scope list> = Map.empty

                  let infer strict text =
                      match CKParser.parseString text "common/scripted_triggers/test.txt" with
                      | Success(statements, _, _) ->
                          let root = STLProcess.shipProcess.ProcessNode () "root" range.Zero statements
                          let trigger = root.Children |> List.exactlyOne

                          STLProcess.scriptedTriggerScope
                              strict
                              vanilla
                              noNewEffects
                              noScopedEffects
                              trigger.Key
                              trigger
                      | Failure(error, _, _) -> failtest error

                  let known =
                      infer
                          true
                          "test_trigger = { left = yes AND = { right = yes } }"

                  let withUnknown =
                      "test_trigger = { left = yes AND = { right = yes unknown = yes } }"

                  Expect.equal known (Set.singleton shared) "known scopes should intersect across mask words"
                  Expect.isEmpty (infer true withUnknown) "strict inference should reject an unknown trigger"

                  Expect.equal
                      (infer false withUnknown)
                      (Set.singleton shared)
                      "first-pass inference should treat an unknown trigger as unconstrained"
              finally
                  UtilityParser.initializeScopes None (Some(defaultScopeInputs ())) } ]

[<Tests>]
let scriptedDefinitionCommentTests =
    testList
        "scripted definition comments"
        [ test "single-pass lookup preserves first-key and comment ordering semantics" {
              let text =
                  "# first\n\
                   # second\n\
                   duplicate = { }\n\
                   separator = yes\n\
                   # later\n\
                   duplicate = { }\n\
                   # other\n\
                   distinct = { }"

              match CKParser.parseString text "common/scripted_effects/test.txt" with
              | Success(statements, _, _) ->
                  let root = STLProcess.shipProcess.ProcessNode () "root" range.Zero statements
                  let definitions = STLLookup.getChildrenWithComments root
                  Expect.equal definitions.Length 3 "all top-level nodes should be returned"

                  let firstComments = definitions[0] |> snd
                  let duplicateComments = definitions[1] |> snd
                  let distinctComments = definitions[2] |> snd
                  Expect.equal firstComments [ " second"; " first" ] "adjacent comments retain their prior order"

                  Expect.equal
                      duplicateComments
                      firstComments
                      "duplicate keys should continue to use the first definition's comments"

                  Expect.equal distinctComments [ " other" ] "non-node children should reset pending comments"
              | Failure(error, _, _) -> failtest error } ]

[<Tests>]
let crossGameIncrementalEquivalenceTests =
    testSequenced
    <| (testWithCapturedLogs "all game adapters match full refresh for shared incremental operations"
    <| fun () ->
        let folder =
            Path.Combine(Path.GetTempPath(), "cwtools-cross-game-incremental-" + Guid.NewGuid().ToString("N"))
        let scriptFolder = Path.Combine(folder, "common", "test_items")
        let scriptFile = Path.Combine(scriptFolder, "items.txt")
        Directory.CreateDirectory(scriptFolder) |> ignore
        File.WriteAllText(scriptFile, "first_item = { value = 1 }")

        let rules =
            """
types = {
    type[test_item] = {
        path = "game/common/test_items"
    }
}
test_item = {
    value = int
}
"""
        let ruleFiles = [ Path.Combine(folder, "rules.cwt"), rules ]

        let factories: (string * string * (unit -> IGame)) list =
            [ "Stellaris", ".yml", fun () ->
                  STLGame(crossGameSettings<STLLookup> folder ruleFiles [| Lang.STL STLLang.English |]) :> IGame
              "HOI4", ".yml", fun () ->
                  CWTools.Games.HOI4.HOI4Game(crossGameSettings<HOI4Lookup> folder ruleFiles [| Lang.HOI4 HOI4Lang.English |]) :> IGame
              "EU4", ".yml", fun () ->
                  CWTools.Games.EU4.EU4Game(crossGameSettings<EU4Lookup> folder ruleFiles [| Lang.EU4 EU4Lang.English |]) :> IGame
              "EU5", ".yml", fun () ->
                  CWTools.Games.EU5.EU5Game(crossGameSettings<JominiLookup> folder ruleFiles [| Lang.EU5 EU5Lang.English |]) :> IGame
              "CK2", ".csv", fun () ->
                  CWTools.Games.CK2.CK2Game(crossGameSettings<CK2Lookup> folder ruleFiles [| Lang.CK2 CK2Lang.English |]) :> IGame
              "CK3", ".yml", fun () ->
                  CWTools.Games.CK3.CK3Game(crossGameSettings<JominiLookup> folder ruleFiles [| Lang.CK3 CK3Lang.English |]) :> IGame
              "Imperator", ".yml", fun () ->
                  CWTools.Games.IR.IRGame(crossGameSettings<IRLookup> folder ruleFiles [| Lang.IR IRLang.English |]) :> IGame
              "VIC2", ".yml", fun () ->
                  CWTools.Games.VIC2.VIC2Game(crossGameSettings<VIC2Lookup> folder ruleFiles [| Lang.VIC2 VIC2Lang.English |]) :> IGame
              "VIC3", ".yml", fun () ->
                  CWTools.Games.VIC3.VIC3Game(crossGameSettings<JominiLookup> folder ruleFiles [| Lang.VIC3 VIC3Lang.English |]) :> IGame
              "Custom", ".yml", fun () ->
                  CWTools.Games.Custom.CustomGame(
                      crossGameSettings<JominiLookup> folder ruleFiles [| Lang.Custom CustomLang.English |],
                      "custom"
                  )
                  :> IGame ]

        let typeFacts (game: IGame) =
            game.Types()
            |> Map.tryFind "test_item"
            |> Option.defaultValue [||]
            |> Array.map _.id
            |> Array.sort

        try
            for gameName, localisationExtension, createGame in factories do
                File.WriteAllText(scriptFile, "first_item = { value = 1 }")
                let incrementalGame = createGame ()
                let fullGame = createGame ()
                incrementalGame.UpdateFile false scriptFile (Some "first_item = { value = 1 }") |> ignore
                fullGame.UpdateFile false scriptFile (Some "first_item = { value = 1 }") |> ignore
                let index = incrementalGame :?> IIncrementalTypeIndex
                let localisation = incrementalGame :?> IIncrementalLocalisation
                let semantics = incrementalGame :?> ISemanticDeltaProvider

                Expect.isTrue
                    (localisation.IsLocalisationFile("test" + localisationExtension))
                    $"{gameName} must recognise its declared localisation extension"
                Expect.isFalse
                    (localisation.IsLocalisationFile("test.txt"))
                    $"{gameName} must not classify scripts as localisation"
                Expect.isSome
                    (semantics.SemanticSignatureForFile scriptFile)
                    $"{gameName} must expose a semantic signature for a loaded script"
                Expect.contains
                    (typeFacts incrementalGame)
                    "first_item"
                    $"{gameName} fixture must contribute a real CWT-derived type"

                let renamed = "second_item = { value = 2 }"
                incrementalGame.UpdateFile false scriptFile (Some renamed) |> ignore
                let typeStage = index.PrepareTypeIndex [ scriptFile ]
                Expect.isSome typeStage $"{gameName} must prepare a type-index stage"
                Expect.isTrue
                    (index.CommitTypeIndex typeStage.Value)
                    $"{gameName} must commit its type-index stage"
                fullGame.UpdateFile false scriptFile (Some renamed) |> ignore
                fullGame.RefreshCaches()
                Expect.equal
                    (typeFacts incrementalGame)
                    (typeFacts fullGame)
                    $"{gameName} incremental type rename must match full refresh"

                let scripted = "third_item = { value = 3 }"
                incrementalGame.UpdateFile false scriptFile (Some scripted) |> ignore
                let scriptedStage = incrementalGame.PrepareScriptedTypes([ scriptFile ], true)
                Expect.isSome scriptedStage $"{gameName} must prepare scripted services"
                Expect.isTrue
                    (incrementalGame.CommitScriptedTypes scriptedStage.Value)
                    $"{gameName} must commit scripted services"
                fullGame.UpdateFile false scriptFile (Some scripted) |> ignore
                fullGame.RefreshCaches()
                Expect.equal
                    (typeFacts incrementalGame)
                    (typeFacts fullGame)
                    $"{gameName} incremental scripted refresh must match full refresh"

                Expect.isTrue
                    (index.RemoveTypeIndex [ scriptFile ])
                    $"{gameName} must remove a file from the type index"
                fullGame.UpdateFile false scriptFile (Some "") |> ignore
                fullGame.RefreshCaches()
                Expect.equal
                    (typeFacts incrementalGame)
                    (typeFacts fullGame)
                    $"{gameName} incremental type deletion must match full refresh"

                let localisationFolder = Path.Combine(folder, "localisation")
                Directory.CreateDirectory(localisationFolder) |> ignore
                let localisationFile =
                    Path.Combine(localisationFolder, "cross_game" + localisationExtension)
                let localisationText key value =
                    if gameName = "CK2" || gameName = "VIC2" then
                        $"#CODE;ENGLISH;FRENCH;GERMAN;;SPANISH;;;;;;;;;x{Environment.NewLine}{key};{value};French;German;;Spanish;;;;;;;;;x"
                    else
                        $"l_english:\n {key}:0 \"{value}\"\n"

                let originalLocalisation = localisationText "cross_old" "Old"
                File.WriteAllText(localisationFile, originalLocalisation)
                incrementalGame.UpdateFile false localisationFile (Some originalLocalisation) |> ignore
                fullGame.UpdateFile false localisationFile (Some originalLocalisation) |> ignore
                incrementalGame.RefreshLocalisationCaches()
                fullGame.RefreshLocalisationCaches()
                incrementalGame.LocalisationErrors(true, true) |> ignore
                fullGame.LocalisationErrors(true, true) |> ignore

                let renamedLocalisation = localisationText "cross_new" "New"
                File.WriteAllText(localisationFile, renamedLocalisation)
                incrementalGame.UpdateFile false localisationFile (Some renamedLocalisation) |> ignore
                let renamePeek = localisation.PeekLocalisationDelta "cross-game-contract"
                let renameBatch =
                    match renamePeek with
                    | Result.Ok(Some batch) -> batch
                    | other -> failtestf $"{gameName} localisation rename must produce an incremental delta, got %A{other}"
                Expect.containsAll
                    renameBatch.delta.changedKeys
                    [| "cross_old"; "cross_new" |]
                    $"{gameName} localisation rename must invalidate old and new keys"
                Expect.contains
                    renameBatch.delta.affectedLocalisationFiles
                    localisationFile
                    $"{gameName} detached rename payload must include its file replacement"
                let renameStage =
                    match localisation.PrepareLocalisationRefresh "cross-game-contract" with
                    | Result.Ok(Some staged) -> staged
                    | other -> failtestf $"{gameName} localisation rename must prepare, got %A{other}"
                let incrementalLocalisationErrors =
                    match localisation.TryCommitLocalisationRefresh renameStage with
                    | StagedLocalisationCommitResult.Committed result -> result
                    | other -> failtestf $"{gameName} localisation rename stage must commit, got %A{other}"
                fullGame.UpdateFile false localisationFile (Some renamedLocalisation) |> ignore
                fullGame.RefreshLocalisationCaches()
                let affectedAfterRename = incrementalLocalisationErrors.affectedFiles |> Set.ofArray
                let fullRenameErrors =
                    fullGame.LocalisationErrors(true, true)
                    |> List.filter (fun error -> affectedAfterRename.Contains error.range.FileName)
                let errorFacts errors =
                    errors
                    |> List.map (fun error ->
                        error.code,
                        error.range.FileName,
                        error.range.StartLine,
                        error.range.StartColumn,
                        error.message)
                    |> Set.ofList
                Expect.equal
                    (errorFacts incrementalLocalisationErrors.errors)
                    (errorFacts fullRenameErrors)
                    $"{gameName} incremental localisation rename diagnostics must match full refresh"

                File.Delete(localisationFile)
                let deletionResult = localisation.RemoveLocalisationFile localisationFile
                Expect.contains
                    deletionResult.affectedFiles
                    localisationFile
                    $"{gameName} localisation deletion must invalidate the removed path"
                Expect.isFalse
                    (incrementalGame.AllLoadedLocalisation()
                     |> List.exists (fun value -> value.Contains localisationFile))
                    $"{gameName} localisation deletion must remove the provider"
                let fullAfterDelete = createGame ()
                let affectedAfterDelete = deletionResult.affectedFiles |> Set.ofArray
                let fullDeleteErrors =
                    fullAfterDelete.LocalisationErrors(true, true)
                    |> List.filter (fun error -> affectedAfterDelete.Contains error.range.FileName)
                Expect.equal
                    (errorFacts deletionResult.errors)
                    (errorFacts fullDeleteErrors)
                    $"{gameName} incremental localisation deletion diagnostics must match full refresh"
        finally
            try Directory.Delete(folder, true) with _ -> ()
    )

