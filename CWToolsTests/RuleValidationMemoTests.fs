module RuleValidationMemoTests

open System
open System.Collections.Frozen
open System.IO
open System.Text
open Expecto
open FParsec
open CWTools.Common
open CWTools.Common.STLConstants
open CWTools.Games
open CWTools.Games.Files
open CWTools.Games.Stellaris
open CWTools.Parser
open CWTools.Process
open CWTools.Process.Scopes.STL
open CWTools.Process.Scopes
open CWTools.Process.Scopes.Scopes
open CWTools.Rules
open CWTools.Rules.RulesWrapper
open CWTools.Utilities.Position
open CWTools.Utilities.Utils
open CWTools.Validation
open TestHelpers
open LogCaptureTest

// The memo key pins results to (canonical path, Entity reference, service
// reference, resource epoch, localisation epoch, lazyCreated); these tests
// exercise every key dimension plus the hit-path side effects (addToCache,
// nonSelf/impacted assembly, downstream filters) through the public
// ValidationManager surface. Internal counters only assist verification.

let private memoTestConfig =
    "types = {\n\
         type[test_thing] = {\n\
             path = \"game/common/test_things\"\n\
         }\n\
     }\n\
     test_thing = {\n\
         ## cardinality = 1..1\n\
         required_field = int\n\
     }"

let private makeEntity filepath logicalpath (text: string) =
    match CKParser.parseString text logicalpath with
    | Success(statements, _, _) ->
        let node = STLProcess.shipProcess.ProcessNode () "root" (mkZeroFile logicalpath) statements

        { filepath = filepath
          logicalpath = logicalpath
          rawEntity = node
          entity = node
          validate = true
          entityType = EntityType.Other
          overwrite = Overwrite.No }
    | Failure(error, _, _) -> failwith error

let private computedLazy () =
    lazy (STLComputedData(None, None, None, false, None, None, None))

let private pairOf (entity: Entity) =
    struct (entity, computedLazy ())

let private forcedPair (entity: Entity) =
    let data = computedLazy ()
    data.Force() |> ignore
    struct (entity, data)

let private buildService () =
    let rules, types, _, _, _ =
        parseConfig
            (scopeManager.ParseScope())
            scopeManager.AllScopes
            (scopeManager.ParseScope () "Any")
            scopeManager.ScopeGroups
            "memo.cwt"
            memoTestConfig

    Expect.isNonEmpty types "the memo fixture must contain its test_thing type definition"
    Expect.isNonEmpty rules "the memo fixture must contain its test_thing root rule"

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

type private FakeResources(entities: struct (Entity * Lazy<STLComputedData>) list) =
    interface IResourceAPI<STLComputedData> with
        member _.UpdateFiles = fun _ -> failwith "FakeResources.UpdateFiles is not used by these tests"
        member _.UpdateFile = fun _ -> failwith "FakeResources.UpdateFile is not used by these tests"
        member _.RemoveFile = fun _ -> failwith "FakeResources.RemoveFile is not used by these tests"
        member _.PrepareRemoveFiles _ = failwith "FakeResources.PrepareRemoveFiles is not used by these tests"
        member _.CommitRemoveFiles _ = failwith "FakeResources.CommitRemoveFiles is not used by these tests"
        member _.GetResources = fun () -> []
        member _.ValidatableFiles = fun () -> []
        member _.AllEntities = fun () -> Seq.ofList entities
        member _.ValidatableEntities = fun () -> entities
        member _.ForceRecompute() = ()
        member _.ForceDynamicParameterData(_, _) = 0
        member _.ForceDynamicParameterDataForFiles _ = 0
        member _.ForceRulesDataGenerate() = ()
        member _.GetInlineScriptCallers _ = []
        member _.RefreshInlineScriptCallers _ = []
        member _.PrepareInlineScriptCallers _ = None
        member _.CommitInlineScriptCallers _ = false
        member _.GetFileNames = fun () -> Seq.empty
        member _.GetEntityByFilePath path =
            entities
            |> List.tryFind (fun struct (e, _) ->
                String.Equals(e.filepath, path, StringComparison.OrdinalIgnoreCase))

let private testFileManager () =
    FileManager(
        [| WD { name = "test"; path = "./testfiles/embeddedtest/test" } |],
        Some "",
        scriptFolders,
        "stellaris",
        Encoding.UTF8,
        [||],
        2000000
    )

let private createManager (service: RuleValidationService) (resources: IResourceAPI<STLComputedData>) dynamicValidators batchValidators =
    let settings =
        { validators = batchValidators
          globalValidators = []
          dynamicValidators = dynamicValidators
          experimentalValidators = []
          heavyExperimentalValidators = []
          experimental = false
          fileValidators = []
          globalFileValidators = []
          lookupValidators = []
          globalLookupValidators = []
          lookupFileValidators = []
          scriptedParamsValidators = []
          useRules = true
          debugRulesOnly = false
          localisationValidators = [] }

    let services =
        { resources = resources
          lookup = STLLookup()
          ruleValidationService = Some service
          infoService = None
          localisationKeys = fun () -> [||]
          fileManager = testFileManager () }

    ValidationManager<STLComputedData>(
        settings,
        services,
        (fun _ -> validateLocalisationLazy.Value),
        defaultContext,
        noneContext,
        ErrorCache()
    )

let private singleManager (service: RuleValidationService) (entities: struct (Entity * Lazy<STLComputedData>) list) =
    createManager service (FakeResources entities :> IResourceAPI<STLComputedData>) [] []

let private diagnosticsSignature (errors: CWError list) =
    errors
    |> List.map (fun e ->
        e.code, e.message, e.range.FileName, e.range.Start.Line, e.range.Start.Column, e.range.End.Line, e.range.End.Column)
    |> List.sort

let private badThing () =
    makeEntity "common/test_things/a.txt" "common/test_things/a.txt" "test_thing = { required_field = nope }"

let private goodThing () =
    makeEntity "common/test_things/b.txt" "common/test_things/b.txt" "test_thing = { required_field = 1 }"

[<Tests>]
let ruleResultMemoTests =
    testSequenced
    <| testList
        "rule result memo"
        [ testWithCapturedLogs "memo hit reuses the completed result and keeps diagnostics equivalent"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
              let service = buildService ()
              let directErrors =
                  match service.RuleValidateEntity(badThing ()) with
                  | Invalid(_, errors) -> errors
                  | _ -> []
              Expect.isNonEmpty directErrors "the rule service itself should report the invalid required_field value"
              let entities = [ pairOf (badThing ()); pairOf (goodThing ()) ]
              let manager = singleManager service entities

              let first = manager.ValidateInteractive entities
              Expect.equal (List.length first) 1 "the bad entity should report exactly one rule error"

              let hits, misses, stores, evictions = manager.RuleResultMemoStats
              Expect.equal (hits, misses, stores, evictions) (0L, 2L, 2L, 0L)
                  "first pass should miss and store both entities without evictions"

              // Mirror the editor flow: drop the stale diagnostics, then
              // revalidate the exact same entities and demand identical output.
              manager.InvalidateInteractive entities
              let second = manager.ValidateInteractive entities
              Expect.equal (diagnosticsSignature second) (diagnosticsSignature first)
                  "memo hits must reproduce identical diagnostics"

              let hits2, misses2, stores2, evictions2 = manager.RuleResultMemoStats
              Expect.equal (hits2, misses2, stores2, evictions2) (2L, 2L, 2L, 0L)
                  "the second pass should be served entirely from the memo"

          testWithCapturedLogs "memo key distinguishes forced computed data"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
              let service = buildService ()
              let entity = badThing ()
              let manager = singleManager service [ pairOf entity ]

              let first = manager.ValidateInteractive [ pairOf entity ]
              Expect.equal (List.length first) 1 "unforced lazy should validate with one error"

              // Drop the previously cached diagnostics, mirroring the editor flow.
              manager.InvalidateInteractive [ pairOf entity ]
              let second = manager.ValidateInteractive [ forcedPair entity ]
              Expect.equal (List.length second) 1 "forced lazy should keep validating with one error"
              Expect.equal (diagnosticsSignature second) (diagnosticsSignature first)
                  "lazyCreated transition must not change diagnostics"

              let hits, misses, stores, _ = manager.RuleResultMemoStats
              Expect.equal (hits, misses, stores) (0L, 2L, 2L)
                  "lazyCreated false-to-true must miss and store again"

          testWithCapturedLogs "resource and localisation epochs invalidate memo entries"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
              let service = buildService ()
              let entities = [ pairOf (badThing ()) ]
              let manager = singleManager service entities

              let baseline = manager.ValidateInteractive entities
              Expect.equal (List.length baseline) 1 "baseline should report the rule error"
              manager.InvalidateInteractive entities

              ResourceManagerEager.nextResource () |> ignore
              let afterResource = manager.ValidateInteractive entities
              Expect.equal (diagnosticsSignature afterResource) (diagnosticsSignature baseline)
                  "resource epoch bump must not change diagnostics"
              manager.InvalidateInteractive entities

              ResourceManagerEager.nextLocalisation () |> ignore
              let afterLocalisation = manager.ValidateInteractive entities
              Expect.equal (diagnosticsSignature afterLocalisation) (diagnosticsSignature baseline)
                  "localisation epoch bump must not change diagnostics"

              let hits, misses, stores, _ = manager.RuleResultMemoStats
              Expect.equal (hits, misses, stores) (0L, 3L, 3L)
                  "every epoch bump must miss and store again"

          testWithCapturedLogs "entity or service replacement invalidates memo entries"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
              let service = buildService ()
              let original = badThing ()
              let manager = singleManager service [ pairOf original ]
              manager.ValidateInteractive [ pairOf original ] |> ignore

              // Same path, new Entity record: committing it invalidates the old generation.
              let replacement = badThing ()
              manager.InvalidateInteractive [ pairOf replacement ]
              let afterEntity = manager.ValidateInteractive [ pairOf replacement ]
              Expect.equal (List.length afterEntity) 1 "replaced entity should revalidate with one error"
              Expect.equal manager.RuleResultMemoCount 1 "invalidation must release the replaced entity instead of retaining both generations"

              let hits, misses, stores, _ = manager.RuleResultMemoStats
              Expect.equal (hits, misses, stores) (0L, 2L, 2L)
                  "a replaced entity record must miss and store again"

              // A rebuilt ValidationManager (new service reference) starts empty.
              let rebuiltService = buildService ()
              let rebuiltManager = singleManager rebuiltService [ pairOf original ]
              let afterService = rebuiltManager.ValidateInteractive [ pairOf original ]
              Expect.equal (List.length afterService) 1 "rebuilt manager should revalidate with one error"

              let serviceHits, serviceMisses, serviceStores, _ = rebuiltManager.RuleResultMemoStats
              Expect.equal (serviceHits, serviceMisses, serviceStores) (0L, 1L, 1L)
                  "a rebuilt manager must not reuse the previous service's memo"

          testWithCapturedLogs "memo is bounded and evicts the oldest entries"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
              let service = buildService ()

              let entities =
                  [ for i in 0 .. 1099 ->
                        let path = sprintf "common/test_things/f%04d.txt" i
                        pairOf (makeEntity path path "test_thing = { required_field = 1 }") ]

              let resources = FakeResources entities :> IResourceAPI<STLComputedData>
              let manager = createManager service resources [] []
              manager.ValidateInteractive entities |> ignore

              let hits, misses, stores, evictions = manager.RuleResultMemoStats
              Expect.equal (hits, misses) (0L, 1100L) "the first pass should miss everywhere"
              Expect.equal stores 1100L "every validated entity should be stored"
              Expect.equal evictions 76L "the LRU should evict the 76 entries beyond capacity 1024"

              // The oldest entity was evicted; the newest is still cached.
              manager.ValidateInteractive [ entities.Head ] |> ignore
              let _, missesAfterOldest, _, _ = manager.RuleResultMemoStats
              Expect.equal missesAfterOldest 1101L "an evicted entry must miss again"

              manager.ValidateInteractive [ entities |> List.last ] |> ignore
              let hitsAfterNewest, _, _, _ = manager.RuleResultMemoStats
              Expect.equal hitsAfterNewest 1L "the newest entry should still hit"

          testWithCapturedLogs "cleanup drops memo entries for removed files"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
              let service = buildService ()
              let keep = makeEntity "common/test_things/keep.txt" "common/test_things/keep.txt" "test_thing = { required_field = nope }"
              let drop = makeEntity "common/test_things/drop.txt" "common/test_things/drop.txt" "test_thing = { required_field = nope }"
              let entities = [ pairOf keep; pairOf drop ]
              let manager = singleManager service entities
              manager.ValidateInteractive entities |> ignore

              manager.Cleanup(Set.ofList [ "common/test_things/keep.txt" ])

              manager.ValidateInteractive [ pairOf keep ] |> ignore
              manager.ValidateInteractive [ pairOf drop ] |> ignore

              let hits, misses, stores, _ = manager.RuleResultMemoStats
              Expect.equal (hits, misses, stores) (1L, 3L, 3L)
                  "cleanup must drop only the removed file's entry"

          testWithCapturedLogs "cancelled validation stores nothing"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
              let service = buildService ()
              let entity = badThing ()
              let manager = singleManager service [ pairOf entity ]

              // Flip the cancellation check mid-flight so the cancellable rule
              // API aborts the run before any complete result exists.
              let mutable calls = 0
              let check () =
                  calls <- calls + 1
                  calls >= 3

              let cancelled = manager.ValidateLocalCancellable([ pairOf entity ], check)
              Expect.isTrue cancelled.IsNone "a superseded run must surface as cancellation"

              let hits, misses, stores, _ = manager.RuleResultMemoStats
              Expect.equal (hits, misses, stores) (0L, 1L, 0L)
                  "a cancelled run must not be stored"

              let recomputed = manager.ValidateInteractive [ pairOf entity ]
              Expect.equal (List.length recomputed) 1 "the entity must revalidate normally afterwards"

              let hits2, misses2, stores2, _ = manager.RuleResultMemoStats
              Expect.equal (hits2, misses2, stores2) (0L, 2L, 1L)
                  "the post-cancel run must miss and store fresh"

          testWithCapturedLogs "cross-file errors survive on memo hit"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
              let service = buildService ()

              // The error is produced while validating b.txt but located in
              // a.txt, so it only surfaces through the impacted-file assembly.
              let crossFile =
                  makeEntity "common/test_things/b.txt" "common/test_things/a.txt" "test_thing = { required_field = nope }"

              let entities = [ pairOf crossFile ]
              let manager = singleManager service entities

              let first = manager.ValidateInteractive entities
              Expect.equal (List.length first) 1 "the cross-file error should be reported once"

              manager.InvalidateInteractive entities
              let second = manager.ValidateInteractive entities
              Expect.equal (diagnosticsSignature second) (diagnosticsSignature first)
                  "a memo hit must still run addToCache and the impacted assembly"

              let hits, misses, stores, _ = manager.RuleResultMemoStats
              Expect.equal (hits, misses, stores) (1L, 1L, 1L)
                  "the second pass should be a single memo hit"

          testWithCapturedLogs "batch validators still run when the memo hits"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
              let service = buildService ()
              let entities = [ pairOf (badThing ()) ]
              let resources = FakeResources entities :> IResourceAPI<STLComputedData>

              let mutable batchRuns = 0

              let batchValidator (changedEntities: EntitySet<STLComputedData>) =
                  batchRuns <- batchRuns + 1
                  OK

              let manager = createManager service resources [] [ batchValidator, "batch" ]

              let first, _ = manager.ValidateLocal entities
              Expect.equal (List.length first) 1 "the first pass should report the rule error"
              Expect.equal batchRuns 1 "the batch validator should run on the first pass"

              manager.InvalidateInteractive entities

              let second, _ = manager.ValidateLocal entities
              Expect.equal (diagnosticsSignature second) (diagnosticsSignature first)
                  "a memo hit must keep the published diagnostics"
              Expect.equal batchRuns 2 "batch validators must still run when the memo hits"

              let hits, misses, stores, _ = manager.RuleResultMemoStats
              Expect.equal (hits, misses, stores) (1L, 1L, 1L)
                  "the second pass should be a single memo hit"

          testWithCapturedLogs "dynamic workspace snapshot is reused per epoch and dynamic validators run per batch"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
              let service = buildService ()
              let workspace = goodThing ()
              let resources = FakeResources [ pairOf workspace ] :> IResourceAPI<STLComputedData>

              let captured = ResizeArray<struct (EntitySet<STLComputedData> * EntitySet<STLComputedData>)>()

              let dynamicValidator (workspaceEntities: EntitySet<STLComputedData>) (changedEntities: EntitySet<STLComputedData>) =
                  captured.Add(struct (workspaceEntities, changedEntities))
                  OK

              let manager = createManager service resources [ dynamicValidator, "dyn" ] []
              let firstChanged = pairOf (badThing ())
              let secondChanged = pairOf (badThing ())

              match manager.ValidateDynamicLocalCancellable([ firstChanged ], fun () -> false) with
              | None -> failtest "the first dynamic batch should validate"
              | Some _ -> ()

              match manager.ValidateDynamicLocalCancellable([ secondChanged ], fun () -> false) with
              | None -> failtest "the second dynamic batch should validate"
              | Some _ -> ()

              Expect.equal captured.Count 2 "dynamic validators must run once per batch"

              let struct (firstWorkspace, firstChangedSet) = captured.[0]
              let struct (secondWorkspace, secondChangedSet) = captured.[1]
              Expect.isTrue (Object.ReferenceEquals(firstWorkspace, secondWorkspace))
                  "an unchanged workspace should reuse one EntitySet snapshot"
              Expect.isFalse (Object.ReferenceEquals(firstChangedSet, secondChangedSet))
                  "changedEntities must stay per-batch"

              let builds, reuses = manager.DynamicWorkspaceSnapshotStats
              Expect.equal (builds, reuses) (1L, 1L) "one build and one reuse at a stable epoch"

              ResourceManagerEager.nextResource () |> ignore

              match manager.ValidateDynamicLocalCancellable([ pairOf (badThing ()) ], fun () -> false) with
              | None -> failtest "the third dynamic batch should validate"
              | Some _ -> ()

              let builds2, reuses2 = manager.DynamicWorkspaceSnapshotStats
              Expect.equal (builds2, reuses2) (2L, 1L) "a resource epoch bump must rebuild the snapshot"

          testWithCapturedLogs "save validation reuses the memo without changing published diagnostics"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
              let folder = Path.Combine(Path.GetTempPath(), "cwtools-rule-memo-" + Guid.NewGuid().ToString("N"))
              let thingDir = Path.Combine(folder, "common", "test_things")
              let filename = Path.Combine(thingDir, "a.txt")

              try
                  Directory.CreateDirectory thingDir |> ignore
                  File.WriteAllText(filename, "test_thing = { required_field = nope }\n")

                  let settings =
                      { emptyStellarisSettings folder with
                          rules =
                              Some
                                  { ruleFiles = [ "memo.cwt", memoTestConfig ]
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = new STLGame(settings) :> IGame<STLComputedData>

                  let first = stl.ValidateFile false filename
                  Expect.isNonEmpty first "the bad file should report the invalid required_field value"

                  let second = stl.ValidateFile false filename
                  // Re-validating without an edit re-surfaces self errors through
                  // the impacted-file assembly by pre-existing design, so compare
                  // the distinct diagnostic sets: a memo hit must add none and
                  // drop none.
                  Expect.equal (diagnosticsSignature second |> List.distinct) (diagnosticsSignature first |> List.distinct)
                      "a memo-hit save validation must publish identical diagnostics"

                  // Editing the file replaces the entity and must not be served
                  // from the memo.
                  stl.UpdateFile false filename (Some "test_thing = { required_field = 1 }\n") |> ignore
                  let third = stl.ValidateFile false filename
                  let remainingRuleErrors =
                      third |> List.filter (fun e -> e.message.Contains("required_field"))
                  Expect.isEmpty remainingRuleErrors "the fixed file must revalidate without the rule error"
              finally
                  if File.Exists filename then
                      File.Delete filename

                  if Directory.Exists thingDir then
                      Directory.Delete thingDir

                  let commonDir = Path.Combine(folder, "common")

                  if Directory.Exists commonDir then
                      Directory.Delete commonDir

                  if Directory.Exists folder then
                      Directory.Delete folder
        ]
