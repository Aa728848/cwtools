module Tests
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



let logger = Log.create "MyTests"
logDiag <- logger.logSimple << (event LogLevel.Verbose)
logInfo <- logger.logSimple << (event LogLevel.Info)
logWarning <- logger.logSimple << (event LogLevel.Warn)
logError <- logger.logSimple << (event LogLevel.Error)

Encoding.RegisterProvider(CodePagesEncodingProvider.Instance)

CultureInfo.DefaultThreadCurrentCulture <- CultureInfo("ru-RU")
CultureInfo.DefaultThreadCurrentUICulture <- CultureInfo("ru-RU")
Thread.CurrentThread.CurrentCulture <- CultureInfo("ru-RU")
Thread.CurrentThread.CurrentUICulture <- CultureInfo("ru-RU")
// CWTools.Utilities.Utils.loglevel <- CWTools.Utilities.Utils.LogLevel.Verbose

let getAllTestLocs node =
    let fNode =
        (fun (x: Node) (req, notreq) ->
            let required =
                x.Values
                |> List.filter (fun l -> l.Value.ToRawString() = "test_required")
                |> List.map (fun l -> l.Position)

            let notrequired =
                x.Values
                |> List.filter (fun l -> l.Value.ToRawString() = "test_optional")
                |> List.map (fun l -> l.Position)

            required @ req, notrequired @ notreq)

    let fCombine = (fun (r, n) (r2, n2) -> (r @ r2, n @ n2))
    node |> (foldNode2 fNode fCombine ([], []))

let getLocTestInfo node =
    let req, noreq = getAllTestLocs node

    let comments =
        getNodeComments node
        |> List.filter (fun (_, c) -> not (List.isEmpty c))
        |> List.collect (fun (f, c) -> c |> List.map (fun cc -> f, cc))
        |> List.map fst

    req, noreq, comments

let locErrorCodes =
    [ "CW225"
      "CW226"
      "CW254"
      "CW255"
      "CW256"
      "CW257"
      "CW258"
      "CW259"
      "CW260" ]

[<Tests>]
let tests =
    testList
        "localisation"
        [ testWithCapturedLogs "no loc"
          <| fun () ->
              let configtext =
                  [ "./testfiles/localisationtests/test.cwt", File.ReadAllText "./testfiles/localisationtests/test.cwt" ]

              let configtext =
                  ("./testfiles/localisationtests/localisation.cwt",
                   File.ReadAllText "./testfiles/localisationtests/localisation.cwt")
                  :: configtext

              let settings = emptyStellarisSettings "./testfiles/localisationtests/gamefiles"

              let settings =
                  { settings with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = false
                                debugRulesOnly = false
                                debugMode = false } }
              // UtilityParser.initializeScopes None (Some defaultScopeInputs)
              let stl = STLGame(settings) :> IGame<STLComputedData>
              let parseErrors = stl.ParserErrors()
              let errors = stl.LocalisationErrors(true, true) |> List.map (fun e -> e.range)
              let entities = stl.AllEntities() |> Seq.toList

              let testLocKeys =
                  entities |> List.map (fun struct (e, _) -> e.filepath, getLocTestInfo e.entity)

              let _ =
                  entities
                  |> List.collect (fun struct (e, _) -> getNodeComments e.entity)
                  |> List.map fst

              logInfo
                  $"%A{entities
                       |> List.head
                       |> (fun struct (e, _) -> api.prettyPrintStatement e.entity.ToRaw)}"

              Expect.isEmpty
                  parseErrors
                  (parseErrors
                   |> List.tryHead
                   |> Option.map (sprintf "%A")
                   |> Option.defaultValue "")
              // yield testWithCapturedLogs "parse" <| fun () -> Expect.isEmpty parseErrors (parseErrors |> List.tryHead |> Option.map (sprintf "%A") |> Option.defaultValue "")
              Expect.isEmpty
                  (stl.ParserErrors())
                  (stl.ParserErrors()
                   |> List.tryHead
                   |> Option.map (sprintf "%A")
                   |> Option.defaultValue "")
              // yield testWithCapturedLogs "parse2" <| fun () -> Expect.isEmpty (stl.ParserErrors()) (stl.ParserErrors() |> List.tryHead |> Option.map (sprintf "%A") |> Option.defaultValue "")
              //eprintfn "%A" testLocKeys
              // eprintfn "%A" entities
              //eprintfn "%A" errors
              // eprintfn "%A" stl.LocalisationErrors
              let inner (file, (req: range list, noreq: range list, nodekeys: range list)) =
                  let extra = noreq |> List.filter (fun r -> errors |> List.contains r)
                  let expected = req @ nodekeys
                  let fileErrors = errors |> List.filter (fun f -> f.FileName = file)
                  let missing = remove_all expected fileErrors
                  let extras = remove_all fileErrors expected
                  Expect.isEmpty missing $"Following lines are expected to have an error %A{missing}"
                  Expect.isEmpty extras $"Following lines are not expected to have an error %A{extras}"
                  Expect.isEmpty extra $"Incorrect required %s{file}"

              testLocKeys |> List.iter (fun (f, t) -> inner (f, t))
          // yield! testLocKeys |> List.map (fun (f, t) -> testWithCapturedLogs (f.ToString()) <| fun () -> inner (f, t))
          testWithCapturedLogs "with loc"
          <| fun () ->
              let configtext =
                  [ "./testfiles/localisationtests/test.cwt", File.ReadAllText "./testfiles/localisationtests/test.cwt" ]

              let configtext =
                  ("./testfiles/localisationtests/localisation.cwt",
                   File.ReadAllText "./testfiles/localisationtests/localisation.cwt")
                  :: configtext

              let locfiles =
                  "localisation/l_english.yml",
                  File.ReadAllText("./testfiles/localisationtests/localisation/l_english.yml")
              // let locCommands = STLParser.loadLocCommands "./testfiles/localisationtests/test.cwt" (File.ReadAllText "./testfiles/localisationtests/test.cwt")
              // UtilityParser.initializeScopes None (Some defaultScopeInputs)

              let settings = emptyStellarisSettings "./testfiles/localisationtests/gamefiles"

              let settings =
                  { settings with
                      embedded = FromConfig([ locfiles ], [])
                      validation =
                          { settings.validation with
                              langs = [| STL STLLang.English; STL STLLang.German |] }
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = false
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let parseErrors = stl.ParserErrors()

              Expect.isEmpty
                  parseErrors
                  (parseErrors
                   |> List.tryHead
                   |> Option.map (sprintf "%A")
                   |> Option.defaultValue "")
              // yield testWithCapturedLogs "parse" <| fun () -> Expect.isEmpty parseErrors (parseErrors |> List.tryHead |> Option.map (sprintf "%A") |> Option.defaultValue "")

              let errors = stl.LocalisationErrors(true, true) |> List.map (fun e -> e.range)

              let testLocKeys =
                  stl.AllEntities()
                  |> Seq.map (fun struct (e, _) -> e.filepath, getLocTestInfo e.entity)

              let inner (file, (req: range list, noreq: range list, _: range list)) =
                  let missing = req |> List.filter (fun r -> not (errors |> List.contains r))
                  let extra = noreq |> List.filter (fun r -> errors |> List.contains r)
                  Expect.isEmpty missing $"Missing required despite having key %s{file}"
                  Expect.isEmpty extra $"Incorrect required %s{file}"

              testLocKeys |> Seq.iter (fun (f, t) -> inner (f, t))
              // yield! testLocKeys |> List.map (fun (f, t) -> testWithCapturedLogs (f.ToString()) <| fun () -> inner (f, t))
              // eprintfn "%A" (stl.LocalisationErrors(true))
              let globalLocError =
                  stl.LocalisationErrors(true, true)
                  |> List.filter (fun e -> List.contains e.code locErrorCodes)

              Expect.hasCountOf globalLocError 9u (fun _ -> true) $"wrong number of errors %A{globalLocError}"
          // yield testWithCapturedLogs "globalLoc" <| fun () ->
          // Expect.hasCountOf globalLocError 10u (fun f -> true) (sprintf "wrong number of errors %A" globalLocError)
          testWithCapturedLogs "loc references are case-sensitive"
          <| fun () ->
              let keys = LocKeySet(StringComparer.Ordinal)
              keys.Add "CASE_MISMATCH_SELF_REF" |> ignore

              let entry =
                  { LocEntry.key = "CASE_MISMATCH_SELF_REF"
                    value = None
                    desc = "\"$case_mismatch_self_ref$\""
                    position = range.Zero
                    refs = [ "case_mismatch_self_ref" ]
                    commands = []
                    jominiCommands = []
                    scopes = []
                    errorRanges = None }

              let result =
                  CWTools.Validation.LocalisationString.validateProcessedLocalisationBase
                      []
                      Set.empty
                      [| STL STLLang.English, keys |]
                      [ STL STLLang.English, Map.ofList [ entry.key, entry ] ]

              let errors =
                  match result with
                  | OK -> []
                  | Invalid(_, es) -> es

              Expect.exists
                  errors
                  (fun e -> e.code = "CW225" && e.message.Contains("case_mismatch_self_ref"))
                  "case-mismatched localisation references should be unresolved"

              Expect.isFalse
                  (errors |> List.exists (fun e -> e.code = "CW259"))
                  "case-mismatched localisation references must not be treated as self-references"

          testWithCapturedLogs "incremental key add revalidates referencing files exactly"
          <| fun () ->
              let configtext =
                  [ "./testfiles/localisationtests/test.cwt",
                    (File.ReadAllText "./testfiles/localisationtests/test.cwt")
                        .Replace("event = {", "event = {" + Environment.NewLine + "    desc = localisation")
                    "./testfiles/localisationtests/localisation.cwt",
                    File.ReadAllText "./testfiles/localisationtests/localisation.cwt" ]
              let embeddedLocPath = Path.GetFullPath("./testfiles/localisationtests/localisation/l_english.yml")
              let originalLoc = File.ReadAllText embeddedLocPath
              let settings = emptyStellarisSettings "./testfiles/localisationtests/gamefiles"
              let settings =
                  { settings with
                      embedded = FromConfig([ embeddedLocPath, originalLoc ], [])
                      validation =
                          { settings.validation with
                              langs = [| STL STLLang.English |] }
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = false
                                debugRulesOnly = false
                                debugMode = false } }
              let stl = STLGame(settings) :> IGame<STLComputedData>
              let incremental = stl :?> IIncrementalLocalisation
              let locPath =
                  stl.AllFiles()
                  |> List.pick (function
                      | FileWithContentResource(_, file) when file.filetext.Contains("test_required_desc") -> Some file.filepath
                      | _ -> None)
              let updatedLoc = originalLoc + Environment.NewLine + " test:0 \"resolved\"" + Environment.NewLine
              stl.UpdateFile false locPath (Some updatedLoc) |> ignore
              Expect.equal
                  (incremental.PeekLocalisationDelta "before-baseline")
                  (Result.Ok None)
                  "peek must wait for localisation caches"
              Expect.equal
                  (incremental.PeekLocalisationDelta "before-baseline")
                  (Result.Ok None)
                  "repeated peek must remain empty before localisation caches are ready"
              Expect.isNone
                  (incremental.TakeLocalisationDelta())
                  "TakeDelta must wait for localisation caches"
              stl.LocalisationErrors(true, true) |> ignore
              let firstPeek = incremental.PeekLocalisationDelta "validation"
              let firstBatch =
                  match firstPeek with
                  | Result.Ok(Some batch) -> batch
                  | other -> failtestf "localisation update should publish an incremental delta, got %A" other
              let repeated = incremental.PeekLocalisationDelta "validation"
              Expect.equal repeated firstPeek "peek must be repeatable for the active owner"
              Expect.isTrue
                  (firstBatch.delta.changedKeys = Array.sort firstBatch.delta.changedKeys)
                  "detached changed-key facts must be sorted"
              Expect.isTrue
                  (firstBatch.delta.affectedLocalisationFiles = Array.sort firstBatch.delta.affectedLocalisationFiles)
                  "detached affected-file replacements must be sorted"
              Expect.contains firstBatch.delta.changedKeys "test" "added key should be present in the delta"

              let secondLoc = updatedLoc + " another_test:0 \"newer\"" + Environment.NewLine
              stl.UpdateFile false locPath (Some secondLoc) |> ignore
              Expect.equal
                  (incremental.PeekLocalisationDelta "validation")
                  firstPeek
                  "newer revisions must not change an active prefix"
              Expect.equal
                  (incremental.PeekLocalisationDelta "other")
                  (Result.Error LocalisationDeltaCursorError.Stale)
                  "a concurrent owner must be stale"
              let wrongPrefix = { firstBatch.cursor with throughRevision = firstBatch.cursor.throughRevision + 1L }
              Expect.equal
                  (incremental.AckLocalisationDelta wrongPrefix)
                  LocalisationDeltaAckResult.Stale
                  "ack must match the exact owner and prefix"
              Expect.equal
                  (incremental.AckLocalisationDelta firstBatch.cursor)
                  LocalisationDeltaAckResult.Acknowledged
                  "the exact prefix should be acknowledged"
              Expect.equal
                  (incremental.AckLocalisationDelta firstBatch.cursor)
                  LocalisationDeltaAckResult.AlreadyCompleted
                  "repeating an exact ack should report completion"

              let newerPeek = incremental.PeekLocalisationDelta "shim-parity"
              let newerBatch =
                  match newerPeek with
                  | Result.Ok(Some batch) -> batch
                  | other -> failtestf "the concurrent revision must remain pending, got %A" other
              Expect.contains newerBatch.delta.changedKeys "another_test" "prefix ack must retain newer facts"
              incremental.DiscardLocalisationDelta newerBatch.cursor
              incremental.DiscardLocalisationDelta newerBatch.cursor
              let delta = incremental.TakeLocalisationDelta()
              Expect.isSome delta "the compatibility shim should consume a discarded batch"
              Expect.equal delta.Value newerBatch.delta "TakeDelta must preserve peek plus ack payload behavior"
              Expect.equal
                  (incremental.PeekLocalisationDelta "after-shim")
                  (Result.Ok None)
                  "TakeDelta must acknowledge the materialised prefix"
              let result = incremental.ValidateLocalisationDelta firstBatch.delta
              let eventFile =
                  stl.AllEntities()
                  |> Seq.map (fun struct (entity, _) -> entity.filepath)
                  |> Seq.find (fun filepath -> filepath.EndsWith("test_events.txt"))
              Expect.contains
                  result.affectedFiles
                  eventFile
                  "a script file referencing the added key must be revalidated"
              Expect.isFalse
                  (result.errors
                   |> List.exists (fun error -> error.range.FileName = eventFile && error.data = Some "test"))
                  "the incremental pass must remove the resolved missing-localisation diagnostic"

              let affected = result.affectedFiles |> Set.ofArray
              let errorFacts (errors: CWError list) =
                  errors
                  |> List.filter (fun error -> affected.Contains error.range.FileName)
                  |> List.map (fun error ->
                      error.code,
                      error.range.FileName,
                      error.range.StartLine,
                      error.range.StartColumn,
                      error.message)
                  |> Set.ofList
              let fullFacts = stl.LocalisationErrors(true, true) |> errorFacts
              Expect.equal
                  (errorFacts result.errors)
                  fullFacts
                  "incremental diagnostics for affected files must equal a full localisation pass"

          testWithCapturedLogs "staged localisation prepare is pure and commit is guarded"
          <| fun () ->
              let configtext =
                  [ "./testfiles/localisationtests/test.cwt", File.ReadAllText "./testfiles/localisationtests/test.cwt"
                    "./testfiles/localisationtests/localisation.cwt", File.ReadAllText "./testfiles/localisationtests/localisation.cwt" ]
              let locPath = Path.GetFullPath("./testfiles/localisationtests/localisation/l_english.yml")
              let originalLoc = File.ReadAllText locPath
              let settings = emptyStellarisSettings "./testfiles/localisationtests/gamefiles"
              let settings =
                  { settings with
                      embedded = FromConfig([ locPath, originalLoc ], [])
                      validation = { settings.validation with langs = [| STL STLLang.English |] }
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = false
                                debugRulesOnly = false
                                debugMode = false } }
              let concrete = STLGame(settings)
              let stl = concrete :> IGame<STLComputedData>
              let incremental = stl :?> IIncrementalLocalisation
              let beforeReady = incremental.PrepareLocalisationRefresh "not-ready"
              Expect.equal beforeReady (Result.Ok None) "prepare must require ready localisation caches"
              stl.LocalisationErrors(true, true) |> ignore
              let updated = String.concat Environment.NewLine [ originalLoc; " staged_key:0 \"ready\""; "" ]
              stl.UpdateFile false locPath (Some updated) |> ignore
              let peek = incremental.PeekLocalisationDelta "staged"
              let cursor =
                  match peek with
                  | Result.Ok(Some batch) -> batch.cursor
                  | other -> failtestf "staged update should have a cursor, got %A" other
              let beforePrepare = concrete.IncrementalLocalisationValidationCount
              let beforeState = concrete.LocalisationPublicationIdentity
              let beforeGeneration, _, _ = concrete.LocalisationPublicationStats
              let firstStage =
                  match incremental.PrepareLocalisationRefresh "staged" with
                  | Result.Ok(Some value) -> value
                  | other -> failtestf "staged update should prepare, got %A" other
              stl.RefreshCaches()
              Expect.equal
                  (incremental.TryCommitLocalisationRefresh firstStage)
                  StagedLocalisationCommitResult.Superseded
                  "a validation manager refresh must supersede a prepared candidate"
              Expect.isTrue
                  (Object.ReferenceEquals(beforeState, concrete.LocalisationPublicationIdentity))
                  "a superseded candidate must not publish state"
              let stage =
                  match incremental.PrepareLocalisationRefresh "staged" with
                  | Result.Ok(Some value) -> value
                  | other -> failtestf "staged update should reprepare, got %A" other
              Expect.equal
                  (incremental.PeekLocalisationDelta "staged")
                  peek
                  "prepare must neither acknowledge nor alter the active prefix"
              Expect.isTrue
                  (Object.ReferenceEquals(beforeState, concrete.LocalisationPublicationIdentity))
                  "prepare must preserve the live publication state identity"
              Expect.isTrue
                  (concrete.LocalisationManager.CanAckDelta cursor)
                  "the exact active owner and prefix must be acknowledgeable"
              let wrongOwner = { cursor with owner = cursor.owner + "-other" }
              let wrongPrefix = { cursor with throughRevision = cursor.throughRevision + 1L }
              Expect.isFalse
                  (concrete.LocalisationManager.CanAckDelta wrongOwner)
                  "a different owner must not be acknowledgeable"
              Expect.isFalse
                  (concrete.LocalisationManager.CanAckDelta wrongPrefix)
                  "a different prefix must not be acknowledgeable"
              let mutable staleCallbackCalled = false
              Expect.equal
                  (concrete.LocalisationManager.TryCommitDelta(wrongPrefix, fun () -> staleCallbackCalled <- true))
                  LocalisationDeltaAckResult.Stale
                  "a stale transform must be rejected"
              Expect.isFalse staleCallbackCalled "a stale transform must not invoke publication"
              let callbackFailure = InvalidOperationException("publication failed")
              try
                  concrete.LocalisationManager.TryCommitDelta(cursor, fun () -> raise callbackFailure)
                  |> ignore
                  failtest "the publication exception must escape"
              with ex ->
                  Expect.equal ex callbackFailure "the publication exception must escape unchanged"
              Expect.isTrue
                  (concrete.LocalisationManager.CanAckDelta cursor)
                  "a throwing callback must leave the exact prefix active"
              Expect.equal
                  (incremental.PeekLocalisationDelta "staged")
                  peek
                  "a throwing callback must not acknowledge or alter the journal"
              let repeated =
                  match incremental.PrepareLocalisationRefresh "staged" with
                  | Result.Ok(Some value) -> value
                  | other -> failtestf "repeated prepare should remain possible, got %A" other
              Expect.equal
                  concrete.IncrementalLocalisationValidationCount
                  (beforePrepare + 3)
                  "each prepare validates exactly once before commit"
              let suffix = updated + " staged_suffix:0 \"newer\"" + Environment.NewLine
              let currentLocResource =
                  stl.AllFiles()
                  |> List.pick (function
                      | FileWithContentResource(_, file) when file.filepath = locPath -> Some file
                      | _ -> None)
              concrete.LocalisationManager.UpdateLocalisationFile { currentLocResource with filetext = suffix }
              let assertRetryableFailure hookName exceptionValue invoke =
                  try
                      invoke ()
                      failtestf "%s fault must escape" hookName
                  with ex ->
                      Expect.equal ex exceptionValue (hookName + " fault must escape unchanged")
                  Expect.isFalse stage.IsCompleted (hookName + " fault must leave the stage retryable")
                  Expect.isTrue
                      (concrete.LocalisationManager.CanAckDelta cursor)
                      (hookName + " fault must leave the exact journal prefix active")

              let projectionFailure = InvalidOperationException("projection failed")
              concrete.LocalisationManager.BeforeDeltaProjection <- fun () -> raise projectionFailure
              assertRetryableFailure
                  "projection"
                  projectionFailure
                  (fun () -> incremental.TryCommitLocalisationRefresh stage |> ignore)
              concrete.LocalisationManager.BeforeDeltaProjection <- ignore
              Expect.isTrue
                  (Object.ReferenceEquals(beforeState, concrete.LocalisationPublicationIdentity))
                  "projection failure must not publish state"

              let callbackFailure = InvalidOperationException("callback failed before swap")
              concrete.LocalisationManager.BeforeDeltaPublish <- fun () -> raise callbackFailure
              assertRetryableFailure
                  "pre-callback"
                  callbackFailure
                  (fun () -> incremental.TryCommitLocalisationRefresh stage |> ignore)
              concrete.LocalisationManager.BeforeDeltaPublish <- ignore
              Expect.isTrue
                  (Object.ReferenceEquals(beforeState, concrete.LocalisationPublicationIdentity))
                  "failure before the callback must not publish state"
              Expect.equal
                  concrete.LocalisationManager.localisationErrors
                  (Some stage.BaseState.flattenedLocalErrors)
                  "compatibility local errors must be getter-backed by the canonical snapshot"
              Expect.equal
                  concrete.LocalisationManager.globalLocalisationErrors
                  (Some stage.BaseState.flattenedGlobalErrors)
                  "compatibility global errors must be getter-backed by the canonical snapshot"

              let journalFailure = InvalidOperationException("journal failed after callback")
              concrete.LocalisationManager.AfterDeltaPublish <- fun () -> raise journalFailure
              assertRetryableFailure
                  "post-callback journal"
                  journalFailure
                  (fun () -> incremental.TryCommitLocalisationRefresh stage |> ignore)
              concrete.LocalisationManager.AfterDeltaPublish <- ignore
              let candidateState = concrete.LocalisationPublicationIdentity
              Expect.isFalse
                  (Object.ReferenceEquals(beforeState, candidateState))
                  "a post-callback fault occurs after the canonical swap"
              let publishedCandidate = stage.CandidateState |> Option.get
              Expect.equal
                  concrete.LocalisationManager.localisationErrors
                  (Some publishedCandidate.flattenedLocalErrors)
                  "compatibility local errors must follow the swapped canonical snapshot"
              Expect.equal
                  concrete.LocalisationManager.globalLocalisationErrors
                  (Some publishedCandidate.flattenedGlobalErrors)
                  "compatibility global errors must follow the swapped canonical snapshot"

              match incremental.TryCommitLocalisationRefresh stage with
              | StagedLocalisationCommitResult.Committed result ->
                  Expect.isTrue
                      (result.affectedFiles = Array.sort result.affectedFiles)
                      "staged replacements must be deterministic"
                  Expect.isEmpty result.localisationErrorReplacements "explicit empty local replacements must clear affected paths"
                  Expect.isEmpty result.globalLocalisationErrorReplacements "explicit empty global replacements must clear affected paths"
              | other -> failtestf "retry after fault should commit the exact staged prefix, got %A" other
              Expect.isTrue
                  (Object.ReferenceEquals(candidateState, concrete.LocalisationPublicationIdentity))
                  "retry after a post-callback fault must reuse the published candidate"
              let committedState = concrete.LocalisationPublicationIdentity
              let committedGeneration, _, _ = concrete.LocalisationPublicationStats
              Expect.isFalse
                  (Object.ReferenceEquals(beforeState, committedState))
                  "commit must atomically replace the publication state identity"
              Expect.equal committedGeneration (beforeGeneration + 1L) "commit must advance publication generation once"
              Expect.equal
                  concrete.IncrementalLocalisationValidationCount
                  (beforePrepare + 3)
                  "commit must not run validation"
              let suffixBatch =
                  match incremental.PeekLocalisationDelta "staged" with
                  | Result.Ok(Some batch) -> batch
                  | other -> failtestf "a newer suffix must remain peekable after prefix commit, got %A" other
              Expect.equal
                  suffixBatch.cursor.fromRevision
                  (cursor.throughRevision + 1L)
                  "the retained suffix must begin immediately after the committed prefix"
              Expect.equal
                  suffixBatch.cursor.throughRevision
                  suffixBatch.cursor.fromRevision
                  "the retained suffix must contain exactly the one newer journal revision"
              Expect.equal
                  suffixBatch.delta.changedKeys
                  [| "required"; "staged_key"; "staged_suffix"; "test_required_desc" |]
                  "prefix commit must retain exactly the newer revision's key facts"
              Expect.equal
                  suffixBatch.delta.affectedLocalisationFiles
                  [| locPath |]
                  "prefix commit must retain exactly the newer file facts"
              Expect.isTrue suffixBatch.delta.semanticChanged "the retained suffix must preserve its semantic change"
              use callbackStarted = new ManualResetEventSlim(false)
              use releaseCallback = new ManualResetEventSlim(false)
              let mutable publishCount = 0
              let transformTask =
                  System.Threading.Tasks.Task.Run(fun () ->
                      concrete.LocalisationManager.TryCommitDelta(
                          suffixBatch.cursor,
                          fun () ->
                              publishCount <- publishCount + 1
                              callbackStarted.Set()
                              releaseCallback.Wait()
                      ))
              Expect.isTrue (callbackStarted.Wait(1000)) "the transform callback must run synchronously"
              let concurrent = suffix + " staged_concurrent:0 \"queued\"" + Environment.NewLine
              let writerTask =
                  System.Threading.Tasks.Task.Run(fun () ->
                      concrete.LocalisationManager.UpdateLocalisationFile
                          { currentLocResource with filetext = concurrent })
              Expect.isFalse
                  (writerTask.Wait(50))
                  "a concurrent journal writer must wait until callback and prefix removal complete"
              releaseCallback.Set()
              Expect.equal
                  transformTask.Result
                  LocalisationDeltaAckResult.Acknowledged
                  "the callback and exact prefix removal must complete atomically"
              Expect.equal publishCount 1 "an exact commit must publish exactly once"
              Expect.isTrue (writerTask.Wait(1000)) "the queued writer must resume after acknowledgement"
              Expect.isFalse
                  (concrete.LocalisationManager.CanAckDelta suffixBatch.cursor)
                  "the acknowledged prefix must no longer be active"
              let concurrentBatch =
                  match incremental.PeekLocalisationDelta "concurrent-suffix" with
                  | Result.Ok(Some batch) -> batch
                  | other -> failtestf "the concurrent writer must remain as a newer suffix, got %A" other
              Expect.isTrue
                  (concurrentBatch.cursor.fromRevision > suffixBatch.cursor.throughRevision)
                  "the serialized concurrent writer must receive a newer revision"
              incremental.DiscardLocalisationDelta concurrentBatch.cursor
              Expect.equal
                  (incremental.TryCommitLocalisationRefresh stage)
                  StagedLocalisationCommitResult.AlreadyCompleted
                  "a committed stage is single-use"
              Expect.equal
                  (incremental.TryCommitLocalisationRefresh repeated)
                  StagedLocalisationCommitResult.Superseded
                  "a second stage for an acknowledged cursor is superseded"
              Expect.isTrue
                  (Object.ReferenceEquals(committedState, concrete.LocalisationPublicationIdentity))
                  "a stale stage must not invoke publication"

              let second = suffix + " staged_second:0 \"ready\"" + Environment.NewLine
              stl.UpdateFile false locPath (Some second) |> ignore
              let staleCursor =
                  match incremental.PeekLocalisationDelta "cursor-stale" with
                  | Result.Ok(Some batch) -> batch.cursor
                  | other -> failtestf "second staged update should have a cursor, got %A" other
              let cursorStage =
                  match incremental.PrepareLocalisationRefresh "cursor-stale" with
                  | Result.Ok(Some value) -> value
                  | other -> failtestf "second staged update should prepare, got %A" other
              let cursorState = concrete.LocalisationPublicationIdentity
              Expect.equal
                  (incremental.AckLocalisationDelta staleCursor)
                  LocalisationDeltaAckResult.Acknowledged
                  "test setup should consume the cursor externally"
              Expect.equal
                  (incremental.TryCommitLocalisationRefresh cursorStage)
                  StagedLocalisationCommitResult.Superseded
                  "a stale cursor must supersede without another acknowledgement"
              Expect.isTrue
                  (Object.ReferenceEquals(cursorState, concrete.LocalisationPublicationIdentity))
                  "a stale cursor must preserve publication identity"

              let third = second + " staged_third:0 \"ready\"" + Environment.NewLine
              stl.UpdateFile false locPath (Some third) |> ignore
              let epochStage =
                  match incremental.PrepareLocalisationRefresh "epoch-stale" with
                  | Result.Ok(Some value) -> value
                  | other -> failtestf "third staged update should prepare, got %A" other
              let epochState = concrete.LocalisationPublicationIdentity
              ResourceManagerEager.nextTypeRules () |> ignore
              Expect.equal
                  (incremental.TryCommitLocalisationRefresh epochStage)
                  StagedLocalisationCommitResult.Superseded
                  "a changed dependency epoch must supersede without acknowledgement"
              Expect.isSome
                  (incremental.PeekLocalisationDelta "epoch-stale" |> Result.toOption |> Option.flatten)
                  "superseded commit must leave its prefix pending"
              Expect.isTrue
                  (Object.ReferenceEquals(epochState, concrete.LocalisationPublicationIdentity))
                  "an epoch-stale stage must not invoke publication"
              incremental.DiscardLocalisationRefresh epochStage
              incremental.DiscardLocalisationRefresh epochStage
              Expect.equal
                  (incremental.TryCommitLocalisationRefresh epochStage)
                  StagedLocalisationCommitResult.AlreadyCompleted
                  "discard must be idempotent and terminal"

          testWithCapturedLogs "incremental key add follows localisation reference in-edges"
          <| fun () ->
              let tempFolder = Path.Combine(Path.GetTempPath(), "cwtools-loc-delta-" + Guid.NewGuid().ToString("N"))
              let tempLocalisationFolder = Path.Combine(tempFolder, "localisation")
              Directory.CreateDirectory tempLocalisationFolder |> ignore
              try
                  let sourcePath = Path.Combine(tempLocalisationFolder, "source_l_english.yml")
                  let targetPath = Path.Combine(tempLocalisationFolder, "target_l_english.yml")
                  let utf8Bom = Text.UTF8Encoding(true)
                  let sourceText = "l_english:" + Environment.NewLine + " source_ref:0 \"$target_ref$\"" + Environment.NewLine
                  let targetText = "l_english:" + Environment.NewLine + " other:0 \"other\"" + Environment.NewLine
                  File.WriteAllText(sourcePath, sourceText, utf8Bom)
                  File.WriteAllText(targetPath, targetText, utf8Bom)

                  let configtext =
                      [ "./testfiles/localisationtests/test.cwt", File.ReadAllText "./testfiles/localisationtests/test.cwt"
                        "./testfiles/localisationtests/localisation.cwt",
                        File.ReadAllText "./testfiles/localisationtests/localisation.cwt" ]
                  let settings = emptyStellarisSettings tempFolder
                  let settings =
                      { settings with
                          validation =
                              { settings.validation with
                                  langs = [| STL STLLang.English |] }
                          rules =
                              Some
                                  { ruleFiles = configtext
                                    validateRules = false
                                    debugRulesOnly = false
                                    debugMode = false } }
                  let stl = STLGame(settings) :> IGame<STLComputedData>
                  stl.LocalisationErrors(true, true) |> ignore
                  let incremental = stl :?> IIncrementalLocalisation
                  let loadedTargetPath =
                      stl.AllFiles()
                      |> List.pick (function
                          | FileWithContentResource(_, file) when file.filetext.Contains("other:0") -> Some file.filepath
                          | _ -> None)
                  let loadedSourcePath =
                      stl.AllFiles()
                      |> List.pick (function
                          | FileWithContentResource(_, file) when file.filetext.Contains("source_ref:0") -> Some file.filepath
                          | _ -> None)
                  let updatedTarget = targetText + " target_ref:0 \"resolved\"" + Environment.NewLine
                  stl.UpdateFile false loadedTargetPath (Some updatedTarget) |> ignore
                  let delta = incremental.TakeLocalisationDelta()
                  Expect.isSome delta "target key addition should publish a delta"
                  Expect.contains
                      delta.Value.affectedLocalisationFiles
                      loadedSourcePath
                      "the source entry referencing the changed key must be invalidated"
                  let result = incremental.ValidateLocalisationDelta delta.Value
                  Expect.contains result.affectedFiles loadedSourcePath "the source localisation file must be replaced"
                  Expect.isFalse
                      (result.errors
                       |> List.exists (fun error ->
                           error.range.FileName = loadedSourcePath
                           && error.message.Contains("target_ref")))
                      "resolved inbound references must not retain an undefined-reference diagnostic"
              finally
                  try Directory.Delete(tempFolder, true) with _ -> ()

          testWithCapturedLogs "incremental localisation file deletion removes providers and matches full validation"
          <| fun () ->
              let configtext =
                  [ "./testfiles/localisationtests/test.cwt",
                    File.ReadAllText "./testfiles/localisationtests/test.cwt"
                    "./testfiles/localisationtests/localisation.cwt",
                    File.ReadAllText "./testfiles/localisationtests/localisation.cwt" ]
              let settings = emptyStellarisSettings "./testfiles/localisationtests/gamefiles"
              let settings =
                  { settings with
                      validation =
                          { settings.validation with
                              langs = [| STL STLLang.English |] }
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = false
                                debugRulesOnly = false
                                debugMode = false } }
              let stl = STLGame(settings) :> IGame<STLComputedData>
              stl.LocalisationErrors(true, true) |> ignore
              let incremental = stl :?> IIncrementalLocalisation
              let locPath =
                  stl.AllFiles()
                  |> List.pick (function
                      | FileWithContentResource(_, file) when file.filepath.EndsWith("l_english.yml") ->
                          Some file.filepath
                      | _ -> None)
              Expect.isTrue (incremental.IsLocalisationFile locPath) "the adapter must declare its localisation extension"
              let result = incremental.RemoveLocalisationFile locPath
              Expect.contains result.affectedFiles locPath "the deleted provider file must be invalidated"
              Expect.isFalse
                  (stl.AllLoadedLocalisation() |> List.exists (fun value -> value.Contains locPath))
                  "the deleted file must be removed from the localisation API map"
              let affected = result.affectedFiles |> Set.ofArray
              let facts (errors: CWError list) =
                  errors
                  |> List.filter (fun error -> affected.Contains error.range.FileName)
                  |> List.map (fun error ->
                      error.code,
                      error.range.FileName,
                      error.range.StartLine,
                      error.range.StartColumn,
                      error.message)
                  |> Set.ofList
              Expect.equal
                  (facts result.errors)
                  (stl.LocalisationErrors(true, true) |> facts)
                  "incremental deletion diagnostics must equal a full localisation validation"

          testWithCapturedLogs "incremental required type localisation reaches definitions and references"
          <| fun () ->
              let folder = "./testfiles/configtests/rulestests/STL/loc"
              let rulesPath = Path.Combine(folder, "rules.cwt")
              let settings = emptyStellarisSettings folder
              let settings =
                  { settings with
                      rules =
                          Some
                              { ruleFiles = [ rulesPath, File.ReadAllText rulesPath ]
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }
              let stl = STLGame(settings) :> IGame<STLComputedData>
              stl.LocalisationErrors(true, true) |> ignore
              let locPath, locText =
                  stl.AllFiles()
                  |> List.pick (function
                      | FileWithContentResource(_, file) when file.filepath.EndsWith("l_english.yml") ->
                          Some(file.filepath, file.filetext)
                      | _ -> None)
              let updatedLoc =
                  locText + Environment.NewLine + " my_ship_no_loc_required:0 \"resolved\"" + Environment.NewLine
              stl.UpdateFile false locPath (Some updatedLoc) |> ignore
              let incremental = stl :?> IIncrementalLocalisation
              let delta = incremental.TakeLocalisationDelta()
              Expect.isSome delta "required type localisation addition should publish a delta"
              let result = incremental.ValidateLocalisationDelta delta.Value
              let shipSizeFile =
                  stl.AllEntities()
                  |> Seq.map (fun struct (entity, _) -> entity.filepath)
                  |> Seq.find (fun filepath -> filepath.Contains("ship_sizes") && filepath.EndsWith("test.txt"))
              let eventFile =
                  stl.AllEntities()
                  |> Seq.map (fun struct (entity, _) -> entity.filepath)
                  |> Seq.find (fun filepath -> filepath.EndsWith("test_events.txt"))
              Expect.contains
                  result.affectedFiles
                  shipSizeFile
                  "global required-localisation diagnostics on the type definition file must be replaced"
              Expect.contains
                  result.affectedFiles
                  eventFile
                  "type references that require the changed localisation key must be revalidated"
          ]
