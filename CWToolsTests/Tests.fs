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

let getNodeComments (clause: IClause) =
    let findComments t s (a: Child) =
        match (s, a) with
        | (b, c), _ when b -> (b, c)
        | (_, c), CommentC comment when comment.Comment.StartsWith('#') -> (false, c)
        | (_, c), CommentC comment when comment.Comment.StartsWith('@') -> (false, c)
        | (_, c), CommentC comment -> (false, comment.Comment :: c)
        | (_, c), NodeC n when n.Position = t -> (true, c)
        | (_, c), LeafC v when v.Position = t -> (true, c)
        | (_, c), LeafValueC v when v.Position = t -> (true, c)
        | (_, c), ValueClauseC vc when vc.Position = t -> (true, c)
        | _ -> (false, [])
    // | ((_, c), LeafValueC lv) when lv.Position = t -> (true, c)
    // | ((_, _), _) -> (false, [])
    let fNode =
        (fun (clause: IClause) children ->
            let one =
                clause.Leaves
                |> Seq.map (fun e ->
                    e.Position, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> snd)
                |> List.ofSeq
            //log "%s %A" node.Key (node.All |> List.rev)
            //log "%A" one
            let two =
                clause.Nodes
                |> Seq.map (fun e ->
                    e.Position, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> snd)
                |> List.ofSeq

            let three =
                clause.LeafValues
                |> Seq.toList
                |> List.map (fun e ->
                    e.Position, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> snd)

            let four =
                clause.ValueClauses
                |> Seq.toList
                |> List.map (fun e ->
                    e.Position, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> snd)

            let new2 =
                one @ two @ three @ four |> List.filter (fun (_, c) -> not (List.isEmpty c))

            new2 @ children)

    let fCombine = (@)
    clause |> (foldClause2 fNode fCombine [])

// [<Tests>]
// let testsConfig =
//     testList "testFindComments" [
//         ftestWithCapturedLogs "basic" <| fun () ->
//             let testString = """
// #error
// test = test
// #error
// test2 = test
// test3 = test
// test
// """
//             let parsed = CWTools.Parser.CKParser.parseString testString "test"
//             match parsed with
//             |Success(res,_,_) ->
//                 let node = (STLProcess.shipProcess.ProcessNode() "root" (range.Zero) res)
//                 let comments = getNodeComments (node)
//                 eprintfn "%A" comments
//             |_ -> ()
//     ]

let getCompletionTests (clause: IClause) =
    let findComments t s (a: Child) =
        match (s, a) with
        | (b, c), _ when b -> (b, c)
        | (_, c), CommentC comment when comment.Comment.StartsWith('@') -> (false, comment.Comment :: c)
        | (_, c), CommentC _ -> (false, c)
        | (_, c), NodeC n when n.Position = t -> (true, c)
        | (_, c), LeafC v when v.Position = t -> (true, c)
        | (_, c), LeafValueC v when v.Position = t -> (true, c)
        | (_, c), ValueClauseC vc when vc.Position = t -> (true, c)
        | _ -> (false, [])
    // | ((_, c), LeafValueC lv) when lv.Position = t -> (true, c)
    // | ((_, _), _) -> (false, [])
    let fNode =
        (fun (clause: IClause) children ->
            let one =
                clause.Leaves
                |> Seq.map (fun e ->
                    e.Position, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> snd)
                |> List.ofSeq
            //log "%s %A" node.Key (node.All |> List.rev)
            //log "%A" one
            let two =
                clause.Nodes
                |> Seq.map (fun e ->
                    e.Position, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> snd)
                |> List.ofSeq

            let three =
                clause.LeafValues
                |> Seq.toList
                |> List.map (fun e ->
                    e.Position, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> snd)

            let four =
                clause.ValueClauses
                |> Seq.toList
                |> List.map (fun e ->
                    e.Position, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> snd)

            let new2 =
                one @ two @ three @ four |> List.filter (fun (_, c) -> not (List.isEmpty c))

            new2 @ children)

    let fCombine = (@)

    let res =
        clause
        |> (foldClause2 fNode fCombine [])
        |> List.collect (fun (r, sl) -> sl |> List.map (fun s -> r, s))

    let convertResToCompletionTest (pos: range, comment: string) =
        match comment.Split(' ', 3) with
        | [| option; column; text |] ->
            let negate = option = "@!"
            let lowscore = option = "@?"
            let pos = mkPos pos.Start.Line (pos.Start.Column + (int column) - 1)
            pos, text, negate, lowscore
        | _ -> failwith "invalid comment"

    res |> List.map convertResToCompletionTest

let rec remove_first f lst item =
    match lst with
    | h :: t when f item = f h -> t
    | h :: t -> h :: remove_first f t item
    | _ -> []

let remove_all_by x y f = y |> List.fold (remove_first f) x
let remove_all x y = remove_all_by x y id
//y |> List.fold remove_first x



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
              stl.LocalisationErrors(true, true) |> ignore
              let incremental = stl :?> IIncrementalLocalisation
              let locPath =
                  stl.AllFiles()
                  |> List.pick (function
                      | FileWithContentResource(_, file) when file.filetext.Contains("test_required_desc") -> Some file.filepath
                      | _ -> None)
              let updatedLoc = originalLoc + Environment.NewLine + " test:0 \"resolved\"" + Environment.NewLine
              stl.UpdateFile false locPath (Some updatedLoc) |> ignore
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

let testFolder folder testsname config configValidate configfile configOnly configLoc stl (culture: string) =
    testWithCapturedLogs (folder + testsname + culture)
    <| fun () ->
        Thread.CurrentThread.CurrentCulture <- CultureInfo(culture)
        Thread.CurrentThread.CurrentUICulture <- CultureInfo(culture)
        let configtext = if config then configFilesFromDir configfile else []
        // configtext |> Seq.iter (fun (fn, _) -> eprintfn "%s" fn)
        let completionTest (game: IGame) filename filetext (pos: pos, text: string, negate: bool, lowscore: bool) =
            let getLabel =
                function
                | Simple(label, score, _)
                | Detailed(label, _, score, _)
                | Snippet(label, _, _, score, _) -> label, score

            let compRes = game.Complete pos filename filetext |> List.map getLabel
            let labels = compRes |> List.map fst

            let lowscorelables =
                compRes
                |> List.choose (fun (label, score) ->
                    score |> Option.bind (fun s -> if s <= 20 then Some label else None))

            let scoreMap = compRes |> Map.ofList

            match negate, lowscore with
            | true, _ ->
                Expect.hasCountOf
                    labels
                    0u
                    ((=) text)
                    $"Completion shouldn't contain value %s{text} at %A{pos} in %s{filename}"
            | false, true ->
                //                logInfo (sprintf "ct %A" compRes)
                let firstLowScore = text, scoreMap[text]

                Expect.contains
                    lowscorelables
                    text
                    $"Incorrect completion values (missing low score) at %A{pos} in %s{filename}. Score (%A{firstLowScore})"
            | false, false ->
                Expect.contains labels text $"Incorrect completion values at %A{pos} in %s{filename}, %A{labels}"
                Expect.isNonEmpty labels $"No completion results, expected %s{text}"

        let completionTestPerFile (game: IGame) (filename: string, tests) =
            let filetext = File.ReadAllText filename
            tests |> List.iter (completionTest game filename filetext)
        // let stl = STLGame(folder, FilesScope.All, "", triggers, effects, modifiers, [], [configtext], [STL STLLang.English], false, true, config)
        let (game: IGame), errors, testVals, completionVals, parseErrors =
            if stl = 1 then
                let configtext =
                    ("./testfiles/validationtests/trigger_docs.log",
                     File.ReadAllText "./testfiles/validationtests/trigger_docs.log")
                    :: configtext
                // configtext |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "scopes.cwt")
                //             |> (fun f -> UtilityParser.initializeScopes f (Some defaultScopeInputs) )

                // let eventTargetLinks =
                //             configtext |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "links.cwt")
                //                     |> Option.map (fun (fn, ft) -> UtilityParser.loadEventTargetLinks (scopeManager.AnyScope) (scopeManager.ParseScope()) (scopeManager.AllScopes) fn ft)
                //                     |> Option.defaultValue (Scopes.STL.scopedEffects() |> List.map SimpleLink)
                // let triggers, effects = parseDocsFile "./testfiles/validationtests/trigger_docs_2.1.0.txt" |> (function |Success(p, _, _) -> DocsParser.processDocs (scopeManager.ParseScopes) p)
                // let modifiers = SetupLogParser.parseLogsFile "./testfiles/validationtests/setup.log" |> (function |Success(p, _, _) -> SetupLogParser.processLogs p)
                let settings = emptyStellarisSettings folder

                let settings =
                    { settings with
                        rules =
                            if config then
                                Some
                                    { ruleFiles = configtext
                                      validateRules = configValidate
                                      debugRulesOnly = configOnly
                                      debugMode = false }
                            else
                                None }

                let stl = STLGame(settings) :> IGame<STLComputedData>

                let errors =
                    stl.ValidationErrors()
                    @ (if configLoc then
                           stl.LocalisationErrors(false, false)
                       else
                           [])
                    |> List.map (fun e -> e.message, e.range) //>> (fun p -> FParsec.Position(p.StreamName, p.Index, p.Line, 1L)))

                let testVals =
                    stl.AllEntities()
                    |> Seq.toList
                    |> List.map (fun struct (e, _) ->
                        e.filepath,
                        getNodeComments e.entity
                        |> List.collect (fun (r, cs) -> cs |> List.map (fun _ -> r)))

                let completionTests =
                    stl.AllEntities()
                    |> Seq.toList
                    |> List.map (fun struct (e, _) -> e.filepath, getCompletionTests e.entity)

                (stl :> IGame), errors, testVals, completionTests, stl.ParserErrors()
            else if stl = 0 then
                let configtext =
                    ("./testfiles/configtests/rulestests/IR/triggers.log",
                     File.ReadAllText "./testfiles/configtests/rulestests/IR/triggers.log")
                    :: configtext

                let configtext =
                    ("./testfiles/configtests/rulestests/IR/effects.log",
                     File.ReadAllText "./testfiles/configtests/rulestests/IR/effects.log")
                    :: configtext

                let settings = emptyImperatorSettings folder

                let settings =
                    { settings with
                        rules =
                            if config then
                                Some
                                    { ruleFiles = configtext
                                      validateRules = configValidate
                                      debugRulesOnly = configOnly
                                      debugMode = false }
                            else
                                None }

                let ir = CWTools.Games.IR.IRGame(settings) :> IGame<IRComputedData>

                let errors =
                    ir.ValidationErrors()
                    @ (if configLoc then
                           ir.LocalisationErrors(false, false)
                       else
                           [])
                    |> List.map (fun e -> e.message, e.range) //>> (fun p -> FParsec.Position(p.StreamName, p.Index, p.Line, 1L)))

                let testVals =
                    ir.AllEntities()
                    |> Seq.toList
                    |> List.map (fun struct (e, _) ->
                        e.filepath,
                        getNodeComments e.entity
                        |> List.collect (fun (r, cs) -> cs |> List.map (fun _ -> r)))

                let completionTests =
                    ir.AllEntities()
                    |> Seq.toList
                    |> List.map (fun struct (e, _) -> e.filepath, getCompletionTests e.entity)

                (ir :> IGame), errors, testVals, completionTests, ir.ParserErrors()
            else if stl = 2 then
                let configtext =
                    ("./testfiles/configtests/rulestests/IR/triggers.log",
                     File.ReadAllText "./testfiles/configtests/rulestests/IR/triggers.log")
                    :: configtext

                let configtext =
                    ("./testfiles/configtests/rulestests/IR/effects.log",
                     File.ReadAllText "./testfiles/configtests/rulestests/IR/effects.log")
                    :: configtext

                let settings = emptyVictoriaSettings folder

                let settings =
                    { settings with
                        rules =
                            if config then
                                Some
                                    { ruleFiles = configtext
                                      validateRules = configValidate
                                      debugRulesOnly = configOnly
                                      debugMode = false }
                            else
                                None }

                let vic3 = CWTools.Games.VIC3.VIC3Game(settings) :> IGame<VIC3ComputedData>

                let errors =
                    vic3.ValidationErrors()
                    @ (if configLoc then
                           vic3.LocalisationErrors(false, false)
                       else
                           [])
                    |> List.map (fun e -> e.message, e.range) //>> (fun p -> FParsec.Position(p.StreamName, p.Index, p.Line, 1L)))

                let testVals =
                    vic3.AllEntities()
                    |> Seq.toList
                    |> List.map (fun struct (e, _) ->
                        e.filepath,
                        getNodeComments e.entity
                        |> List.collect (fun (r, cs) -> cs |> List.map (fun _ -> r)))

                let completionTests =
                    vic3.AllEntities()
                    |> Seq.toList
                    |> List.map (fun struct (e, _) -> e.filepath, getCompletionTests e.entity)

                (vic3 :> IGame), errors, testVals, completionTests, vic3.ParserErrors()
            else
                // let configtext = ("./testfiles/configtests/rulestests/IR/triggers.log", File.ReadAllText "./testfiles/configtests/rulestests/IR/triggers.log")::configtext
                // let configtext = ("./testfiles/configtests/rulestests/IR/effects.log", File.ReadAllText "./testfiles/configtests/rulestests/IR/effects.log")::configtext
                // let triggers = JominiParser.parseTriggerFilesRes "./testfiles/configtests/rulestests/IR/triggers.log" |> CWTools.Parser.JominiParser.processTriggers IRConstants.parseScopes
                // let effects = JominiParser.parseEffectFilesRes "./testfiles/configtests/rulestests/IR/effects.log" |> CWTools.Parser.JominiParser.processEffects IRConstants.parseScopes
                // eprintfn "testtest %A" triggers
                // configtext |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "scopes.cwt")
                //             |> (fun f -> UtilityParser.initializeScopes f None )

                // let eventTargetLinks =
                //             configtext |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "links.cwt")
                //                     |> Option.map (fun (fn, ft) -> UtilityParser.loadEventTargetLinks IRConstants.Scope.Any IRConstants.parseScope IRConstants.allScopes fn ft)
                //                     |> Option.defaultValue (Scopes.IR.scopedEffects |> List.map SimpleLink)
                let settings = emptyImperatorSettings folder

                let settings =
                    { settings with
                        rules =
                            if config then
                                Some
                                    { ruleFiles = configtext
                                      validateRules = configValidate
                                      debugRulesOnly = configOnly
                                      debugMode = false }
                            else
                                None }

                let hoi4 = CWTools.Games.HOI4.HOI4Game(settings) :> IGame<HOI4ComputedData>

                let errors =
                    hoi4.ValidationErrors()
                    @ (if configLoc then
                           hoi4.LocalisationErrors(false, false)
                       else
                           [])
                    |> List.map (fun e -> e.message, e.range) //>> (fun p -> FParsec.Position(p.StreamName, p.Index, p.Line, 1L)))

                let testVals =
                    hoi4.AllEntities()
                    |> Seq.toList
                    |> List.map (fun struct (e, _) ->
                        e.filepath,
                        getNodeComments e.entity
                        |> List.collect (fun (r, cs) -> cs |> List.map (fun _ -> r)))

                let completionTests =
                    hoi4.AllEntities()
                    |> Seq.toList
                    |> List.map (fun struct (e, _) -> e.filepath, getCompletionTests e.entity)

                (hoi4 :> IGame), errors, testVals, completionTests, hoi4.ParserErrors()

        // printfn "%A" (errors |> List.map (fun (c, f) -> f.StreamName))
        //printfn "%A" (testVals)
        //eprintfn "%A" testVals
        // eprintfn "%A" (stl.AllFiles())
        //let nodeComments = entities |> List.collect (fun (f, s) -> getNodeComments s) |> List.map fst
        let inner (file: string, nodekeys: range list) =
            if file.Contains "noerr" then
                ()
            else
                let expected = nodekeys |> List.map (fun nk -> "", nk)
                //|> List.map (fun p -> FParsec.Position(p.StreamName, p.Index, p.Line, 1L))
                let fileErrors = errors |> List.filter (fun (_, f) -> f.FileName = file)
                let fileErrorPositions = fileErrors //|> List.map snd
                let missing = remove_all_by expected fileErrorPositions snd
                let extras = remove_all_by fileErrorPositions expected snd
                //eprintfn "%A" nodekeys
                Expect.isEmpty
                    extras
                    $"Following lines are not expected to have an error %A{extras}, expected %A{expected}, actual %A{fileErrors}"

                Expect.isEmpty missing $"Following lines are expected to have an error %A{missing}"
        // eprintfn "ss %s %s" folder testsname
        Expect.isEmpty
            parseErrors
            (parseErrors
             |> List.tryHead
             |> Option.map (sprintf "%A")
             |> Option.defaultValue "")
        // yield testWithCapturedLogs (sprintf "parse %s" folder) <| fun () -> Expect.isEmpty parseErrors (parseErrors |> List.tryHead |> Option.map (sprintf "%A") |> Option.defaultValue "")
        testVals |> List.iter inner
        // yield! testVals |> List.map (fun (f, t) -> testWithCapturedLogs (f.ToString()) <| fun () -> inner (f, t))
        // yield! completionVals |> List.map (fun (f, t) -> testWithCapturedLogs ("Completion " + f.ToString()) <| fun() -> completionTestPerFile game (f, t))
        completionVals |> List.iter (completionTestPerFile game)

let testSubdirectories stl rulesonly dir =
    let dirs = Directory.EnumerateDirectories dir

    dirs
    |> Seq.map (fun d -> testFolder d "detailedconfigrules" true true d rulesonly true stl "en-GB")

