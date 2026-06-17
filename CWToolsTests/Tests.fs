module Tests

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

let emptyEmbeddedSettings =
    { triggers = []
      effects = []
      modifiers = [||]
      embeddedFiles = []
      cachedResourceData = []
      localisationCommands = Legacy([], [], [])
      eventTargetLinks = []
      cachedRuleMetadata = None
      featureSettings = UtilityParser.FeatureSettings.Default }

let emptyStellarisSettings rootDirectory =
    { rootDirectories = [| WD { name = "test"; path = rootDirectory } |]
      modFilter = None
      validation =
        { validateVanilla = false
          experimental = true
          langs = [| STL STLLang.English |] }
      rules = None
      embedded = FromConfig([], [])
      scriptFolders = None
      excludeGlobPatterns = None
      maxFileSize = None
      debugSettings = DebugSettings.Default
      vanillaPath = None }

let emptyImperatorSettings rootDirectory =
    { rootDirectories = [| WD { name = "test"; path = rootDirectory } |]
      modFilter = None
      validation =
        { validateVanilla = false
          experimental = true
          langs = [| IR IRLang.English |] }
      rules = None
      embedded = FromConfig([], [])
      scriptFolders = None
      excludeGlobPatterns = None
      maxFileSize = None
      debugSettings = DebugSettings.Default
      vanillaPath = None }

let emptyVictoriaSettings rootDirectory =
    { rootDirectories = [| WD { name = "test"; path = rootDirectory } |]
      modFilter = None
      validation =
        { validateVanilla = false
          experimental = true
          langs = [| VIC3 VIC3Lang.English |] }
      rules = None
      embedded = FromConfig([], [])
      scriptFolders = None
      excludeGlobPatterns = None
      maxFileSize = None
      debugSettings = DebugSettings.Default
      vanillaPath = None }

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

[<Tests>]
let pdxShaderFeatureTests =
    let source filepath filetext : PdxShaderFeatures.ShaderSource =
        { filepath = filepath
          logicalpath = filepath
          filetext = filetext }

    let cursorAtMarker (text: string) =
        let marker = text.IndexOf('|')
        Expect.isGreaterThan marker -1 "test shader cursor marker was not found"
        let before = text.Substring(0, marker)
        let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
        let lastLineBreak = before.LastIndexOf('\n')
        let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
        text.Remove(marker, 1), mkPos line column

    let label =
        function
        | CompletionResponse.Simple(label, _, _) -> label
        | CompletionResponse.Detailed(label, _, _, _) -> label
        | CompletionResponse.Snippet(label, _, _, _, _) -> label

    let sharedSource =
        source
            "gfx/FX/shared.fxh"
            """
VertexShader =
{
    MainCode VanillaVertex
    [[
        float4 main() { return float4(1.0f); }
    ]]
}

BlendState VanillaBlend
{
    BlendEnable = yes
}

PixelShader =
{
    MainCode PixelPdxMeshWhiteHole
    [[
        #ifdef WHITE_HOLE
        float4 main() { return float4(1.0f); }
        #endif
    ]]
}
"""

    testList
        "pdx shader features"
        [ test "complete vanilla cached shader symbols" {
              let text, cursor =
                  cursorAtMarker
                      """
Effect Example
{
    VertexShader = "Van|"
}
"""

              let labels =
                  PdxShaderFeatures.completeFromSources [ sharedSource ] Set.empty cursor "gfx/FX/current.shader" text
                  |> List.map label

              Expect.contains labels "VanillaVertex" "cached FX MainCodes should feed LSP completion"
          }
          test "complete DSL field types" {
              let text, cursor =
                  cursorAtMarker
                      """
VertexStruct VS_INPUT
{
    flo|
}
"""

              let labels =
                  PdxShaderFeatures.completeFromSources [] Set.empty cursor "gfx/FX/current.shader" text
                  |> List.map label

              Expect.contains labels "float4" "vertex struct members should complete FX field types"
          }
          test "complete cached shader symbols directly after assignment" {
              let text, cursor =
                  cursorAtMarker
                      """
Effect Example
{
    PixelShader = |
}
"""

              let labels =
                  PdxShaderFeatures.completeFromSources [ sharedSource ] Set.empty cursor "gfx/FX/current.shader" text
                  |> List.map label

              Expect.contains labels "PixelPdxMeshWhiteHole" "FX references should complete before opening a quoted value"
          }
          test "complete Effect Defines from cached shader conditions" {
              let text, cursor =
                  cursorAtMarker
                      """
Effect Example
{
    Defines = { "WH|" }
}
"""

              let labels =
                  PdxShaderFeatures.completeFromSources [ sharedSource ] Set.empty cursor "gfx/FX/current.shader" text
                  |> List.map label

              Expect.contains labels "WHITE_HOLE" "Effect Defines should complete preprocessor condition names"

              let bareText, bareCursor =
                  cursorAtMarker
                      """
Effect Example
{
    Defines = { | }
}
"""

              let bareLabels =
                  PdxShaderFeatures.completeFromSources [ sharedSource ] Set.empty bareCursor "gfx/FX/current.shader" bareText
                  |> List.map label

              Expect.contains bareLabels "WHITE_HOLE" "Effect Defines should complete before opening a quoted value"
          }
          test "validate against cached FX symbols" {
              let text =
                  """
Includes = { "shared.fxh" }

Effect Example
{
    VertexShader = "VanillaVertex"
    PixelShader = "MissingPixel"
    BlendState = "VanillaBlend"
}
"""

              let errors =
                  PdxShaderFeatures.validateFromSources [ sharedSource ] Set.empty "gfx/FX/current.shader" text

              Expect.exists
                  errors
                  (fun e -> e.code = "CWFX001" && e.message.Contains("MissingPixel"))
                  "missing FX references should still be diagnosed"

              Expect.isFalse
                  (errors |> List.exists (fun e -> e.message.Contains("VanillaVertex") || e.message.Contains("shared.fxh")))
                  "cached vanilla definitions and include files should satisfy FX validation"
          }
          test "validate MainCode references case-insensitively" {
              let text =
                  """
Effect PdxMeshWhitehole
{
    PixelShader = "PixelPdxMeshWhitehole"
}
"""

              let errors =
                  PdxShaderFeatures.validateFromSources [ sharedSource ] Set.empty "gfx/FX/current.shader" text

              Expect.isFalse
                  (errors |> List.exists (fun e -> e.message.Contains("PixelPdxMeshWhitehole")))
                  "Effect references should match MainCode names even when casing differs"
          }
          test "document symbols expose FX declarations" {
              let text =
                  """
VertexShader =
{
    MainCode ExampleVertex
    [[
        float4 main() { return float4(1.0f); }
    ]]
}

Effect ExampleEffect
{
    VertexShader = "ExampleVertex"
}
"""

              let symbols = PdxShaderFeatures.documentSymbols "gfx/FX/current.shader" text
              let shaderBlock = symbols |> List.find (fun symbol -> symbol.name = "VertexShader")

              Expect.exists symbols (fun symbol -> symbol.name = "ExampleEffect") "effects should appear in FX outline"
              Expect.exists shaderBlock.children (fun symbol -> symbol.name = "ExampleVertex") "MainCode should nest under the shader block"
          }
          test "goto definition resolves cached FX references" {
              let text, cursor =
                  cursorAtMarker
                      """
Effect Example
{
    VertexShader = "Vanilla|Vertex"
}
"""

              let target =
                  PdxShaderFeatures.goToDefinitionFromSources [ sharedSource ] cursor "gfx/FX/current.shader" text

              Expect.isSome target "cached FX definitions should be available to goto definition"
              Expect.equal target.Value.FileName "gfx/FX/shared.fxh" "goto definition should target the cached source"
          } ]

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

              Expect.hasCountOf globalLocError 10u (fun _ -> true) $"wrong number of errors %A{globalLocError}"
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
          ]

let rec getAllFolders dirs =
    if Seq.isEmpty dirs then
        Seq.empty
    else
        seq {
            yield! dirs |> Seq.collect Directory.EnumerateDirectories
            yield! dirs |> Seq.collect Directory.EnumerateDirectories |> getAllFolders
        }

let getAllFoldersUnion dirs =
    seq {
        yield! dirs
        yield! getAllFolders dirs
    }

let configFilesFromDir folder =
    let configFiles =
        if Directory.Exists folder then
            getAllFoldersUnion ([ folder ] |> Seq.ofList)
            |> Seq.collect Directory.EnumerateFiles
        else if File.Exists folder then
            [ folder ] |> Seq.ofList
        else
            Seq.empty

    configFiles
    |> List.ofSeq
    |> List.filter (fun f -> Path.GetExtension f = ".cwt")
    |> List.map (fun f -> f, File.ReadAllText f)

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

[<Tests>]
let folderTests =
    testList
        "validation"
        [ testFolder "./testfiles/validationtests/gfxtests" "gfx" false false "" false false 1 "en-GB"
          // testFolder "./testfiles/validationtests/scopetests" "scopes" false "" false false "en-GB"
          // testFolder "./testfiles/validationtests/variabletests" "variables" true false "./testfiles/stellarisconfig" false false "en-GB"
          // testFolder "./testfiles/validationtests/modifiertests" "modifiers" false "" false false "en-GB"
          testFolder
              "./testfiles/validationtests/eventtests"
              "events"
              true
              false
              "./testfiles/stellarisconfig"
              false
              false
              1
              "en-GB"
          // testFolder "./testfiles/validationtests/weighttests" "weights" false "" false false "en-GB"
          testFolder
              "./testfiles/multiplemodtests"
              "multiple"
              true
              true
              "./testfiles/multiplemodtests/test.cwt"
              false
              false
              1
              "en-GB"
          testFolder
              "./testfiles/configtests/validationtests"
              "configrules"
              true
              true
              "./testfiles/configtests/config/"
              false
              false
              1
              "en-GB"
          testFolder
              "./testfiles/configtests/validationtests"
              "configrules"
              true
              true
              "./testfiles/configtests/config/"
              false
              false
              1
              "ru-RU"
          // yield! testSubdirectories "./testfiles/configtests/rulestests"
          // testFolder "./testfiles/configtests/rulestests" "detailedconfigrules" true "./testfiles/configtests/rulestests/rules.cwt" true "en-GB"
          ]
//[<Tests>]
//let stlAllSubfolderTests = testList "validation all stl" (testSubdirectories true "./testfiles/configtests/rulestests/All" |> List.ofSeq)
//[<Tests>]
//let irAllSubfolderTests = testList "validation all ir" (testSubdirectories false "./testfiles/configtests/rulestests/All" |> List.ofSeq)
[<Tests>]
let stlSubfolderTests =
    testList "validation stl" (testSubdirectories 1 true "./testfiles/configtests/rulestests/STL" |> List.ofSeq)

[<Tests>]
let stlGlobalSubfolderTests =
    testList
        "validation stl global"
        (testSubdirectories 1 false "./testfiles/configtests/ruleswithglobaltests/STL"
         |> List.ofSeq)

[<Tests>]
let inlineScriptCompletionRegressionTests =
    testList
        "inline script completion regression"
        [ testWithCapturedLogs "nested inline keeps concrete parent path" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/inlinescripts"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "completion_inner.txt")
                  )
              let filetext = File.ReadAllText filename

              let labels =
                  stl.Complete (mkPos 2 8) filename filetext
                  |> List.map (function
                      | Simple(label, _, _)
                      | Detailed(label, _, _, _)
                      | Snippet(label, _, _, _, _) -> label)

              Expect.contains labels "expected_leaf" "Nested inline completion should use the concrete child block"
              Expect.isFalse (labels |> List.contains "root_only") "Nested inline completion should not fall back to root fields"

              let parameterizedFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "completion_param_common.txt")
                  )

              let parameterizedFiletext = File.ReadAllText parameterizedFilename

              let parameterizedLabels =
                  stl.Complete (mkPos 1 4) parameterizedFilename parameterizedFiletext
                  |> List.map (function
                      | Simple(label, _, _)
                      | Detailed(label, _, _, _)
                      | Snippet(label, _, _, _, _) -> label)

              Expect.contains parameterizedLabels "expected_leaf" "Parameterized nested inline completion should use the concrete child block"
              Expect.isFalse (parameterizedLabels |> List.contains "root_only") "Parameterized nested inline completion should not fall back to root fields"

              let inlineDefaultFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "completion_pipe_default_no.txt")
                  )

              let inlineDefaultFiletext = File.ReadAllText inlineDefaultFilename

              let inlineDefaultLabels =
                  stl.Complete (mkPos 1 4) inlineDefaultFilename inlineDefaultFiletext
                  |> List.map (function
                      | Simple(label, _, _)
                      | Detailed(label, _, _, _)
                      | Snippet(label, _, _, _, _) -> label)

              Expect.isFalse (inlineDefaultLabels |> List.contains "expected_leaf") "Inline script callers should not match path defaults with pipe syntax" ]

[<Tests>]
let scriptedBracketParameterRegressionTests =
    let cursorAtMarker (text: string) =
        let marker = text.IndexOf('|')
        Expect.isGreaterThan marker -1 "test cursor marker was not found"
        let before = text.Substring(0, marker)
        let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
        let lastLineBreak = before.LastIndexOf('\n')
        let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
        text.Remove(marker, 1), mkPos line column

    let cursorAtTildeMarker (text: string) =
        let marker = text.IndexOf('~')
        Expect.isGreaterThan marker -1 "test cursor marker was not found"
        let before = text.Substring(0, marker)
        let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
        let lastLineBreak = before.LastIndexOf('\n')
        let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
        text.Remove(marker, 1), mkPos line column

    let label =
        function
        | Simple(label, _, _)
        | Detailed(label, _, _, _)
        | Snippet(label, _, _, _, _) -> label

    testSequenced
    <| testList
        "scripted bracket parameter regression"
        [ testWithCapturedLogs "bracket params feed call-site completion" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripteddefaults"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    option = {
        scripted_effect_bracket_param_validation = {
            |
        }
    }
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.contains labels "bracket_condition" "Positive bracket condition should complete as a scripted parameter"
              Expect.contains labels "negated_condition" "Negated bracket condition should complete as a scripted parameter"
              Expect.contains labels "kamikakushi_bonus" "Prefixed bracket condition should complete as a scripted parameter"

          testWithCapturedLogs "script value bracket params feed value completion" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtTildeMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    trigger = {
        test_value = value:scripted_bracket_positive|~
    }
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.contains labels "BRACKET" "Script value bracket condition should complete as a value parameter"

          testWithCapturedLogs "script value names complete after value prefix" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtTildeMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    trigger = {
        test_value = value:~
    }
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.contains labels "value:scripted_param" "Script values should complete after value:"
              Expect.contains labels "value:scripted_bracket_positive" "Script value names should include bracket-param definitions"

          testWithCapturedLogs "script value param completion skips value slot" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtTildeMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    trigger = {
        test_value = value:scripted_param|PARAM|~
    }
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.isFalse (labels |> List.contains "PARAM") "Script value value slots should not suggest parameter names"

          testWithCapturedLogs "script value parameterized call goes to definition" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtTildeMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    trigger = {
        test_value = value:scri~pted_param|PARAM|abs|
    }
}
"""

              let target = stl.GoToType pos filename filetext

              Expect.isSome target "Parameterized script value call should go to its definition"
              Expect.stringContains
                  (target.Value.FileName.Replace("\\", "/"))
                  "common/script_values/test.txt"
                  "Go to definition should target the script_values file"

          testWithCapturedLogs "scripted count wrapper completes as trigger" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    trigger = {
        |
    }
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.contains
                  labels
                  "test_scripted_trigger_value"
                  "Scripted triggers wrapping count_* without count should complete as trigger conditions" ]

[<Tests>]
let incrementalScriptedRefreshTests =
    let stlScriptedGame () =
        let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
        let configtext = configFilesFromDir folder

        let settings =
            { emptyStellarisSettings folder with
                rules =
                    Some
                        { ruleFiles = configtext
                          validateRules = true
                          debugRulesOnly = false
                          debugMode = false } }

        STLGame(settings) :> IGame<STLComputedData>, folder

    // Sequenced: constructing an STLGame re-inits the global ScopeManager singleton, which
    // races with any other game construction running in parallel.
    testSequenced
    <| testList
        "incremental scripted refresh"
        [ testWithCapturedLogs "prepare is pure and commit swaps the type index" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))

              let typesBefore = stl.Types()
              let staged = stl.PrepareScriptedTypes [ triggerFile ]
              Expect.isSome staged "prepare should stage a scripted_triggers file"
              Expect.isTrue
                  (System.Object.ReferenceEquals(stl.Types(), typesBefore))
                  "prepare must not reassign the live type index"

              let committed = stl.CommitScriptedTypes staged.Value
              Expect.isTrue committed "commit should succeed when the type index is unchanged since prepare"
              Expect.isFalse
                  (System.Object.ReferenceEquals(stl.Types(), typesBefore))
                  "commit should install the staged type index"
              Expect.contains
                  (stl.Types().["scripted_trigger"] |> Array.map (fun t -> t.id))
                  "test_scripted_trigger_country"
                  "committed type index should still contain the fixture's scripted triggers"

          testWithCapturedLogs "commit is rejected when the type index changed since prepare" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))

              let staged = stl.PrepareScriptedTypes [ triggerFile ]
              Expect.isSome staged "prepare should stage a scripted_triggers file"

              // Simulate an external writer replacing lookup.typeDefInfo between prepare and commit.
              stl.RefreshScriptedTypes [ triggerFile ] |> ignore

              let committed = stl.CommitScriptedTypes staged.Value
              Expect.isFalse committed "commit must reject a staged result whose base type index was replaced" ]

[<Tests>]
let irSubfolderTests =
    testList "validation ir" (testSubdirectories 0 true "./testfiles/configtests/rulestests/IR" |> List.ofSeq)

[<Tests>]
let hoi4SubfolderTests =
    testList
        "validation hoi4"
        (testSubdirectories 3 true "./testfiles/configtests/rulestests/HOI4"
         |> List.ofSeq)

[<Tests>]
let vic3SubfolderTests =
    testList
        "validation vic3"
        (testSubdirectories 2 true "./testfiles/configtests/rulestests/VIC3"
         |> List.ofSeq)

[<Tests>]
let specialtests =
    // testList
    // "log"
    ptestCase "log modifiers"
    <| fun () ->
        let configtext =
            [ ("./testfiles/scriptedorstatictest/setup.log",
               File.ReadAllText "./testfiles/scriptedorstatictest/setup.log") ]

        let modfile =
            SetupLogParser.parseLogsFile "./testfiles/scriptedorstatictest/setup.log"
        // (modfile |> (function |Failure(e, _,_) -> eprintfn "%s" e |_ -> ()))
        let modifiers =
            (modfile
             |> (function
             | ParserResult.Success(p, _, _) -> SetupLogParser.processLogs p
             | ParserResult.Failure _ -> failwith "todo"))

        let settings = emptyStellarisSettings "./testfiles/scriptedorstatictest"
        // UtilityParser.initializeScopes None (Some defaultScopeInputs)
        let stl =
            STLGame(
                { settings with
                    rules =
                        Some
                            { ruleFiles = configtext
                              validateRules = false
                              debugRulesOnly = false
                              debugMode = false }
                    embedded =
                        ManualSettings
                            { emptyEmbeddedSettings with
                                modifiers = modifiers |> List.toArray } }
            )
            :> IGame<STLComputedData>
        // let stl = STLGame("./testfiles/scriptedorstatictest/", FilesScope.All, "", [], [], modifiers, [], [], [STL STLLang.English], false, true, false)
        let exp =
            [| { tag = "test"
                 categories = [ modifierCategoryManager.ParseModifier () "pop" ] } |]

        Expect.equal (stl.StaticModifiers()) exp ""
// [<Tests>]
// let tests2 =
//     testList "validation" [
//         let stl = STLGame("./testfiles/validationtests/interfacetests", FilesScope.All, "", [], [], [], [], [STL STLLang.English], false)
//         let errors = stl.ValidationErrors |> List.map (fun (c, s, n, l, f) -> Position.UnConv n)
//         let testVals = stl.AllEntities |> List.map (fun (e) -> e.filepath, getNodeComments e.entity |> List.map fst)
//         // eprintfn "%A" (stl.AllFiles())
//         //let nodeComments = entities |> List.collect (fun (f, s) -> getNodeComments s) |> List.map fst
//         let inner (file, ((nodekeys : FParsec.Position list)) )=
//             let expected = nodekeys
//             let fileErrors = errors |> List.filter (fun f -> f.StreamName = file )
//             let missing = remove_all expected fileErrors
//             let extras = remove_all fileErrors expected
//             Expect.isEmpty (extras) (sprintf "Following lines are not expected to have an error %A" extras )
//             Expect.isEmpty (missing) (sprintf "Following lines are expected to have an error %A" missing)
//         yield! testVals |> List.map (fun (f, t) -> testWithCapturedLogs (f.ToString()) <| fun () -> inner (f, t))

//     ]

// [<Tests>]
// let tests3 =
//     testList "validation" [
//         let triggers, effects = parseDocsFile "./testfiles/validationtests/trigger_docs_0.2.txt" |> (function |Success(p, _, _) -> DocsParser.processDocs p)
//         let stl = STLGame("./testfiles/validationtests/scopetests", FilesScope.All, "", triggers, effects, [], [], [STL STLLang.English], false)
//         let errors = stl.ValidationErrors |> List.map (fun (c, s, n, l, f) -> Position.UnConv n)
//         let testVals = stl.AllEntities |> List.map (fun (e) -> e.filepath, getNodeComments e.entity |> List.map fst)
//         //let nodeComments = entities |> List.collect (fun (f, s) -> getNodeComments s) |> List.map fst
//         let inner (file, ((nodekeys : FParsec.Position list)) )=
//             let expected = nodekeys
//             let fileErrors = errors |> List.filter (fun f -> f.StreamName = file )
//             let missing = remove_all expected fileErrors
//             let extras = remove_all fileErrors expected
//             Expect.isEmpty (extras) (sprintf "Following lines are not expected to have an error %A" extras )
//             Expect.isEmpty (missing) (sprintf "Following lines are expected to have an error %A" missing)
//         yield! testVals |> List.map (fun (f, t) -> testWithCapturedLogs (f.ToString()) <| fun () -> inner (f, t))
//     ]

let rec replaceFirst predicate value =
    function
    | [] -> []
    | h :: t when predicate h -> value :: t
    | h :: t -> h :: replaceFirst predicate value t

let fixEmbeddedFileName (s: string) =
    let count = (Seq.filter ((=) '.') >> Seq.length) s
    let mutable out = "//" + s

    [ 1 .. count - 1 ]
    |> List.iter (fun _ ->
        out <-
            (replaceFirst ((=) '.') '/' (out |> List.ofSeq))
            |> Array.ofList
            |> FSharp.Core.string)

    out

[<Tests>]
let embeddedTests =
    testWithCapturedLogs "embedded"
    <| fun () ->
        let filelist =
            Assembly
                .GetExecutingAssembly()
                .GetManifestResourceStream("CWToolsTests.testfiles.embeddedtest.embedded.vanilla_files_test.csv")
            |> (fun f -> (new StreamReader(f)).ReadToEnd().Split(Environment.NewLine))
            |> Array.toList
            |> List.map (fun f -> f, "")

        let embeddedFileNames =
            Assembly.GetExecutingAssembly().GetManifestResourceNames()
            |> Array.filter (fun f ->
                f.Contains("embeddedtest")
                && (f.Contains("common") || f.Contains("localisation") || f.Contains("interface")))

        //Test serialization
        let fileManager =
            FileManager(
                [| WD
                       { name = "test"
                         path = "./testfiles/embeddedtest/test" } |],
                Some "",
                scriptFolders,
                "stellaris",
                Encoding.UTF8,
                [||],
                2000000
            )

        let files = fileManager.AllFilesByPath()

        let resources: IResourceAPI<STLComputedData> =
            ResourceManager<STLComputedData>(
                Compute.STL.computeSTLData (fun () -> None),
                Compute.STL.computeSTLDataUpdate (fun () -> None),
                Encoding.UTF8,
                Encoding.GetEncoding(1252),
                true
            )
                .Api

        let entities =
            resources.UpdateFiles(files)
            |> List.choose (fun (r, e) ->
                e
                |> function
                    | Some e2 -> Some(r, e2)
                    | _ -> None)
            |> List.map (fun (r, (struct (e, _))) -> r, e)

        let cache = Serializer.picklerCache
        let binarySerializer = FsPickler.CreateBinarySerializer(picklerResolver = cache)

        let data =
            { resources = entities
              fileIndexTable = fileIndexTable
              files = []
              stringResourceManager = StringResource.stringManager }

        let pickle = binarySerializer.Pickle data

        let unpickled = binarySerializer.UnPickle pickle
        fileIndexTable <- unpickled.fileIndexTable
        let cached = unpickled.resources


        let _ =
            embeddedFileNames
            |> List.ofArray
            |> List.map (fun f ->
                fixEmbeddedFileName f,
                (new StreamReader(Assembly.GetExecutingAssembly().GetManifestResourceStream(f))).ReadToEnd())

        let configtext = configFilesFromDir "./testfiles/embeddedtest/config/"
        let baseSettings = emptyStellarisSettings "./testfiles/embeddedtest/test"

        let settings =
            { baseSettings with
                rules =
                    Some
                        { RulesSettings.ruleFiles = configtext
                          validateRules = true
                          debugMode = false
                          debugRulesOnly = false } }

        let settingsE =
            { settings with
                embedded =
                    ManualSettings
                        { emptyEmbeddedSettings with
                            embeddedFiles = filelist
                            cachedResourceData = cached } }
        // UtilityParser.initializeScopes None (Some defaultScopeInputs)

        let stlE = STLGame(settingsE) :> IGame<STLComputedData>
        let stlNE = STLGame(settings) :> IGame<STLComputedData>
        let eerrors = stlE.ValidationErrors() |> List.map (fun e -> e.range)
        let neerrors = stlNE.ValidationErrors() |> List.map (fun e -> e.message, e.range)

        let etestVals =
            stlE.AllEntities()
            |> Seq.toList
            |> List.map (fun struct (e, _) -> e.filepath, getNodeComments e.entity |> List.map fst)

        let netestVals =
            stlNE.AllEntities()
            |> Seq.toList
            |> List.map (fun struct (e, _) -> e.filepath, getNodeComments e.entity |> List.map fst)

        let einner (file, _: range list) =
            let fileErrors = eerrors |> List.filter (fun f -> f.FileName = file)
            Expect.isEmpty fileErrors $"Following lines are not expected to have an error %A{fileErrors}"

        etestVals |> List.iter einner

        let neinner (file, nodekeys: range list) =
            let expected = nodekeys |> List.map (fun nk -> "", nk)
            let fileErrors = neerrors |> List.filter (fun (_, f) -> f.FileName = file)
            let fileErrorPositions = fileErrors //|> List.map snd
            let missing = remove_all_by expected fileErrorPositions snd
            let extras = remove_all_by fileErrorPositions expected snd

            Expect.isEmpty
                extras
                $"Following lines are not expected to have an error %A{extras}, expected %A{expected}, actual %A{fileErrors}"

            Expect.isEmpty missing $"Following lines are expected to have an error %A{missing}"

        netestVals |> List.iter neinner

// ]

[<Tests>]
let overwriteTests =
    testWithCapturedLogs "overwrite"
    <| fun () ->
        // eprintfn "%A" filelist
        let configtext =
            [ "./testfiles/overwritetest/test.cwt", File.ReadAllText "./testfiles/overwritetest/test.cwt" ]

        let triggers, effects =
            parseDocsFile "./testfiles/validationtests/trigger_docs_2.0.2.txt"
            |> (function
            | Success(p, _, _) -> processDocs scopeManager.ParseScopes p
            | ParserResult.Failure _ -> failwith "todo")

        let modifiers =
            SetupLogParser.parseLogsFile "./testfiles/validationtests/setup.log"
            |> (function
            | Success(p, _, _) -> SetupLogParser.processLogs p
            | ParserResult.Failure _ -> failwith "todo")

        let embeddedFileNames =
            Assembly.GetExecutingAssembly().GetManifestResourceNames()
            |> Array.filter (fun f ->
                f.Contains("overwritetest")
                && (f.Contains("common") || f.Contains("localisation") || f.Contains("interface")))

        let embeddedFiles =
            embeddedFileNames
            |> List.ofArray
            |> List.map (fun f ->
                fixEmbeddedFileName f,
                (new StreamReader(Assembly.GetExecutingAssembly().GetManifestResourceStream(f))).ReadToEnd())

        let settings = emptyStellarisSettings "./testfiles/overwritetest/test"

        let settings =
            { settings with
                embedded =
                    ManualSettings
                        { emptyEmbeddedSettings with
                            triggers = triggers
                            effects = effects
                            modifiers = modifiers |> List.toArray
                            embeddedFiles = embeddedFiles }
                rules =
                    Some
                        { ruleFiles = configtext
                          validateRules = true
                          debugRulesOnly = false
                          debugMode = false } }
        // UtilityParser.initializeScopes None (Some defaultScopeInputs)
        let stl = STLGame(settings) :> IGame<STLComputedData>
        let errors = stl.ValidationErrors() |> List.map (fun e -> e.message, e.range) //>> (fun p -> FParsec.Position(p.StreamName, p.Index, p.Line, 1L)))

        let testVals =
            stl.AllEntities()
            |> Seq.map (fun struct (e, _) -> e.filepath, getNodeComments e.entity |> List.map fst)

        let inner (file, nodekeys: range list) =
            let expected = nodekeys //|> List.map (fun p -> FParsec.Position(p.StreamName, p.Index, p.Line, 1L))
            let fileErrors = errors |> List.filter (fun (_, f) -> f.FileName = file)
            let fileErrorPositions = fileErrors |> List.map snd
            let missing = remove_all expected fileErrorPositions
            let extras = remove_all fileErrorPositions expected
            //eprintfn "%A" fileErrors
            Expect.isEmpty
                extras
                $"Following lines are not expected to have an error %A{extras}, all %A{expected}, actual %A{fileErrors}"

            Expect.isEmpty missing $"Following lines are expected to have an error %A{missing}"

        testVals |> Seq.iter inner
// ]

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

        let updateErrors =
            stl.UpdateFile true updatePath None
            |> List.filter (fun e -> e.code = "CW239")

        Expect.equal
            updateErrors.Length
            1
            $"UpdateFile should also report the unused on_action: %A{updateErrors |> List.map (fun e -> e.message)}"



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
