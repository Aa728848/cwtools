module EmbeddedResourceTests

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




open TestHelpers
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

let fixEmbeddedResourceFileName (s: string) =
    let marker = ".embedded."
    let embeddedIndex = s.IndexOf(marker, StringComparison.Ordinal)

    if embeddedIndex >= 0 then
        let fixedName = s.Substring(embeddedIndex + marker.Length) |> fixEmbeddedFileName
        fixedName.TrimStart('/')
    else
        fixEmbeddedFileName s

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

        let manifestEmbeddedFiles =
            embeddedFileNames
            |> List.ofArray
            |> List.map (fun f ->
                fixEmbeddedResourceFileName f,
                (new StreamReader(Assembly.GetExecutingAssembly().GetManifestResourceStream(f))).ReadToEnd())

        let manifestResourceInputs =
            manifestEmbeddedFiles
            |> List.map (fun (filePath, fileText) ->
                EntityResourceInput
                    { scope = "embedded"
                      filepath = filePath
                      logicalpath = fileManager.ConvertPathToLogicalPath filePath
                      filetext = fileText
                      validate = false })
            |> Array.ofList

        let files = Array.append (fileManager.AllFilesByPath()) manifestResourceInputs

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


        let embeddedFiles = filelist @ manifestEmbeddedFiles

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
                            embeddedFiles = embeddedFiles
                            cachedResourceData = cached } }
        // UtilityParser.initializeScopes None (Some defaultScopeInputs)

        let stlE = STLGame(settingsE) :> IGame<STLComputedData>
        let stlNE = STLGame(settings) :> IGame<STLComputedData>
        let embeddedButtonEffects =
            stlE.Types()
            |> Map.tryFind "button_effect"
            |> Option.defaultValue [||]
            |> Array.map (fun t -> t.id)
            |> Array.toList

        let embeddedEntitySummaries =
            stlE.AllEntities()
            |> Seq.map (fun struct (e, _) -> e.filepath, e.logicalpath, e.entityType.ToString())
            |> Seq.toList

        Expect.contains
            embeddedButtonEffects
            "test_button_effect_1"
            $"Embedded button effects should be loaded, got %A{embeddedButtonEffects}; entities %A{embeddedEntitySummaries}"

        let eerrors = stlE.ValidationErrors() |> List.map (fun e -> e.message, e.range)
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
            let fileErrors = eerrors |> List.filter (fun (_, f) -> f.FileName = file)
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

