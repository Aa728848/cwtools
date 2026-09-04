module TestHelpers


open System.Collections.Frozen
open Expecto
open LogCaptureTest
open FParsec
open CWTools.Common
open CWTools.Process
open CWTools.Parser
open CWTools.Rules
// open CWTools.Rules.RulesParser
open CWTools.Games
open System.IO
open CWTools.Common.STLConstants
open CWTools.Utilities.Position
open CWTools.Validation
open CWTools.Utilities.Utils
open CWTools.Utilities.Utils2
open CWTools.Utilities
open CWTools.Games.Files
open CWTools.Games.Stellaris

open CWTools.Process.Scopes.STL
open CWTools.Process.Scopes
open CWTools.Process.Scopes.Scopes
open System
open System.Reflection
open CWTools.Parser.CKPrinter
open CWTools.Parser.DocsParser
open CWTools
open Expecto.Logging
open Expecto.Logging.Message
open CWTools.Process.Localisation
open CWTools.Process.ProcessCore
open System.Threading
open System.Globalization
open System.Text
open MBrace.FsPickler

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

let emptyDataTypesLazy =
    lazy
        { DataTypeParser.JominiLocDataTypes.promotes = Map.empty
          DataTypeParser.JominiLocDataTypes.confidentFunctions = Map.empty
          DataTypeParser.JominiLocDataTypes.functions = Map.empty
          DataTypeParser.JominiLocDataTypes.dataTypes = Map.empty
          DataTypeParser.JominiLocDataTypes.dataTypeNames = Set.empty }

let specificField = RulesParser.specificField
let optionalMany = RulesParser.optionalMany
let optionalSingle = RulesParser.optionalSingle
let requiredSingle = RulesParser.requiredSingle
let defaultFloat = RulesParser.defaultFloat
let defaultInt = RulesParser.defaultInt
let parseConfig = RulesParser.parseConfig

let dynamicSettings _ =
    { CWTools.Process.Localisation.LegacyLocDynamicsSettings.scriptedLocCommands = []
      CWTools.Process.Localisation.LegacyLocDynamicsSettings.eventTargets = []
      CWTools.Process.Localisation.LegacyLocDynamicsSettings.setVariables = IgnoreCaseStringSet() }

let processLocalisationLazy =
    lazy
        ((Helpers.createLocalisationFunctions
            CWTools.Process.Localisation.STL.locStaticSettings
            dynamicSettings
            ([], [], ([], []))
            (STLLookup()))
         |> fst)

let validateLocalisationLazy =
    lazy
        ((Helpers.createLocalisationFunctions
            CWTools.Process.Localisation.STL.locStaticSettings
            dynamicSettings
            ([], [], ([], []))
            (STLLookup()))
         |> snd)
let createStarbaseRule () =
    let owner =
       NewRule(LeafRule(specificField "owner", ScopeField [ scopeManager.AnyScope ]), requiredSingle)

    let size =
        NewRule(LeafRule(specificField "size", ValueField(ValueType.Enum "size")), requiredSingle)

    let moduleR =
        NewRule(LeafRule(specificField "module", ValueField(ValueType.Enum "module")), optionalMany)

    let building =
        NewRule(LeafRule(specificField "building", ValueField(ValueType.Enum "building")), optionalMany)

    let effect =
        NewRule(
            NodeRule(
                specificField "effect",
                [| (LeafRule(AliasField "effect", AliasField "effect")), optionalMany |]
            ),
            { optionalSingle with
                replaceScopes =
                    Some
                        { froms = None
                          root = Some(scopeManager.ParseScope () "country")
                          this = Some(scopeManager.ParseScope () "country")
                          prevs = None } }
        )

    let rule =
        NewRule(
            NodeRule(specificField "create_starbase", [| owner; size; moduleR; building; effect |]),
            optionalMany
        )

    rule

let createStarbaseLazy = lazy (createStarbaseRule ())

let createStarbaseAlias () = AliasRule("effect", createStarbaseRule ())

let createStarbaseAliasLazy = lazy (createStarbaseAlias ())

let createStarbaseEnumsLazy =
    lazy
        ([ ("size", ("size", [ "medium"; "large" ]))
           ("module", ("module", [ "trafficControl" ]))
           ("building", ("building", [ "crew" ])) ]
         |> Map.ofList)

let createStarbaseTypeDefLazy =
    lazy
        { name = "create_starbase"
          nameField = None
          pathOptions =
            { paths = [| "events" |]
              pathStrict = false
              pathFile = None
              pathExtension = None }
          conditions = None
          subtypes = []
          typeKeyFilter = None
          typeKeyRegex = None
          rootCompletionFromSubtypes = false
          skipRootKey = []
          warningOnly = false
          type_per_file = false
          localisation = []
          modifiers = []
          startsWith = None
          unique = false
          graphRelatedTypes = []
          keyPrefix = None
          shouldBeReferenced = RefNotRequired
          unknownKeyHandling = UnknownKeyIgnore
          obsoleteKeys = Map.empty }

let buildingLazy =
    lazy
        (let inner =
            [| NewRule(LeafRule(specificField "allow", ScalarField ScalarValue), requiredSingle)
               NewRule(LeafRule(specificField "empire_unique", ValueField ValueType.Bool), optionalSingle) |]

         NewRule(NodeRule(specificField "building", inner), optionalMany))

let shipsizeLazy =
    lazy
        (let inner =
            [| NewRule(LeafRule(specificField "formation_priority", defaultInt), optionalSingle)
               NewRule(LeafRule(specificField "max_speed", defaultFloat), requiredSingle)
               NewRule(LeafRule(specificField "acceleration", defaultFloat), requiredSingle)
               NewRule(LeafRule(specificField "rotation_speed", defaultFloat), requiredSingle)
               NewRule(LeafRule(specificField "collision_radius", defaultFloat), optionalSingle)
               NewRule(LeafRule(specificField "max_hitpoints", defaultInt), requiredSingle)
               NewRule(NodeRule(specificField "modifier", [||]), optionalSingle)
               NewRule(LeafRule(specificField "size_multiplier", defaultInt), requiredSingle)
               NewRule(LeafRule(specificField "fleet_slot_size", defaultInt), requiredSingle)
               NewRule(NodeRule(specificField "section_slots", [||]), optionalSingle)
               NewRule(LeafRule(specificField "num_target_locators", defaultInt), requiredSingle)
               NewRule(LeafRule(specificField "is_space_station", ValueField ValueType.Bool), requiredSingle)
               NewRule(LeafRule(specificField "icon_frame", defaultInt), requiredSingle)
               NewRule(LeafRule(specificField "base_buildtime", defaultInt), requiredSingle)
               NewRule(LeafRule(specificField "can_have_federation_design", ValueField ValueType.Bool), requiredSingle)
               NewRule(LeafRule(specificField "enable_default_design", ValueField ValueType.Bool), requiredSingle)
               NewRule(
                   LeafRule(specificField "default_behavior", TypeField(TypeType.Simple "ship_behavior")),
                   requiredSingle
               )
               NewRule(NodeRule(specificField "prerequisites", [||]), optionalSingle)
               NewRule(LeafRule(specificField "combat_disengage_chance", defaultFloat), optionalSingle)
               NewRule(LeafRule(specificField "has_mineral_upkeep", ValueField ValueType.Bool), requiredSingle)
               NewRule(LeafRule(specificField "class", ScalarField ScalarValue), requiredSingle)
               NewRule(LeafRule(specificField "construction_type", ScalarField ScalarValue), requiredSingle)
               NewRule(LeafRule(specificField "required_component_set", ScalarField ScalarValue), requiredSingle) |]

         NewRule(NodeRule(specificField "ship_size", inner), optionalMany))

let shipBehaviorTypeLazy =
    lazy
        { name = "ship_behavior"
          nameField = Some "name"
          pathOptions =
            { paths = [| "common/ship_behaviors" |]
              pathStrict = false
              pathFile = None
              pathExtension = None }
          conditions = None
          subtypes = []
          typeKeyFilter = None
          typeKeyRegex = None
          rootCompletionFromSubtypes = false
          skipRootKey = []
          warningOnly = false
          type_per_file = false
          localisation = []
          modifiers = []
          startsWith = None
          unique = false
          shouldBeReferenced = RefNotRequired
          unknownKeyHandling = UnknownKeyIgnore
          obsoleteKeys = Map.empty
          graphRelatedTypes = []
          keyPrefix = None }

let shipSizeTypeLazy =
    lazy
        { name = "ship_size"
          pathOptions =
            { paths = [| "common/ship_sizes" |]
              pathStrict = false
              pathFile = None
              pathExtension = None }
          nameField = None
          conditions = None
          subtypes = []
          typeKeyFilter = None
          typeKeyRegex = None
          rootCompletionFromSubtypes = false
          skipRootKey = []
          warningOnly = false
          type_per_file = false
          localisation = []
          modifiers = []
          startsWith = None
          unique = false
          shouldBeReferenced = RefNotRequired
          unknownKeyHandling = UnknownKeyIgnore
          obsoleteKeys = Map.empty
          graphRelatedTypes = []
          keyPrefix = None }
//  type[ship_behavior] = {
//      path = "game/common/ship_behaviors"
//      name_field = "name"
//  }
//  type[leader_trait] = {
//      path = "game/common/traits"
//      conditions = {
//          leader_trait = yes
//      }
//  }
//  type[species_trait] = {
//      path = "game/common/traits"
//  }


let effectMap = EffectMap()
let leftScopeRule () =
    RootRule.AliasRule(
            "effect",
            (NodeRule(
                (ScopeField [ (scopeManager.ParseScope () "Any") ]),
                [| LeafRule((AliasField "effect"), (AliasField "Effect")), optionalMany |]
             ),
             optionalMany)
    )

let leftScopeLazy = lazy (leftScopeRule ())

let eopEffectRule () =
    RootRule.AliasRule(
            "effect",
            (NodeRule(
                SpecificField(SpecificValue(StringResource.stringManager.InternIdentifierToken "every_owned_planet")),
                [| LeafRule((AliasField "effect"), (AliasField "Effect")), optionalMany |]
             ),
             { optionalMany with
                 pushScope = Some(scopeManager.ParseScope () "Planet") })
    )

let eopEffectLazy = lazy (eopEffectRule ())

let logEffectRule () =
    RootRule.AliasRule(
            "effect",
            (LeafRule(
                NewField.SpecificField(SpecificValue(StringResource.stringManager.InternIdentifierToken "log")),
                ValueField(ValueType.Bool)
             ),
             { optionalMany with
                 pushScope = Some(scopeManager.ParseScope () "Planet") })
    )

let logEffectLazy = lazy (logEffectRule ())


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

let crossGameSettings<'L> folder ruleFiles langs : GameSetupSettings<'L> =
    { rootDirectories = [| WD { name = "game"; path = folder } |]
      modFilter = None
      validation =
        { validateVanilla = false
          experimental = true
          langs = langs }
      rules =
        Some
            { ruleFiles = ruleFiles
              validateRules = true
              debugRulesOnly = false
              debugMode = false }
      embedded = FromConfig([], [])
      scriptFolders = Some [| "common"; "events" |]
      excludeGlobPatterns = None
      maxFileSize = None
      debugSettings = DebugSettings.Default
      vanillaPath = None }

// Configurable root for the Stellaris config test data. Override with the
// CWTEST_STELLARIS_CONFIG environment variable to point at a live
// cwtools-stellaris-config checkout; defaults to the bundled snapshot.
let stellarisConfigRoot =
    lazy
        (let env = Environment.GetEnvironmentVariable "CWTEST_STELLARIS_CONFIG"
         if String.IsNullOrWhiteSpace env then "./testfiles/stellarisconfig" else env)

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

    let fNode =
        (fun (clause: IClause) children ->
            let one =
                clause.Leaves
                |> Seq.map (fun e ->
                    e.Position, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> snd)
                |> List.ofSeq

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

    let fNode =
        (fun (clause: IClause) children ->
            let one =
                clause.Leaves
                |> Seq.map (fun e ->
                    e.Position, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> snd)
                |> List.ofSeq

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

let testFolder folder testsname config configValidate configfile configOnly configLoc stl (culture: string) =
    testWithCapturedLogs (folder + testsname + culture)
    <| fun () ->
        Thread.CurrentThread.CurrentCulture <- CultureInfo(culture)
        Thread.CurrentThread.CurrentUICulture <- CultureInfo(culture)
        let configtext = if config then configFilesFromDir configfile else []
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

        let (game: IGame), errors, testVals, completionVals, parseErrors =
            if stl = 1 then
                let configtext =
                    ("./testfiles/validationtests/trigger_docs.log",
                     File.ReadAllText "./testfiles/validationtests/trigger_docs.log")
                    :: configtext

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
                    |> List.map (fun e -> e.message, e.range)

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
                    |> List.map (fun e -> e.message, e.range)

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
                    |> List.map (fun e -> e.message, e.range)

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
                    |> List.map (fun e -> e.message, e.range)

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

        let inner (file: string, nodekeys: range list) =
            if file.Contains "noerr" then
                ()
            else
                let expected = nodekeys |> List.map (fun nk -> "", nk)
                let fileErrors = errors |> List.filter (fun (_, f) -> f.FileName = file)
                let fileErrorPositions = fileErrors
                let missing = remove_all_by expected fileErrorPositions snd
                let extras = remove_all_by fileErrorPositions expected snd
                Expect.isEmpty
                    extras
                    $"Following lines are not expected to have an error %A{extras}, expected %A{expected}, actual %A{fileErrors}"

                Expect.isEmpty missing $"Following lines are expected to have an error %A{missing}"

        Expect.isEmpty
            parseErrors
            (parseErrors
             |> List.tryHead
             |> Option.map (sprintf "%A")
             |> Option.defaultValue "")

        testVals |> List.iter inner
        completionVals |> List.iter (completionTestPerFile game)

let testSubdirectories stl rulesonly dir =
    let dirs = Directory.EnumerateDirectories dir

    dirs
    |> Seq.map (fun d -> testFolder d "detailedconfigrules" true true d rulesonly true stl "en-GB")
