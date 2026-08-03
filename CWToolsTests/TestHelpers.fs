module TestHelpers


open System.Collections.Frozen
open Expecto
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
