module ProcessTests

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
open CWTools.Rules.RulesWrapper
open LogCaptureTest


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

[<Tests>]
let plsConfigCompatibilityTests =
    let anyScope = scopeManager.AnyScope
    let parseAnyScope _ = anyScope

    let parseField text =
        RulesParser.processTagAsField parseAnyScope anyScope Map.empty text

    let typeInfo id =
        { id = id
          validate = true
          range = range.Zero
          explicitLocalisation = []
          subtypes = [] }

    let emptyComputedData =
        lazy (STLComputedData(None, None, None, false, None, None, None))

    testSequenced
    <|
    testList
        "PLS config compatibility"
        [ testCase "recognises PLS extension data expressions"
          <| fun () ->
              match parseField "dynamic_value[event_target]" with
              | DynamicValueField "event_target" -> ()
              | other -> failtestf "Expected dynamic value field, got %A" other

              match parseField "$define_reference", parseField "$array_define_reference", parseField "$tags[law]" with
              | DefineReferenceField, ArrayDefineReferenceField, TagsField("law", false) -> ()
              | other -> failtestf "Expected PLS reference fields, got %A" other

              match parseField "$database_object", parseField "name_format[character]" with
              | DatabaseObjectField, NameFormatField "character" -> ()
              | other -> failtestf "Expected PLS database/name-format fields, got %A" other

              match
                  parseField "$shader_effect",
                  parseField "$mesh_locator",
                  parseField "$technology_with_level",
                  parseField "$parameter",
                  parseField "$parameter_value",
                  parseField "$localisation_parameter"
              with
              | ShaderEffectField,
                MeshLocatorField,
                TechnologyWithLevelField,
                ParameterField,
                ParameterValueField,
                LocalisationParameterField -> ()
              | other -> failtestf "Expected PLS dynamic reference fields, got %A" other

              match parseField "glob:*.dds", parseField "ant:on_daily_*", parseField "re:[a-z_]+" with
              | PatternField(GlobPattern, "*.dds", false),
                PatternField(AntPattern, "on_daily_*", false),
                PatternField(RegexPattern, "[a-z_]+", false) -> ()
              | other -> failtestf "Expected PLS pattern fields, got %A" other

              match parseField "ant.i:On_Daily_*", parseField "re.i:[A-Z_]+" with
              | PatternField(AntPattern, "On_Daily_*", true), PatternField(RegexPattern, "[A-Z_]+", true) -> ()
              | other -> failtestf "Expected PLS ignore-case pattern fields, got %A" other

              match parseField "abs_filepath", parseField "filename[gfx/interface]" with
              | AbsoluteFilepathField, FilenameField(Some "gfx/interface") -> ()
              | other -> failtestf "Expected PLS path reference fields, got %A" other

              match parseField "prefix_field[localisation]", parseField "prefix_field[<sprite>]" with
              | PrefixedField(LocalisationField(false, false)),
                PrefixedField(TypeField(TypeType.Simple "sprite")) -> ()
              | other -> failtestf "Expected prefixed fields, got %A" other

          testCase "parses open and closed value field ranges"
          <| fun () ->
              match parseField "value_field[0.0..inf)" with
              | ValueScopeMarkerField(false, (min, max)) ->
                  Expect.equal min 0.0M "Minimum should come from the range"
                  Expect.equal
                      max
                      RulesParserConstants.floatFieldDefaultMaximum
                      "inf should map to the default maximum"
              | other -> failtestf "Expected ranged value field, got %A" other

              match parseField "int_value_field(-100..100]" with
              | ValueScopeMarkerField(true, (min, max)) ->
                  Expect.equal min -100M "Minimum should come from the range"
                  Expect.equal max 100M "Maximum should come from the range"
              | other -> failtestf "Expected ranged int value field, got %A" other

          testCase "parses safe assignment spellings"
          <| fun () ->
              let parseOne text =
                  match CKParser.parseString text "safe_assign.txt" with
                  | Success([ KeyValue(PosKeyValue(_, KeyValueItem(key, _, op))) ], _, _) -> key, op
                  | Success(result, _, _) -> failtestf "Unexpected parse tree: %A" result
                  | Failure(e, _, _) -> failtestf "Parse failed: %s" e

              let key1, op1 = parseOne "owner ?= { x = y }"
              let key2, op2 = parseOne "owner ? = { x = y }"
              let key3, op3 = parseOne "owner? = { x = y }"

              Expect.equal (key1, op1) ("owner", Operator.QuestionEqual) "owner ?= should parse as ?="
              Expect.equal (key2, op2) ("owner", Operator.QuestionSpaceEqual) "owner ? = should preserve spaced operator"
              Expect.equal (key3, op3) ("owner?", Operator.Equals) "owner? = remains the legacy optional scope spelling"

          testCase "loads PLS link extensions"
          <| fun () ->
              let linksText =
                  String.concat
                      "\n"
                      [ "links = {"
                        "    active_outbreak = {"
                        "        input_scope = country"
                        "        output_scope = planet"
                        "        type = both"
                        "        from_argument = yes"
                        "        argument_separator = pipe"
                        "        for_definition_type = law"
                        "        prefix = active_outbreak"
                        "        data_source = <country>"
                        "        data_source = dynamic_value[event_target]"
                        "    }"
                        "}" ]

              let links =
                  UtilityParser.loadEventTargetLinks
                      anyScope
                      parseAnyScope
                      [ anyScope ]
                      "links.cwt"
                      linksText

              Expect.hasLength links 2 "Each data_source should become a data link"

              let sources =
                  links
                  |> List.choose (function
                      | DataLink l ->
                          Expect.isTrue l.fromArgument "from_argument should be preserved"
                          Expect.equal l.argumentSeparator (Some "pipe") "argument_separator should be preserved"
                          Expect.equal l.forDefinitionType (Some "law") "for_definition_type should be preserved"
                          Some l.sourceRuleType
                      | _ -> None)

              Expect.contains sources "<country>" "First data source should be preserved"
              Expect.contains sources "dynamic_value[event_target]" "Second data source should be preserved"

          testCase "parses PLS extended metadata blocks"
          <| fun () ->
              let config =
                  String.concat
                      "\n"
                      [ "priorities = {"
                        "    type[law] = replace"
                        "    \"common/governments\" = FIOS"
                        "    \"common/governments/civics\" = LIOS"
                        "}"
                        "override_modes_info = {"
                        "    LIOS = {"
                        "        ## Last In, Only Served."
                        "        ## How to override vanilla: redefine the same key in a later file."
                        "        name = \"Last In, Only Served\""
                        "    }"
                        "}"
                        "system_scopes = {"
                        "    ## Country scope"
                        "    country = {"
                        "        base_id = scope"
                        "        name = Country"
                        "    }"
                        "}"
                        "locales = {"
                        "    ## Turkish"
                        "    l_turkish = {"
                        "        supports = yes"
                        "        codes = { tr turkish }"
                        "    }"
                        "}"
                        "database_object_types = {"
                        "    law = {"
                        "        type = law"
                        "        swap_type = institution"
                        "        localisation = law_"
                        "    }"
                        "}"
                        "on_actions = {"
                        "    on_test_action = {"
                        "        ## event_type = country"
                        "        ## hint = Country event only"
                        "    }"
                        "}" ]

              let _, _, _, _, _, metadata =
                  RulesParser.parseConfigWithMetadata
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "pls.cwt"
                      config

              Expect.equal metadata.priorities.["type[law]"].strategy "replace" "Priority strategy should be parsed"
              Expect.equal metadata.priorities.["common/governments"].strategy "FIOS" "Path priority should be parsed"
              Expect.equal
                  (ExtendedConfigMetadata.tryFindPriorityForPath
                      "common/governments/civics/00_civics.txt"
                      metadata)
                  (Some metadata.priorities.["common/governments/civics"])
                  "Path priority lookup should prefer the longest matching prefix"

              Expect.equal
                  metadata.overrideModesInfo.["LIOS"].name
                  (Some "Last In, Only Served")
                  "Override mode info name should be parsed"
              Expect.isTrue
                  (metadata.overrideModesInfo.["LIOS"].description.IsSome)
                  "Override mode info description should be parsed from comments"
              Expect.stringContains
                  metadata.overrideModesInfo.["LIOS"].description.Value
                  "redefine the same key"
                  "Override mode info description should preserve multi-line ## comments inside the mode block"
              Expect.equal metadata.systemScopes.["country"].baseId (Some "scope") "System scope base_id should be parsed"
              Expect.equal metadata.locales.["l_turkish"].supports (Some true) "Locale support flag should be parsed"
              Expect.sequenceEqual metadata.locales.["l_turkish"].codes [| "tr"; "turkish" |] "Locale codes should be parsed"
              Expect.equal metadata.databaseObjectTypes.["law"].objectType (Some "law") "Database object type should be parsed"
              Expect.equal metadata.databaseObjectTypes.["law"].swapType (Some "institution") "Database object swap_type should be parsed"
              Expect.equal metadata.onActions.["on_test_action"].eventType "country" "On action event_type should be parsed"
              Expect.equal metadata.onActions.["on_test_action"].hint (Some "Country event only") "On action hint should be parsed"

          testCase "builds combined from_argument data links"
          <| fun () ->
              let linksText =
                  String.concat
                      "\n"
                      [ "links = {"
                        "    active_outbreak = {"
                        "        input_scope = country"
                        "        output_scope = state"
                        "        type = scope"
                        "        from_argument = yes"
                        "        argument_separator = pipe"
                        "        data_source = <country>"
                        "        data_source = <state>"
                        "    }"
                        "}" ]

              let links =
                  UtilityParser.loadEventTargetLinks
                      anyScope
                      parseAnyScope
                      [ anyScope ]
                      "links.cwt"
                      linksText

              let lookup = STLLookup()

              lookup.typeDefInfo <-
                  Map.ofList
                      [ "country", [| typeInfo "c1"; typeInfo "c2" |]
                        "state", [| typeInfo "s1" |] ]

              let embedded = { emptyEmbeddedSettings with eventTargetLinks = links }

              let names =
                  CWTools.Games.Helpers.addDataEventTargetLinks lookup embedded false
                  |> List.map (fun e -> CWTools.Utilities.StringResource.stringManager.GetStringForIDs e.Name)

              Expect.contains names "active_outbreak(c1|s1)" "First combined argument link should be generated"
              Expect.contains names "active_outbreak(c2|s1)" "Second combined argument link should be generated"

          testWithCapturedLogs "validates PLS pattern and parameter fields"
          <| fun () ->
              let config =
                  String.concat
                      "\n"
                      [ "pattern_rule = {"
                        "    ant:on_daily_*"
                        "    glob:portrait_*.dds"
                        "    re:ship_[0-9]+"
                        "}"
                        "scripted_effect = {"
                        "    $parameter = $parameter_value"
                        "}"
                        "gfx_rule = {"
                        "    shader = $shader_effect"
                        "    locator = $mesh_locator"
                        "    tech = $technology_with_level"
                        "    loc_param = $localisation_parameter"
                        "}" ]

              let rules, types, _, _, _, metadata =
                  RulesParser.parseConfigWithMetadata
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "pls_dynamic_fields.cwt"
                      config

              let typeRules =
                  rules
                  |> List.choose (function
                      | TypeRule(_, rs) -> Some rs
                      | _ -> None)
                  |> Array.ofList

              let apply =
                  RuleValidationService(
                      RulesWrapper(rules |> List.toArray),
                      types,
                      FrozenDictionary.Empty,
                      FrozenDictionary.Empty,
                      FrozenDictionary.Empty,
                      [||],
                      FrozenSet.Empty,
                      EffectMap(),
                      EffectMap(),
                      (scopeManager.ParseScope () "Any"),
                      changeScope,
                      defaultContext,
                      STL STLLang.Default,
                      processLocalisationLazy.Value,
                      validateLocalisationLazy.Value,
                      extendedConfigMetadata = metadata
                  )

              let validate onAction =
                  let input =
                      String.concat
                          "\n"
                          [ "pattern_rule = {"
                            $"    %s{onAction}"
                            "    portrait_city.dds"
                            "    ship_42"
                            "}"
                            "scripted_effect = {"
                            "    CUSTOM_PARAM = \"owner.GetName\""
                            "}"
                            "gfx_rule = {"
                            "    shader = PdxMeshStandard"
                            "    locator = turret_locator"
                            "    tech = tech_lasers@3"
                            "    loc_param = Root.GetName"
                            "}" ]

                  match CKParser.parseString input "pls_dynamic_fields.txt" with
                  | Success(r, _, _) ->
                      let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                      apply.ApplyNodeRule(typeRules, node)
                  | Failure(e, _, _) -> failtest e

              match validate "on_daily_country_tag" with
              | OK -> ()
              | Invalid(_, errors) -> failtestf "Valid PLS dynamic fields should pass, got %A" errors

              match validate "on_yearly_country_tag" with
              | OK -> failtest "Value outside the ant: pattern should fail"
              | Invalid _ -> ()

          testCase "preserves PLS file extension and color metadata"
          <| fun () ->
              let config =
                  String.concat
                      "\n"
                      [ "sprite = {"
                        "    ## file_extensions = { png dds tga }"
                        "    texturefile = filepath"
                        "    ## color_type = hsv"
                        "    color = colour[hsv]"
                        "}" ]

              let rules, _, _, _, _, _ =
                  RulesParser.parseConfigWithMetadata
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "pls_file_metadata.cwt"
                      config

              let innerRules =
                  rules
                  |> List.tryPick (function
                      | TypeRule("sprite", (NodeRule(_, inner), _)) -> Some inner
                      | _ -> None)
                  |> Option.defaultWith (fun () -> failtest "Expected sprite root rule")

              let optionsFor predicate =
                  innerRules
                  |> Array.tryPick (fun (rule, options) ->
                      if predicate rule then Some options else None)
                  |> Option.defaultWith (fun () -> failtest "Expected matching child rule")

              let fileOptions =
                  optionsFor (function
                      | LeafRule(_, FilepathField _) -> true
                      | _ -> false)

              let colorOptions =
                  optionsFor (function
                      | NodeRule(_, _) -> true
                      | _ -> false)

              Expect.sequenceEqual fileOptions.fileExtensions [ "png"; "dds"; "tga" ] "file_extensions should be preserved"
              Expect.equal colorOptions.colorType (Some "hsv") "color_type should be preserved"

          testWithCapturedLogs "uses PLS file extensions for filepath validation"
          <| fun () ->
              let config =
                  String.concat
                      "\n"
                      [ "asset = {"
                        "    ## file_extensions = { dds png }"
                        "    texture = filepath"
                        "}" ]

              let rules, types, _, _, _, metadata =
                  RulesParser.parseConfigWithMetadata
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "pls_file_extensions.cwt"
                      config

              let typeRules =
                  rules
                  |> List.choose (function
                      | TypeRule(_, rs) -> Some rs
                      | _ -> None)
                  |> Array.ofList

              let files =
                  [| "gfx/icons/portrait.dds"; "gfx/icons/portrait.png"; "gfx/icons/portrait.txt" |]
                      .ToFrozenSet(System.StringComparer.OrdinalIgnoreCase)

              let apply =
                  RuleValidationService(
                      RulesWrapper(rules |> List.toArray),
                      types,
                      FrozenDictionary.Empty,
                      FrozenDictionary.Empty,
                      FrozenDictionary.Empty,
                      [||],
                      files,
                      EffectMap(),
                      EffectMap(),
                      (scopeManager.ParseScope () "Any"),
                      changeScope,
                      defaultContext,
                      STL STLLang.Default,
                      processLocalisationLazy.Value,
                      validateLocalisationLazy.Value,
                      extendedConfigMetadata = metadata
                  )

              let validate value =
                  let input = $"asset = {{\n    texture = \"%s{value}\"\n}}"

                  match CKParser.parseString input "pls_file_extensions.txt" with
                  | Success(r, _, _) ->
                      let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                      apply.ApplyNodeRule(typeRules, node)
                  | Failure(e, _, _) -> failtest e

              match validate "gfx/icons/portrait.dds", validate "gfx/icons/portrait" with
              | OK, OK -> ()
              | explicitResult, inferredResult ->
                  failtestf
                      "Allowed explicit and inferred file extensions should pass, got %A and %A"
                      explicitResult
                      inferredResult

              match validate "gfx/icons/portrait.txt" with
              | OK -> failtest "Existing file with an extension outside file_extensions should fail"
              | Invalid _ -> ()

          testWithCapturedLogs "validates PLS absolute filepath and filename fields"
          <| fun () ->
              let config =
                  String.concat
                      "\n"
                      [ "asset = {"
                        "    path = abs_filepath"
                        "    icon = filename[gfx/interface]"
                        "}" ]

              let rules, types, _, _, _, metadata =
                  RulesParser.parseConfigWithMetadata
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "pls_path_fields.cwt"
                      config

              let typeRules =
                  rules
                  |> List.choose (function
                      | TypeRule(_, rs) -> Some rs
                      | _ -> None)
                  |> Array.ofList

              let files =
                  [| "gfx/interface/asset_icon.dds" |].ToFrozenSet(System.StringComparer.OrdinalIgnoreCase)

              let apply =
                  RuleValidationService(
                      RulesWrapper(rules |> List.toArray),
                      types,
                      FrozenDictionary.Empty,
                      FrozenDictionary.Empty,
                      FrozenDictionary.Empty,
                      [||],
                      files,
                      EffectMap(),
                      EffectMap(),
                      (scopeManager.ParseScope () "Any"),
                      changeScope,
                      defaultContext,
                      STL STLLang.Default,
                      processLocalisationLazy.Value,
                      validateLocalisationLazy.Value,
                      extendedConfigMetadata = metadata
                  )

              let validate path icon =
                  let input = $"asset = {{\n    path = \"%s{path}\"\n    icon = \"%s{icon}\"\n}}"

                  match CKParser.parseString input "pls_path_fields.txt" with
                  | Success(r, _, _) ->
                      let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                      apply.ApplyNodeRule(typeRules, node)
                  | Failure(e, _, _) -> failtest e

              match validate "C:/mods/example" "asset_icon.dds" with
              | OK -> ()
              | Invalid(_, errors) -> failtestf "Valid absolute path and filename should pass, got %A" errors

              match validate "relative/mods/example" "asset_icon.dds" with
              | OK -> failtest "Relative path should not match abs_filepath"
              | Invalid _ -> ()

              match validate "C:/mods/example" "nested/asset_icon.dds" with
              | OK -> failtest "Nested path should not match filename"
              | Invalid _ -> ()

          testCase "applies PLS color type metadata to color fields"
          <| fun () ->
              let config =
                  String.concat
                      "\n"
                      [ "palette = {"
                        "    ## color_type = rgb"
                        "    tint = color_field"
                        "    ## color_type = hex"
                        "    tint_hex = color_field"
                        "}" ]

              let rules, _, _, _, _, _ =
                  RulesParser.parseConfigs
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      true
                      false
                      [ "pls_color_type.cwt", config ]

              let innerRules =
                  rules
                  |> Array.tryPick (function
                      | TypeRule("palette", (NodeRule(_, inner), _)) -> Some inner
                      | _ -> None)
                  |> Option.defaultWith (fun () -> failtest "Expected palette root rule")

              let tryRule name =
                  innerRules
                  |> Array.tryPick (fun (rule, _) ->
                      match rule with
                      | NodeRule(SpecificField(SpecificValue value), _)
                          when CWTools.Utilities.StringResource.stringManager.GetStringForID value.normal = name ->
                          Some rule
                      | LeafRule(SpecificField(SpecificValue value), _)
                          when CWTools.Utilities.StringResource.stringManager.GetStringForID value.normal = name ->
                          Some rule
                      | _ -> None)
                  |> Option.defaultWith (fun () -> failtestf "Expected %s rule" name)

              match tryRule "tint" with
              | NodeRule(_, [| LeafValueRule(ValueField(ValueType.Float(min, max))), options |]) ->
                  Expect.equal min 0.0M "rgb color minimum should be applied"
                  Expect.equal max 255.0M "rgb color maximum should be applied"
                  Expect.equal options.min 3 "rgb color should require at least 3 channels"
                  Expect.equal options.max 4 "rgb color should allow alpha"
              | other -> failtestf "Expected rgb color node rule, got %A" other

              match tryRule "tint_hex" with
              | LeafRule(_, ScalarField ScalarValue) -> ()
              | other -> failtestf "Expected hex color scalar rule, got %A" other

          testCase "applies PLS config inject metadata without recursive expansion"
          <| fun () ->
              let source =
                  String.concat
                      "\n"
                      [ "injected_group = {"
                        "    injected1 = 1"
                        "    injected2 = 2"
                        "}" ]

              let target =
                  String.concat
                      "\n"
                      [ "## inject = common/test/injection_source.cwt@injected_group/*"
                        "target_block = {"
                        "    existing = 0"
                        "}" ]

              let rules, _, _, _, _, _ =
                  RulesParser.parseConfigs
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      true
                      false
                      [ "common/test/injection_source.cwt", source
                        "common/test/injection_target.cwt", target ]

              let injectedNames =
                  rules
                  |> Array.tryPick (function
                      | TypeRule("target_block", (NodeRule(_, inner), _)) ->
                          inner
                          |> Array.choose (function
                              | LeafRule(SpecificField(SpecificValue value), _), _ ->
                                  Some(
                                      CWTools.Utilities.StringResource.stringManager.GetStringForID value.normal
                                  )
                              | _ -> None)
                          |> Some
                      | _ -> None)
                  |> Option.defaultWith (fun () -> failtest "Expected target block rule")

              Expect.contains injectedNames "existing" "Existing child rule should remain"
              Expect.contains injectedNames "injected1" "Injected child rule should be added"
              Expect.contains injectedNames "injected2" "Injected child rule should be added"

          testCase "preserves PLS type key regex filters"
          <| fun () ->
              let config =
                  String.concat
                      "\n"
                      [ "types = {"
                        "    ## type_key_regex = \"^ship_.*$\""
                        "    type[ship_design] = {"
                        "        path = common/ship_designs"
                        "    }"
                        "}" ]

              let _, types, _, _, _, _ =
                  RulesParser.parseConfigWithMetadata
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "pls_type_key_regex.cwt"
                      config

              match types with
              | [ typeDef ] -> Expect.equal typeDef.typeKeyRegex (Some "^ship_.*$") "type_key_regex should be parsed"
              | other -> failtestf "Expected one type definition, got %A" other

          testCase "keeps recursive single aliases bounded"
          <| fun () ->
              let config =
                  String.concat
                      "\n"
                      [ "single_alias[recursive_color_clause] = {"
                        "    int = color_field"
                        "    special_selection = single_alias_right[recursive_color_clause]"
                        "}"
                        "color_list = {"
                        "    int = single_alias_right[recursive_color_clause]"
                        "}" ]

              let rules, _, _, _, _, _ =
                  RulesParser.parseConfigs
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      true
                      false
                      [ "recursive_alias.cwt", config ]

              Expect.isGreaterThan rules.Length 0 "Recursive single aliases should parse without unbounded expansion"

          testCase "parses external PLS rule samples without importing them"
          <| fun () ->
              let root = System.Environment.GetEnvironmentVariable("CWTOOLS_PLS_CONFIG_ROOT")

              if not (System.String.IsNullOrWhiteSpace root) && Directory.Exists root then
                  let scanRoot =
                      let cwtRoot = Path.Combine(root, "cwt")

                      if Directory.Exists cwtRoot then
                          cwtRoot
                      else
                          root

                  let failures = ResizeArray<string>()

                  // Compatibility smoke only: external PLS rules are parse samples, not bundled game rules.
                  let knownMalformedExternalSample (file: string) =
                      let normalized = file.Replace('\\', '/')

                      [ "/cwtools-vic2-config/history/history_consolidated.cwt"
                        "/cwtools-stellaris-config/config/common/leader_classes.cwt"
                        "/cwtools-stellaris-config/config/gfx/asset_selectors.cwt" ]
                      |> List.exists (fun known ->
                          normalized.EndsWith(known, System.StringComparison.OrdinalIgnoreCase))

                  Directory.EnumerateFiles(scanRoot, "*.cwt", SearchOption.AllDirectories)
                  |> Seq.filter (fun file ->
                      not (file.Contains($"{Path.DirectorySeparatorChar}.git{Path.DirectorySeparatorChar}"))
                      && not (knownMalformedExternalSample file))
                  |> Seq.iter (fun file ->
                      let text = File.ReadAllText file

                      match CKParser.parseString text file with
                      | Failure(e, _, _) -> failures.Add($"{file}: {e}")
                      | Success _ ->
                          try
                              RulesParser.parseConfigWithMetadata
                                  (scopeManager.ParseScope())
                                  scopeManager.AllScopes
                                  (scopeManager.ParseScope () "Any")
                                  scopeManager.ScopeGroups
                                  file
                                  text
                              |> ignore
                          with ex ->
                              failures.Add($"{file}: {ex.Message}"))

                  let failureList = failures |> Seq.truncate 20 |> Seq.toList
                  Expect.isEmpty
                      failureList
                      ("External PLS config samples should parse when CWTOOLS_PLS_CONFIG_ROOT is set. Failures:\n"
                       + String.concat "\n" failureList)

          testWithCapturedLogs "validates configured database_object fields"
          <| fun () ->
              let config =
                  String.concat
                      "\n"
                      [ "types = {"
                        "    type[law] = { path = \"game/common/laws\" }"
                        "    type[institution] = { path = \"game/common/institutions\" }"
                        "}"
                        "database_object_types = {"
                        "    law = {"
                        "        type = law"
                        "        swap_type = institution"
                        "        localisation = law_"
                        "    }"
                        "}"
                        "test_object = {"
                        "    ## cardinality = 1..1"
                        "    object = $database_object"
                        "}" ]

              let rules, types, _, _, _, metadata =
                  RulesParser.parseConfigWithMetadata
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "database_object.cwt"
                      config

              let typeRules =
                  rules
                  |> List.choose (function
                      | TypeRule(_, rs) -> Some rs
                      | _ -> None)
                  |> Array.ofList

              let typeMap =
                  [ "law", createStringSet [ "free_speech" ]
                    "institution", createStringSet [ "schools" ] ]
                  |> Map.ofList

              let apply =
                  RuleValidationService(
                      RulesWrapper(rules |> List.toArray),
                      types,
                      typeMap.ToFrozenDictionary(),
                      FrozenDictionary.Empty,
                      FrozenDictionary.Empty,
                      [||],
                      FrozenSet.Empty,
                      EffectMap(),
                      EffectMap(),
                      (scopeManager.ParseScope () "Any"),
                      changeScope,
                      defaultContext,
                      STL STLLang.Default,
                      processLocalisationLazy.Value,
                      validateLocalisationLazy.Value,
                      extendedConfigMetadata = metadata
                  )

              let validate value =
                  let input = $"test_object = {{\n    object = \"%s{value}\"\n}}"

                  match CKParser.parseString input "database_object.txt" with
                  | Success(r, _, _) ->
                      let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                      apply.ApplyNodeRule(typeRules, node)
                  | Failure(e, _, _) -> failtest e

              match validate "law:free_speech:schools" with
              | OK -> ()
              | Invalid(_, errors) -> failtestf "Valid database object should pass, got %A" errors

              match validate "law:missing:schools" with
              | OK -> failtest "Unknown database object id should fail"
              | Invalid(_, errors) -> Expect.hasLength errors 1 "Only the unknown object id should be reported"

              match validate "law:free_speech:missing" with
              | OK -> failtest "Unknown database object swap id should fail"
              | Invalid(_, errors) -> Expect.hasLength errors 1 "Only the unknown swap id should be reported"

              match validate "unknown:free_speech" with
              | OK -> failtest "Unknown database object prefix should fail"
              | Invalid(_, errors) -> Expect.hasLength errors 1 "Only the unknown prefix should be reported"

          testWithCapturedLogs "validates configured on_action event types"
          <| fun () ->
              let config =
                  String.concat
                      "\n"
                      [ "on_actions = {"
                        "    on_test_action = {"
                        "        ## event_type = country"
                        "    }"
                        "}" ]

              let _, _, _, _, _, metadata =
                  RulesParser.parseConfigWithMetadata
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "on_actions.cwt"
                      config

              let input =
                  "on_test_action = {\n\
                       events = { country.1 character.1 }\n\
                   }"

              match CKParser.parseString input "common/on_actions/test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r

                  let entity =
                      { filepath = "common/on_actions/test.txt"
                        logicalpath = "common/on_actions/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.OnActions
                        overwrite = Overwrite.No }

                  let lookup = STLLookup()
                  lookup.extendedConfigMetadata <- metadata

                  lookup.typeDefInfo <-
                      Map.ofList
                          [ "country_event", [| typeInfo "country.1" |]
                            "character_event", [| typeInfo "character.1" |] ]

                  let entities = EntitySet<STLComputedData>([ struct (entity, emptyComputedData) ])

                  match CWTools.Validation.Common.CommonValidation.validateConfiguredOnActionEventTypes lookup entities entities with
                  | OK -> failtest "Wrong event type should be reported"
                  | Invalid(_, errors) ->
                      Expect.hasLength errors 1 "Only the character event should be reported"
                      Expect.stringContains (errors |> List.head).message "expects country events" "Message should name the expected event type"
              | Failure(e, _, _) -> failtest e

          testWithCapturedLogs "validates definition injection targets"
          <| fun () ->
              let input =
                  "REPLACE:known_target = { }\n\
                   REPLACE:missing_target = { }\n\
                   TRY_REPLACE:missing_target = { }\n\
                   REPLACE_OR_CREATE:new_target = { }"

              match CKParser.parseString input "common/laws/test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r

                  let entity =
                      { filepath = "common/laws/test.txt"
                        logicalpath = "common/laws/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Other
                        overwrite = Overwrite.No }

                  let lookup = STLLookup()

                  lookup.typeDefInfo <-
                      Map.ofList [ "law", [| typeInfo "known_target" |] ]

                  let entities = EntitySet<STLComputedData>([ struct (entity, emptyComputedData) ])

                  match CWTools.Validation.Common.CommonValidation.validateDefinitionInjections lookup entities entities with
                  | OK -> failtest "Strict injection mode should report a missing target"
                  | Invalid(_, errors) ->
                      Expect.hasLength errors 1 "Only strict REPLACE should report the missing target"
                      Expect.stringContains (errors |> List.head).message "missing_target" "Message should name the missing target"
              | Failure(e, _, _) -> failtest e ]

[<Tests>]
let legacyLocalisationCommandTests =
    let validate command =
        let staticSettings: CWTools.Process.Localisation.LegacyLocStaticSettings =
            { questionMarkVariable = true
              usesVariableCommands = false
              parameterVariables = true
              locPrimaryScopes = [ "From", id ]
              scopedLocEffectsMap = EffectMap()
              commands = []
              variableCommands = [] }

        CWTools.Process.Localisation.ChangeLocScope.createLegacyLocalisationCommandValidator
            staticSettings
            (dynamicSettings ())
            defaultContext
            command

    testList
        "legacy localisation commands"
        [ testCase "empty command segments do not throw"
          <| fun () ->
              [ "From..From.GetName"; ".From"; "From."; "?" ]
              |> List.iter (fun command ->
                  match validate command with
                  | CWTools.Process.Localisation.LocNotFound "" -> ()
                  | result -> failtestf "Expected an empty segment in %A to be invalid, got %A" command result)

          testCase "lowercase variable fallback is preserved"
          <| fun () ->
              match validate "myVariable" with
              | CWTools.Process.Localisation.Found "variable_fallback" -> ()
              | result -> failtestf "Expected lowercase variable fallback, got %A" result ]

let createStarbaseLazy =
    lazy
        (let owner =
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

         rule)

let createStarbaseAliasLazy = lazy AliasRule("effect", createStarbaseLazy.Value)

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

[<Tests>]
let testc =
    testList
        "config parse"
        [ testWithCapturedLogs "simple parse"
          <| fun () ->
              let config =
                  "create_starbase = {\n\
                          ## cardinality = 1..1\n\
                          owner = scalar\n\
                          ## cardinality = 1..1\n\
                          size = scalar\n\
                          ## cardinality = 0..100\n\
                          module = scalar\n\
                          ## cardinality = 0..100\n\
                          building = scalar\n\
                          ## cardinality = 0..1\n\
                          effect = effect\n\
                          }"

              let rules, _, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let Typerules =
                  rules
                  |> List.choose (function
                      | TypeRule(_, rs) -> Some(rs)
                      | _ -> None)

              let input =
                  "create_starbase = {\n\
                            owner = this \n\
                            owner = this \n\
                            size = large \n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let apply =
                      RuleValidationService(
                          RulesWrapper(rules |> List.toArray),
                          [],
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

                  let errors = apply.ApplyNodeRule(Typerules |> Array.ofList, node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) ->
                      Expect.equal es.Length 1 $"Following lines are not expected to have an error %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test error_unknown_keys reports unknown type keys"
          <| fun () ->
              let config =
                  "types = {\n\
                          type[game_rule] = {\n\
                          path = \"game/common/game_rules\"\n\
                          error_unknown_keys = yes\n\
                          ## type_key_filter = can_declare_war\n\
                          subtype[can_declare_war] = {\n\
                          }\n\
                          ## type_key_filter = can_add_claim\n\
                          subtype[can_add_claim] = {\n\
                          }\n\
                          }\n\
                          }\n\
                          game_rule = {\n\
                          }"

              let rules, types, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let input =
                  "can_declare_war = {\n\
                            }\n\
                            can_declar_war = {\n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let apply =
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

                  let errors =
                      apply.ManualRuleValidate("common/game_rules/test.txt", node)

                  match errors with
                  | OK -> Expect.isTrue false "Expected an unknown key error for can_declar_war"
                  | Invalid(_, es) ->
                      Expect.equal es.Length 1 $"Expected exactly one unknown key error %A{es}"

                      Expect.stringContains
                          (es |> List.head).message
                          "is not a known game_rule key"
                          "Error message should explain the unknown key"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test error_unknown_keys suggest mode only flags near misses"
          <| fun () ->
              let config =
                  "types = {\n\
                          type[on_action] = {\n\
                          path = \"game/common/on_actions\"\n\
                          error_unknown_keys = suggest\n\
                          ## type_key_filter = on_game_start\n\
                          subtype[on_game_start] = {\n\
                          }\n\
                          ## type_key_filter = on_monthly_pulse\n\
                          subtype[on_monthly_pulse] = {\n\
                          }\n\
                          }\n\
                          }\n\
                          on_action = {\n\
                          }"

              let rules, types, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let input =
                  "on_game_start = {\n\
                            }\n\
                            on_gamestart = {\n\
                            }\n\
                            on_my_totally_custom_action = {\n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let apply =
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

                  let errors =
                      apply.ManualRuleValidate("common/on_actions/test.txt", node)

                  match errors with
                  | OK -> Expect.isTrue false "Expected a suggestion for on_gamestart"
                  | Invalid(_, es) ->
                      Expect.equal
                          es.Length
                          1
                          $"Custom on_action keys must not be flagged; only the near miss should be %A{es}"

                      let error = es |> List.head
                      Expect.stringContains error.message "did you mean 'on_game_start'" "Should suggest the close key"
                      Expect.equal error.severity Severity.Information "Suggestion should be information severity"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test obsolete_keys reports removed and renamed keys"
          <| fun () ->
              let config =
                  "types = {\n\
                          type[on_action] = {\n\
                          path = \"game/common/on_actions\"\n\
                          error_unknown_keys = suggest\n\
                          should_be_used = unless_subtyped\n\
                          obsolete_keys = {\n\
                          on_planet_conquer = \"removed from the game\"\n\
                          on_planet_zero_pops = \"renamed to on_colony_zero_pops\"\n\
                          }\n\
                          ## type_key_filter = on_game_start\n\
                          subtype[on_game_start] = {\n\
                          }\n\
                          }\n\
                          }\n\
                          on_action = {\n\
                          }"

              let rules, types, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let input =
                  "on_planet_conquer = {\n\
                            }\n\
                            on_my_totally_custom_action = {\n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let apply =
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

                  let errors =
                      apply.ManualRuleValidate("common/on_actions/test.txt", node)

                  match errors with
                  | OK -> Expect.isTrue false "Expected an obsolete key warning for on_planet_conquer"
                  | Invalid(_, es) ->
                      Expect.equal es.Length 1 $"Only the obsolete key should be flagged %A{es}"

                      let error = es |> List.head
                      Expect.stringContains error.message "obsolete on_action key" "Should explain the key is obsolete"
                      Expect.stringContains error.message "removed from the game" "Should carry the configured message"
                      Expect.equal error.severity Severity.Warning "Obsolete key in open key set should be a warning"
              | Failure(e, _, _) -> Expect.isTrue false e

              let lookup = STLLookup()
              lookup.typeDefs <- types
              lookup.typeDefInfo <-
                  Map.ofList
                      [ "on_action",
                        [| { id = "on_planet_conquer"
                             validate = true
                             range = range.Zero
                             explicitLocalisation = []
                             subtypes = [] } |] ]

              let emptySet = EntitySet<STLComputedData>(Seq.empty)

              let unusedErrors =
                  CWTools.Validation.Common.CommonValidation.validateUnusuedTypes lookup emptySet emptySet

              Expect.equal unusedErrors OK "Obsolete on_action keys should not also be reported as unused"

          ]

let leftScopeLazy =
    lazy
        RootRule.AliasRule(
            "effect",
            (NodeRule(
                (ScopeField [ (scopeManager.ParseScope () "Any") ]),
                [| LeafRule((AliasField "effect"), (AliasField "Effect")), optionalMany |]
             ),
             optionalMany)
        )

let eopEffectLazy =
    lazy
        RootRule.AliasRule(
            "effect",
            (NodeRule(
                SpecificField(SpecificValue(StringResource.stringManager.InternIdentifierToken "every_owned_planet")),
                [| LeafRule((AliasField "effect"), (AliasField "Effect")), optionalMany |]
             ),
             { optionalMany with
                 pushScope = Some(scopeManager.ParseScope () "Planet") })
        )

let logEffectLazy =
    lazy
        RootRule.AliasRule(
            "effect",
            (LeafRule(
                NewField.SpecificField(SpecificValue(StringResource.stringManager.InternIdentifierToken "log")),
                ValueField(ValueType.Bool)
             ),
             { optionalMany with
                 pushScope = Some(scopeManager.ParseScope () "Planet") })
        )

[<Tests>]
let testsv =
    testList
        "config validate"
        [ testCase "stellaris default scopes include colony fallback"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))

              Expect.equal
                  ((scopeManager.ParseScope () "colony").ToString())
                  "Colony"
                  "colony should not fall back to Any when scopes.cwt is unavailable"

          testCase "scope context uses nested replace_scope from type rules"
          <| fun () ->
              let scopesConfig =
                  "scopes = {\n\
                       Planet = { aliases = { planet } }\n\
                       Colony = { aliases = { colony } }\n\
                   }\n"

              let config =
                  "types = {\n\
                       type[colony_automation] = {\n\
                           path = \"game/common/colony_automation\"\n\
                       }\n\
                   }\n\
                   ## push_scope = planet\n\
                   colony_automation = {\n\
                       ## replace_scope = { this = colony root = colony }\n\
                       available = {\n\
                           alias_name[trigger] = alias_match_left[trigger]\n\
                       }\n\
                   }\n"

              UtilityParser.initializeScopes (Some("scopes.cwt", scopesConfig)) None

              let rules, types, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "colony.cwt"
                      config

              let input =
                  "auto_colony = {\n\
                       available = {\n\
                           has_designation = col_adf_ring_city\n\
                       }\n\
                   }\n"

              match CKParser.parseString input "common/colony_automation/test.txt" with
              | Success(r, _, _) ->
                  let node =
                      STLProcess.shipProcess.ProcessNode () "root" range.Zero r

                  let entity =
                      { filepath = "common/colony_automation/test.txt"
                        logicalpath = "common/colony_automation/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Other
                        overwrite = Overwrite.No }

                  let rulesWrapper = RulesWrapper(rules |> List.toArray)

                  let validationService =
                      RuleValidationService(
                          rulesWrapper,
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

                  let infoService =
                      InfoService(
                          rulesWrapper,
                          types,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          validationService,
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  match infoService.GetInfo(mkPos 3 13, entity) with
                  | Some(context, _) ->
                      Expect.equal context.Root (scopeManager.ParseScope () "Colony") "ROOT should use replace_scope"
                      Expect.sequenceEqual context.Scopes [ scopeManager.ParseScope () "Colony" ] "THIS should use replace_scope"
                  | None -> failtest "info failed"
              | Failure(e, _, _) -> failtest e

          testWithCapturedLogs "create_starbase"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = root \n\
                            size = large \n\
                            module = trafficControl \n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let enums =
                      [ ("size", ("size", [ "medium"; "large" ]))
                        ("module", ("module", [ "trafficControl" ])) ]
                      |> Map.ofList
                      |> Map.toSeq
                      |> Seq.map (fun (k, (d, s)) -> k, (d, createStringSet s))
                      |> Map.ofSeq

                  let rules =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [],
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
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

                  let errors = rules.ApplyNodeRule([| createStarbaseLazy.Value |], node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) -> Expect.isEmpty es $"should be empty: %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "create_starbase fail"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = root \n\
                            size = fake \n\
                            module = faker \n\
                            unknown = test
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let enums =
                      createStarbaseEnumsLazy.Value
                      |> Map.toSeq
                      |> Seq.map (fun (k, (d, s)) -> k, (d, createStringSet s))
                      |> Map.ofSeq

                  let rules =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [],
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
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

                  let errors = rules.ApplyNodeRule([| createStarbaseLazy.Value |], node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) ->
                      Expect.equal es.Length 3 $"Following lines are not expected to have an error %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "create_starbase min count"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let enums =
                      [ ("size", [ "medium"; "large" ]) ]
                      |> Map.ofList
                      |> Map.toSeq
                      |> Seq.map (fun (k, s) -> k, createStringSet s)
                      |> Map.ofSeq

                  let rules =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
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

                  let errors = rules.ApplyNodeRule([| createStarbaseLazy.Value |], node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) ->
                      Expect.equal 2 es.Length $"Following lines are not expected to have an error %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "create_starbase max count"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = this \n\
                            owner = this \n\
                            size = large \n\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let enums =
                      [ ("size", ("size", [ "medium"; "large" ])) ]
                      |> Map.ofList
                      |> Map.toSeq
                      |> Seq.map (fun (k, (d, s)) -> k, (d, createStringSet s))
                      |> Map.ofSeq

                  let rules =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [],
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
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

                  let errors = rules.ApplyNodeRule([| createStarbaseLazy.Value |], node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) ->
                      Expect.equal es.Length 1 $"Following lines are not expected to have an error %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "type suffix pattern validation"
          <| fun () ->
              let config =
                  "planet_class = {\n\
                          ## cardinality = 0..1\n\
                          entity = \"\"\n\
                          ## cardinality = 0..1\n\
                          ## type_suffix_pattern = _$_entity\n\
                          entity = <model_entity>\n\
                          }"

              let rules, _, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let typeRules =
                  rules
                  |> List.choose (function
                      | TypeRule(_, rs) -> Some rs
                      | _ -> None)
                  |> Array.ofList

              let typesMap =
                  [ "model_entity", createStringSet [ "desert_planet_01_entity"; "continental_planet_02_entity" ] ]
                  |> Map.ofList
                  |> fun m -> m.ToFrozenDictionary()

              let apply =
                  RuleValidationService(
                      RulesWrapper(rules |> List.toArray),
                      [],
                      typesMap,
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

              let validate input =
                  match CKParser.parseString input "test" with
                  | Success(r, _, _) ->
                      let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                      apply.ApplyNodeRule(typeRules, node)
                  | Failure(e, _, _) -> failtest e

              Expect.equal
                  (validate
                      "planet_class = {\n\
                          entity = desert_planet\n\
                      }")
                  OK
                  "desert_planet should resolve through desert_planet_01_entity"

              Expect.equal
                  (validate
                      "planet_class = {\n\
                          entity = desert_planet_01_entity\n\
                      }")
                  OK
                  "exact model_entity values should remain legal"

              Expect.equal
                  (validate
                      "planet_class = {\n\
                          entity = \"\"\n\
                      }")
                  OK
                  "empty entity should remain legal"

              match
                  validate
                      "planet_class = {\n\
                          entity = desert\n\
                      }"
              with
              | OK -> failtest "desert should not match desert_planet_01_entity by prefix only"
              | Invalid _ -> ()
          testWithCapturedLogs "type prefix from dynamic scope values"
          <| fun () ->
              let config =
                  "planet_entity = {\n\
                          ## cardinality = 0..1\n\
                          ## type_prefix_from = graphical_culture\n\
                          entity = <model_entity>\n\
                          ## cardinality = 0..1\n\
                          graphical_culture = scalar\n\
                          }"

              let rules, _, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      ""
                      config

              let typeRules =
                  rules
                  |> List.choose (function
                      | TypeRule(_, rs) -> Some rs
                      | _ -> None)
                  |> Array.ofList

              let typesMap =
                  [ "graphical_culture", createStringSet [ "mammalian_01"; "reptilian_01" ]
                    "model_entity", createStringSet [ "mammalian_01_habitat_phase_03_entity" ] ]
                  |> Map.ofList
                  |> fun m -> m.ToFrozenDictionary()

              let apply =
                  RuleValidationService(
                      RulesWrapper(rules |> List.toArray),
                      [],
                      typesMap,
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

              let validate input =
                  match CKParser.parseString input "test" with
                  | Success(r, _, _) ->
                      let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                      apply.ApplyNodeRule(typeRules, node)
                  | Failure(e, _, _) -> failtest e

              Expect.equal
                  (validate
                      "planet_entity = {\n\
                          entity = habitat_phase_03_entity\n\
                          graphical_culture = root\n\
                      }")
                  OK
                  "scope graphical culture should try known graphical culture prefixes"

              Expect.equal
                  (validate
                      "planet_entity = {\n\
                          entity = habitat_phase_03_entity\n\
                          graphical_culture = mammalian_01\n\
                      }")
                  OK
                  "explicit matching graphical culture should resolve the prefixed entity"

              match
                  validate
                      "planet_entity = {\n\
                          entity = habitat_phase_03_entity\n\
                          graphical_culture = reptilian_01\n\
                      }"
              with
              | OK -> failtest "explicit known graphical culture should not try unrelated prefixes"
              | Invalid _ -> ()

              match
                  validate
                      "planet_entity = {\n\
                          entity = habitat_phase_03_entity\n\
                          graphical_culture = no\n\
                      }"
              with
              | OK -> failtest "explicit no should disable type prefix fallback"
              | Invalid _ -> ()
          testWithCapturedLogs "create_starbase effect in effect"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = this \n\
                            size = large \n\
                            effect = {\n\
                            create_starbase = {\
                            owner = this \n size = large\n\
                            }\
                            }\
                            }"

              match CKParser.parseString input "test" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let enums =
                      [ ("size", ("size", [ "medium"; "large" ])) ]
                      |> Map.ofList
                      |> Map.toSeq
                      |> Seq.map (fun (k, (d, s)) -> k, (d, createStringSet s))
                      |> Map.ofSeq

                  let rules =
                      RuleValidationService(
                          RulesWrapper
                              [| TypeRule("create_starbase", createStarbaseLazy.Value)
                                 createStarbaseAliasLazy.Value |],
                          [],
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
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

                  let errors = rules.ApplyNodeRule([| createStarbaseLazy.Value |], node)

                  match errors with
                  | OK -> ()
                  | Invalid(_, es) ->
                      Expect.equal es.Length 0 $"Following lines are not expected to have an error %A{es}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "test rhs completion"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = this \n\
                            size = large \n\
                            }"
              // let resource = makeEntityResourceInput filepath filetext
              // match resourceManager.ManualProcessResource resource, infoService with
              // |Some e, Some info ->

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let enums =
                      [ ("size", ("size", [ "medium"; "large" ])) ]
                      |> Map.ofList
                      |> Map.toSeq
                      |> Seq.map (fun (k, (d, s)) -> k, (d, createStringSet s))
                      |> Map.ofSeq

                  let comp =
                      CompletionService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          enums.ToFrozenDictionary(),
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          [],
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          [],
                          STL STLLang.Default,
                          emptyDataTypesLazy.Value,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let pos = mkPos 3 8

                  let suggestions =
                      comp.Complete(pos, entity, None, None)
                      |> Seq.map (function
                          | CompletionResponse.Simple(c, _, _) -> c
                          | Snippet(l, _, _, _, _) -> l
                          | Detailed _ -> failwith "todo")
                      |> Seq.sort

                  let expected = [ "medium"; "large" ] |> Seq.sort
                  Expect.sequenceEqual suggestions expected "Completion should match"
              | Failure(e, _, _) -> Expect.isTrue false e
          testWithCapturedLogs "test lhs completion"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                            owner = this \n\
                            size \n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let comp =
                      CompletionService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          [],
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          [],
                          STL STLLang.Default,
                          emptyDataTypesLazy.Value,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let pos = mkPos 3 3

                  let suggestions =
                      comp.Complete(pos, entity, None, None)
                      |> Seq.map (function
                          | Simple(c, _, _) -> c
                          | Snippet(l, _, _, _, _) -> l
                          | Detailed _ -> failwith "todo")
                      |> Seq.sort

                  let expected = [ "size"; "owner"; "building"; "effect"; "module" ] |> Seq.sort
                  Expect.sequenceEqual suggestions expected "Completion should match"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test root completion"
          <| fun () ->
              let input =
                  "\n\
                            #test\n\
                            \n\
                            create_starbase = {\n\
                            owner = this \n\
                            }\n"

              let pos = mkPos 1 0
              let split = input.Split('\n')

              let filetext =
                  split
                  |> Array.mapi (fun i s ->
                      if i = (pos.Line - 1) then
                          log $"%s{s}"
                          let s = s.Insert(pos.Column, magicCharString) in
                          log $"%s{s}"
                          s
                      else
                          s)
                  |> String.concat "\n"

              match CKParser.parseString filetext "test.txt" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let comp =
                      CompletionService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          [],
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          [],
                          STL STLLang.Default,
                          emptyDataTypesLazy.Value,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let suggestions =
                      comp.Complete(pos, entity, None, None)
                      |> Seq.map (function
                          | Simple(c, _, _) -> c
                          | Snippet(l, _, _, _, _) -> l
                          | Detailed _ -> failwith "todo")
                      |> Seq.sort

                  let expected = [ "create_starbase"; "create_starbase" ] |> Seq.sort
                  Expect.sequenceEqual suggestions expected "Completion should match"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test scalar completion type hint"
          <| fun () ->
              let input =
                  "fire_on_action = {\n\
                            on_action = o\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let onAction =
                      NewRule(
                          LeafRule(specificField "on_action", ScalarField ScalarValue),
                          { requiredSingle with
                              completionType = Some "on_action" }
                      )

                  let fireOnAction =
                      NewRule(NodeRule(specificField "fire_on_action", [| onAction |]), optionalMany)

                  let typeinfo =
                      [ "on_action", createStringSet [ "on_game_start"; "custom_on_action" ] ]
                      |> Map.ofList

                  let comp =
                      CompletionService(
                          RulesWrapper [| TypeRule("fire_on_action", fireOnAction) |],
                          [ { createStarbaseTypeDefLazy.Value with name = "fire_on_action" } ],
                          typeinfo.ToFrozenDictionary(),
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          [],
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          [],
                          STL STLLang.Default,
                          emptyDataTypesLazy.Value,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let pos = mkPos 2 13

                  let suggestions =
                      comp.Complete(pos, entity, None, None)
                      |> Seq.map (function
                          | Simple(c, _, _) -> c
                          | Snippet(l, _, _, _, _) -> l
                          | Detailed _ -> failwith "todo")
                      |> Seq.sort

                  let expected = [ "custom_on_action"; "on_game_start" ] |> Seq.sort
                  Expect.sequenceEqual suggestions expected "Completion should match"
              | Failure(e, _, _) -> Expect.isTrue false e

          testWithCapturedLogs "test on_action root subtype completion"
          <| fun () ->
              let configtext =
                  [ "./testfiles/configtests/config/on_actions.cwt",
                    "types = {\n\
                          ## root_completion = subtypes\n\
                          type[on_action] = {\n\
                              path = \"game/common/on_actions\"\n\
                              ## type_key_filter = on_game_start\n\
                              subtype[on_game_start] = { }\n\
                              ## type_key_filter = on_monthly_pulse\n\
                              subtype[on_monthly_pulse] = { }\n\
                          }\n\
                      }" ]

              let folder = "./testfiles/configtests/completiontests"
              let settings = emptyStellarisSettings folder

              let settings =
                  { settings with
                      embedded = FromConfig([], [])
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let input = "on"
              let pos = mkPos 1 2

              let suggestions =
                  stl.Complete pos "common/on_actions/test.txt" input
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.toList

              Expect.contains suggestions "on_game_start" "Completion should include vanilla on_action key"
              Expect.contains suggestions "on_monthly_pulse" "Completion should include vanilla on_action key"
              Expect.isFalse (suggestions |> List.contains "on_action") "Subtype-only root completion should not suggest the type name"

          testWithCapturedLogs "test test ship_behavior"
          <| fun () ->
              let input =
                  "ship_size = {\n\
                            default_behavior = s \n\
                            }"

              let behaviours =
                  "ship_behavior = {\n\
                              name = \"default\"\n\
                              }\n\
                              ship_behavior = {\n\
                              name = \"swarm\"\n\
                              }"

              match
                  CKParser.parseString input "common/ship_sizes/test.txt",
                  CKParser.parseString behaviours "common/ship_behaviors/test.txt"
              with
              | Success(r, _, _), Success(b, _, _) ->
                  let bnode =
                      (STLProcess.shipProcess.ProcessNode () "root" (mkZeroFile "common/ship_behaviors/test.txt") b)

                  let be =
                      { entity = bnode
                        rawEntity = bnode
                        filepath = "/test/stellaris/common/ship_behaviors/test.txt"
                        logicalpath = "common/ship_behaviors/test.txt"
                        validate = false
                        entityType = EntityType.ShipBehaviors
                        overwrite = Overwrite.No }

                  let ruleapplicator =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value) |],
                          [],
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

                  let typeinfo =
                      RulesHelpers.getTypesFromDefinitions
                          (Some ruleapplicator)
                          [ shipBehaviorTypeLazy.Value; shipSizeTypeLazy.Value ]
                          [| be |]
                      |> Map.toSeq
                      |> Seq.map (fun (k, s) -> k, createStringSet (s |> Array.map _.id))
                      |> Map.ofSeq
                  // eprintfn "%A" typeinfo
                  let node =
                      (STLProcess.shipProcess.ProcessNode () "root" (mkZeroFile "common/ship_sizes/test.txt") r)

                  let entity =
                      { filepath = "common/ship_sizes/test.txt"
                        logicalpath = "common/ship_sizes/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let pos = mkPos 2 20

                  let comp =
                      CompletionService(
                          RulesWrapper [| TypeRule("ship_size", shipsizeLazy.Value) |],
                          [ shipBehaviorTypeLazy.Value; shipSizeTypeLazy.Value ],
                          typeinfo.ToFrozenDictionary(),
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          [],
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          [],
                          STL STLLang.Default,
                          emptyDataTypesLazy.Value,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )

                  let res = comp.Complete(pos, entity, None, None)
                  // eprintfn "res4 %A" res
                  let suggestions =
                      res
                      |> Seq.map (function
                          | Simple(c, _, _) -> c
                          | Snippet(l, _, _, _, _) -> l
                          | Detailed _ -> failwith "todo")
                      |> Seq.sort

                  let expected = [ "default"; "swarm" ] |> Seq.sort
                  Expect.sequenceEqual suggestions expected "Completion should match"

              | ParserResult.Success _, ParserResult.Failure _ -> failwith "todo"
              | ParserResult.Failure _, ParserResult.Success _ -> failwith "todo"
              | ParserResult.Failure _, ParserResult.Failure _ -> failwith "todo"

          ptestCase "test scope at pos simple nodes"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                         effect = {\n\
                         every_owned_planet = { \n\
                         }\n\
                         }\n\
                         }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let rules =
                      RuleValidationService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value); eopEffectLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
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

                  let infoService =
                      InfoService(
                          RulesWrapper [| TypeRule("create_starbase", createStarbaseLazy.Value); eopEffectLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          rules,
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )
                  // let comp = CompletionService([TypeRule ("create_starbase", RulesParser.createStarbaseLazy.Value)], [RulesParser.createStarbaseTypeDefLazy.Value], Map.empty, Map.empty, [], Set.empty, [], [])
                  let pos = mkPos 3 23
                  let suggestions = infoService.GetInfo(pos, entity)

                  match suggestions with
                  | None -> Expect.isTrue false "info failed"
                  | Some(context, _) ->
                      let scopes = context.Scopes

                      let expected =
                          [ (scopeManager.ParseScope () "Planet")
                            (scopeManager.ParseScope () "Country") ]

                      Expect.sequenceEqual scopes expected "Scopes should match"
              | Failure(e, _, _) -> Expect.isTrue false e
          ptestCase "test scope at pos prev"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                         effect = {\n\
                         every_owned_planet = {\n\
                         prev = { \n\
                         }\n\
                         }\n\
                         }\n\
                         }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let rules =
                      RuleValidationService(
                          RulesWrapper
                              [| TypeRule("create_starbase", createStarbaseLazy.Value)
                                 eopEffectLazy.Value
                                 leftScopeLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
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

                  let infoService =
                      InfoService(
                          RulesWrapper
                              [| TypeRule("create_starbase", createStarbaseLazy.Value)
                                 eopEffectLazy.Value
                                 leftScopeLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          rules,
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )
                  // let comp = CompletionService([TypeRule ("create_starbase", RulesParser.createStarbaseLazy.Value)], [RulesParser.createStarbaseTypeDefLazy.Value], Map.empty, Map.empty, [], Set.empty, [], [])
                  let pos = mkPos 4 9
                  let suggestions = infoService.GetInfo(pos, entity)

                  match suggestions with
                  | None -> Expect.isTrue false "info failed"
                  | Some(context, _) ->
                      let scopes = context.Scopes

                      let expected =
                          [ (scopeManager.ParseScope () "Country")
                            (scopeManager.ParseScope () "Planet")
                            (scopeManager.ParseScope () "Country") ]

                      Expect.sequenceEqual scopes expected "Scopes should match"
              | Failure(e, _, _) -> Expect.isTrue false e
          ptestCase "test scope at pos leaf"
          <| fun () ->
              let input =
                  "create_starbase = {\n\
                         effect = {\n\
                         every_owned_planet = {\n\
                         log = yes \n\
                         }\n\
                         }\n\
                         }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))
                  let node = (STLProcess.shipProcess.ProcessNode () "root" range.Zero r)

                  let entity =
                      { filepath = "events/test.txt"
                        logicalpath = "events/test.txt"
                        rawEntity = node
                        entity = node
                        validate = true
                        entityType = EntityType.Events
                        overwrite = Overwrite.No }

                  let rules =
                      RuleValidationService(
                          RulesWrapper
                              [| TypeRule("create_starbase", createStarbaseLazy.Value)
                                 eopEffectLazy.Value
                                 leftScopeLazy.Value
                                 logEffectLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
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

                  let infoService =
                      InfoService(
                          RulesWrapper
                              [| TypeRule("create_starbase", createStarbaseLazy.Value)
                                 eopEffectLazy.Value
                                 leftScopeLazy.Value
                                 logEffectLazy.Value |],
                          [ createStarbaseTypeDefLazy.Value ],
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          FrozenDictionary.Empty,
                          [||],
                          FrozenSet.Empty,
                          effectMap,
                          effectMap,
                          rules,
                          changeScope,
                          defaultContext,
                          (scopeManager.ParseScope () "Any"),
                          STL STLLang.Default,
                          processLocalisationLazy.Value,
                          validateLocalisationLazy.Value
                      )
                  // let comp = CompletionService([TypeRule ("create_starbase", RulesParser.createStarbaseLazy.Value)], [RulesParser.createStarbaseTypeDefLazy.Value], Map.empty, Map.empty, [], Set.empty, [], [])
                  let pos = mkPos 4 2
                  let suggestions = infoService.GetInfo(pos, entity)

                  match suggestions with
                  | None -> Expect.isTrue false "info failed"
                  | Some(context, _) ->
                      let scopes = context.Scopes

                      let expected =
                          [ (scopeManager.ParseScope () "Planet")
                            (scopeManager.ParseScope () "Country") ]

                      Expect.sequenceEqual scopes expected "Scopes should match"

                  let pos = mkPos 4 8
                  let suggestions = infoService.GetInfo(pos, entity)

                  match suggestions with
                  | None -> Expect.isTrue false "info failed"
                  | Some(context, _) ->
                      let scopes = context.Scopes

                      let expected =
                          [ (scopeManager.ParseScope () "Planet")
                            (scopeManager.ParseScope () "Country") ]

                      Expect.sequenceEqual scopes expected "Scopes should match"

              | Failure(e, _, _) -> Expect.isTrue false e

          ]


[<Tests>]
let testsConfig =
    testList
        "full config"
        [ testWithCapturedLogs "basic"
          <| fun () ->
              let configtext =
                  [ "./testfiles/configtests/config/test.cwt",
                    File.ReadAllText "./testfiles/configtests/config/test.cwt" ]

              let configtext =
                  ("./testfiles/validationtests/trigger_docs.log",
                   File.ReadAllText "./testfiles/validationtests/trigger_docs.log")
                  :: configtext

              let configtext =
                  ("./testfiles/validationtests/setup.log", File.ReadAllText "./testfiles/validationtests/setup.log")
                  :: configtext

              let folder = "./testfiles/configtests/completiontests"
              // let triggers, effects = parseDocsFile "./testfiles/validationtests/trigger_docs_2.0.4.txt" |> (function |Success(p, _, _) -> DocsParser.processDocs (scopeManager.ParseScopes) p)
              // let modifiers = SetupLogParser.parseLogsFile "./testfiles/validationtests/setup.log" |> (function |Success(p, _, _) -> SetupLogParser.processLogs p)
              let settings = emptyStellarisSettings folder

              let settings =
                  { settings with
                      embedded = FromConfig([], [])
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              //let stl = STLGame(folder, Files(scopeManager.ParseScope() "All"), "", triggers, effects, modifiers, [], [configtext], [STL STLLang.English], false, true, true)

              let input =
                  "ship_size = {\n\
                            default_behavior =  \n\
                            }"

              let pos = mkPos 2 20
              // let suggestions = stl.Complete pos "common/ship_sizes/test.txt" input
              let suggestions = stl.Complete pos "common/ship_sizes/test.txt" input
              //eprintfn "%A" suggestions
              let suggestions =
                  suggestions
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.sort

              let expected = [ "default"; "swarm" ] |> Seq.sort
              Expect.sequenceEqual suggestions expected "Completion should match"

          testWithCapturedLogs "basic with config load"
          <| fun () ->
              let configtext =
                  [ "./testfiles/configtests/config/test.cwt",
                    File.ReadAllText "./testfiles/configtests/config/test.cwt" ]

              let configtext =
                  ("./testfiles/validationtests/trigger_docs.log",
                   File.ReadAllText "./testfiles/validationtests/trigger_docs.log")
                  :: configtext

              let configtext =
                  ("./testfiles/validationtests/setup.log", File.ReadAllText "./testfiles/validationtests/setup.log")
                  :: configtext

              let folder = "./testfiles/configtests/completiontests"
              // let triggers, effects = parseDocsFile "./testfiles/validationtests/trigger_docs_2.0.4.txt" |> (function |Success(p, _, _) -> DocsParser.processDocs (scopeManager.ParseScopes) p)
              // let modifiers = SetupLogParser.parseLogsFile "./testfiles/validationtests/setup.log" |> (function |Success(p, _, _) -> SetupLogParser.processLogs p)
              let settings = emptyStellarisSettings folder

              let settings =
                  { settings with
                      embedded = FromConfig([], [])
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>

              let input =
                  "ship_size = {\n\
                            default_behavior = s \n\
                            }"

              let pos = mkPos 2 20
              let pos2 = mkPos 2 5

              let _ =
                  stl.Complete pos2 "common/ship_sizes/test.txt" input
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.sort

              let suggestions =
                  stl.Complete pos "common/ship_sizes/test.txt" input
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.sort

              let expected = [ "default"; "swarm" ] |> Seq.sort
              Expect.sequenceEqual suggestions expected "Completion should match"

          testWithCapturedLogs "shipsize prerequisits"
          <| fun () ->
              let configtext =
                  [ "./testfiles/configtests/config/test.cwt",
                    File.ReadAllText "./testfiles/configtests/config/test.cwt" ]

              let configtext =
                  ("./testfiles/validationtests/trigger_docs.log",
                   File.ReadAllText "./testfiles/validationtests/trigger_docs.log")
                  :: configtext

              let configtext =
                  ("./testfiles/validationtests/setup.log", File.ReadAllText "./testfiles/validationtests/setup.log")
                  :: configtext

              let folder = "./testfiles/configtests/completiontests"
              // let triggers, effects = parseDocsFile "./testfiles/validationtests/trigger_docs_2.0.4.txt" |> (function |Success(p, _, _) -> DocsParser.processDocs (scopeManager.ParseScopes) p)
              // let modifiers = SetupLogParser.parseLogsFile "./testfiles/validationtests/setup.log" |> (function |Success(p, _, _) -> SetupLogParser.processLogs p)
              let settings = emptyStellarisSettings folder

              let settings =
                  { settings with
                      embedded = FromConfig([], [])
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>

              let input =
                  "ship_size = {\n\
                            prerequisites = {\n\
                            \n\
                            }\n\
                            }"

              let pos = mkPos 3 0

              let suggestions =
                  stl.Complete pos "common/ship_sizes/test.txt" input
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.sort

              let expected = [ "tech_one"; "tech_two" ] |> Seq.sort
              Expect.sequenceEqual suggestions expected "Completion should match"

          testWithCapturedLogs "shipsize enum"
          <| fun () ->
              let configtext =
                  [ "./testfiles/configtests/config/test.cwt",
                    File.ReadAllText "./testfiles/configtests/config/test.cwt" ]

              let configtext =
                  ("./testfiles/validationtests/trigger_docs.log",
                   File.ReadAllText "./testfiles/validationtests/trigger_docs.log")
                  :: configtext

              let configtext =
                  ("./testfiles/validationtests/setup.log", File.ReadAllText "./testfiles/validationtests/setup.log")
                  :: configtext

              let folder = "./testfiles/configtests/completiontests"
              // let triggers, effects = parseDocsFile "./testfiles/validationtests/trigger_docs_2.0.4.txt" |> (function |Success(p, _, _) -> DocsParser.processDocs (scopeManager.ParseScopes) p)
              // let modifiers = SetupLogParser.parseLogsFile "./testfiles/validationtests/setup.log" |> (function |Success(p, _, _) -> SetupLogParser.processLogs p)
              let settings = emptyStellarisSettings folder

              let settings =
                  { settings with
                      embedded = FromConfig([], [])
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>

              let input =
                  "ship_size = {\n\
                            class = \n\
                            }"

              let pos = mkPos 2 8

              let suggestions =
                  stl.Complete pos "common/ship_sizes/test.txt" input
                  |> Seq.map (function
                      | Simple(c, _, _) -> c
                      | Snippet(l, _, _, _, _) -> l
                      | Detailed _ -> failwith "todo")
                  |> Seq.sort

              let expected =
                  [ "shipclass_military"
                    "shipclass_transport"
                    "shipclass_military_station"
                    "shipclass_starbase" ]
                  |> Seq.sort

              Expect.sequenceEqual suggestions expected "Completion should match" ]
//
// [<Tests>]
// let miscTests =
//     testList "miscTests" [
//         ftestWithCapturedLogs "concurrentParse" <| fun () ->
//             let filepath = "./testfiles/configtests/config/test.cwt"
//             let filetext = File.ReadAllText filepath
//             let inner i =
//                 printfn "%A" i
//                 match CKParser.parseString filetext filepath with
//                 | Success (statements, _, _) ->
//                     simpleProcess.ProcessNode() filepath (mkZeroFile filepath) statements |> ignore
//                 | _ -> ()
//             Array.create 10000 0 |> Array.Parallel.iteri (fun i _ -> inner i)
//
//     ]

[<Tests>]
let dynamicParameterScanTests =
    testList
        "dynamic parameter scanning"
        [ testCase "scripted_effect $PARAM$ extraction"
          <| fun () ->
              let input =
                  "test_effect = {\n\
                            set_variable = { which = $AMOUNT$ value = 5 }\n\
                            add_resource = { energy = $ENERGY|10$ }\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                  let ps = Compute.EU4.getScriptedEffectParams node
                  Expect.contains ps "AMOUNT" $"should extract AMOUNT, got %A{ps}"
                  Expect.contains ps "ENERGY" $"should strip default from $ENERGY|10$, got %A{ps}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testCase "script_value $PARAM$ extraction"
          <| fun () ->
              let input =
                  "test_value = {\n\
                            value = $BASE$\n\
                            multiply = $FACTOR|2$\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                  let ps = Compute.EU4.getScriptValueParams node
                  Expect.contains ps "BASE" $"should extract BASE, got %A{ps}"
                  Expect.contains ps "FACTOR" $"should strip default from $FACTOR|2$, got %A{ps}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testCase "scripted_effect [[PARAM]content] extraction at start"
          <| fun () ->
              let input =
                  "test_effect = {\n\
                            [[ag_failed]\n\
                                set_variable = { which = result value = -1 }\n\
                            ]\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                  let ps = Compute.EU4.getScriptedEffectParams node
                  Expect.contains ps "ag_failed" $"should extract ag_failed from [[ag_failed], got %A{ps}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testCase "scripted_effect [[PARAM]content] extraction embedded in string"
          <| fun () ->
              let input =
                  "test_effect = {\n\
                            set_variable = { which = result[[ag_failed]_failed] value = 1 }\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                  let ps = Compute.EU4.getScriptedEffectParams node
                  Expect.contains ps "ag_failed" $"should extract ag_failed from embedded [[ag_failed]_failed], got %A{ps}"
              | Failure(e, _, _) -> Expect.isTrue false e
          testCase "scripted_effect [[!PARAM]content] negated extraction"
          <| fun () ->
              let input =
                  "test_effect = {\n\
                            [[!no_effect]\n\
                                do_something = yes\n\
                            ]\n\
                            }"

              match CKParser.parseString input "test.txt" with
              | Success(r, _, _) ->
                  let node = STLProcess.shipProcess.ProcessNode () "root" range.Zero r
                  let ps = Compute.EU4.getScriptedEffectParams node
                  Expect.contains ps "no_effect" $"should extract no_effect from [[!no_effect], got %A{ps}"
              | Failure(e, _, _) -> Expect.isTrue false e ]

[<Tests>]
let nestedEventTargetTests =
    let mkScriptedEffect (node: Node) =
        ScriptedEffect(
            node.KeyId,
            [],
            EffectType.Effect,
            "",
            STLProcess.findAllSavedGlobalEventTargets node |> Set.toList,
            STLProcess.findAllSavedEventTargets node |> Set.toList,
            STLProcess.findAllUsedEventTargets node |> Set.toList,
            STLProcess.findAllFiredOnActions node |> Set.toList
        )

    let parseRoot (input: string) =
        match CKParser.parseString input "test.txt" with
        | Success(r, _, _) -> STLProcess.shipProcess.ProcessNode () "root" range.Zero r
        | Failure(e, _, _) -> failtest e

    let buildEffects (input: string) =
        let root = parseRoot input
        let rawEffects = root.Children |> List.map (fun n -> n, ([]: string list))
        let effects = root.Children |> List.map (mkScriptedEffect >> fun e -> e :> Effect)
        STLProcess.addNestedEventTargetsToEffects rawEffects effects

    let savedTargetsOf (name: string) (effects: Effect list) =
        effects
        |> List.pick (function
            | :? ScriptedEffect as se when se.Name.GetString() == name -> Some se.SavedEventTargets
            | _ -> None)

    let globalTargetsOf (name: string) (effects: Effect list) =
        effects
        |> List.pick (function
            | :? ScriptedEffect as se when se.Name.GetString() == name -> Some se.GlobalEventTargets
            | _ -> None)

    let usedTargetsOf (name: string) (effects: Effect list) =
        effects
        |> List.pick (function
            | :? ScriptedEffect as se when se.Name.GetString() == name -> Some se.UsedEventTargets
            | _ -> None)

    testList
        "nested scripted effect event targets"
        [ testCase "event target existence suffix is not part of the saved target key"
          <| fun () ->
              let input =
                  "test_effect = {\n\
                            event_target:wg_dragon_own_country? = { set_country_flag = checked }\n\
                            exists = event_target:wg_dragon_own_country?\n\
                            is_same_value = event_target:other_target?\n\
                            }"

              let node = parseRoot input
              let used = STLProcess.findAllUsedEventTargets node
              let exists = STLProcess.findAllExistsEventTargets node

              Expect.contains
                  used
                  "wg_dragon_own_country"
                  $"used event target should drop existence suffix, got %A{used}"

              Expect.contains used "other_target" $"value event target should drop existence suffix, got %A{used}"
              Expect.contains exists "wg_dragon_own_country" $"exists target should drop existence suffix, got %A{exists}"
              Expect.isFalse
                  (Set.contains "wg_dragon_own_country?" used)
                  $"used event target should not include '?' in the key, got %A{used}"

              Expect.isFalse
                  (Set.contains "wg_dragon_own_country?" exists)
                  $"exists event target should not include '?' in the key, got %A{exists}"

          testCase "global save under owner existence guard is collected"
          <| fun () ->
              let input =
                  "fleet_event = {\n\
                            id = ai_action.6\n\
                            immediate = {\n\
                            owner? = { save_global_event_target_as = kuat_friendly_faction }\n\
                            }\n\
                            }"

              let node = parseRoot input
              let globals = STLProcess.findAllSavedGlobalEventTargets node

              Expect.contains
                  globals
                  "kuat_friendly_faction"
                  $"owner? global save should be collected, got %A{globals}"
          testCase "global saved event target satisfies guarded event-chain usage"
          <| fun () ->
              let input =
                  "event = {\n\
                            id = ai_action.14\n\
                            trigger = {\n\
                            exists = event_target:kuat_friendly_faction\n\
                            any_galaxy_fleet = {\n\
                            controller? = { is_at_war_with = event_target:kuat_friendly_faction }\n\
                            }\n\
                            }\n\
                            immediate = {\n\
                            event_target:kuat_friendly_faction = { clear_orders = yes }\n\
                            }\n\
                            }\n\
                            fleet_event = {\n\
                            id = ai_action.6\n\
                            immediate = {\n\
                            owner? = { save_global_event_target_as = kuat_friendly_faction }\n\
                            set_automatic_fleet_avaliable = { FRIENDLY_TARGET = event_target:kuat_friendly_faction }\n\
                            }\n\
                            }"

              let root = parseRoot input
              let events = root.Children

              let globals =
                  events
                  |> List.map STLProcess.findAllSavedGlobalEventTargets
                  |> List.fold Set.union Set.empty

              let result =
                  CWTools.Validation.Stellaris.STLEventValidation.checkEventChain [] [] [] globals events

              Expect.equal result OK $"global target should suppress CW220/CW221, got %A{result}"
          testCase "legacy optional scopes work in dotted event target chains"
          <| fun () ->
              UtilityParser.initializeScopes None (Some(defaultScopeInputs ()))

              let parseScope name = scopeManager.ParseScope () name
              let country = parseScope "Country"
              let planet = parseScope "Planet"
              let galacticObject = parseScope "GalacticObject"
              let star = parseScope "Star"
              let ship = parseScope "Ship"

              let mkLink (name: string) (inputs: Scope list) (target: Scope) =
                  ScopedEffect(name, inputs, target, EffectType.Link, "", "", false) :> Effect

              let links =
                  EffectMap.FromList
                      [ mkLink "owner" [ planet; galacticObject; star; ship ] country
                        mkLink "solar_system" [ planet; star ] galacticObject
                        mkLink "star" [ galacticObject ] star
                        mkLink "event_target:surveyed_planet" scopeManager.AllScopes planet ]

              let resolve root current (key: string) =
                  let context =
                      { Root = root
                        From = []
                        FromDepth = 0
                        Scopes = [ current ] }

                  match
                      changeScope.Invoke(
                          false,
                          true,
                          links,
                          EffectMap(),
                          [],
                          createStringSet [],
                          System.ReadOnlySpan<char>(key.ToCharArray()),
                          context
                      )
                  with
                  | NewScope(context, _, _) -> context.CurrentScope
                  | other -> failtestf "%s should resolve as a legacy scope chain, got %A" key other

              Expect.equal (resolve country planet "owner?") country "owner? should behave like owner"
              Expect.equal (resolve planet ship "root.owner?") country "root.owner? should strip the optional marker"
              Expect.equal
                  (resolve country planet "event_target:target_system.star.owner?")
                  country
                  "event target scope chains should allow optional legacy links"
              Expect.equal
                  (resolve country ship "event_target:surveyed_planet")
                  planet
                  "a known saved event target should resolve to its exact scope"
              Expect.equal
                  (resolve country ship "event_target:surveyed_planet.owner")
                  country
                  "links after a known saved event target should use its exact scope"
              Expect.equal
                  (resolve country ship "event_target:unknown_target")
                  scopeManager.AnyScope
                  "an unknown event target should keep the conservative Any fallback"

              let lookup = Lookup()

              lookup.savedEventTargets <-
                  ResizeArray(
                      [ "unique_planet", range.Zero, planet
                        "unique_planet", range.Zero, planet
                        "ambiguous_target", range.Zero, planet
                        "ambiguous_target", range.Zero, country
                        "partially_known_target", range.Zero, ship
                        "partially_known_target", range.Zero, scopeManager.AnyScope ]
                  )

              let savedLinks = STLGameFunctions.savedEventTargetLinks lookup
              Expect.equal
                  savedLinks.Length
                  1
                  "only targets whose every save has one known project-wide scope should get an exact link"
              Expect.equal (savedLinks[0].Name.GetString()) "event_target:unique_planet" "the exact link should use event_target syntax"

              match savedLinks[0] with
              | :? ScopedEffect as link -> Expect.equal link.Target (Some planet) "the exact link should retain the saved scope"
              | other -> failtestf "saved event target link should be scoped, got %A" other
          testWithCapturedLogs "an unresolved FROM save prevents an exact saved event target scope"
          <| fun () ->
              let root =
                  Path.Combine(Path.GetTempPath(), "cwtools-ambiguous-event-target-" + System.Guid.NewGuid().ToString("N"))

              let eventsDir = Path.Combine(root, "events")
              Directory.CreateDirectory(eventsDir) |> ignore
              let eventFile = Path.Combine(eventsDir, "ambiguous_event_target_events.txt")
              let eventText =
                  "namespace = ambiguous_target\n\
                   country_event = {\n\
                       id = ambiguous_target.1\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       immediate = {\n\
                           from = {\n\
                               save_event_target_as = current_marauder_diplomacy\n\
                           }\n\
                       }\n\
                   }\n\
                   country_event = {\n\
                       id = ambiguous_target.2\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       immediate = {\n\
                           owner_species = {\n\
                               save_event_target_as = current_marauder_diplomacy\n\
                           }\n\
                       }\n\
                   }\n\
                   country_event = {\n\
                       id = ambiguous_target.3\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       trigger = {\n\
                           event_target:current_marauder_diplomacy = {\n\
                               has_country_flag = marauder_country_scope_marker\n\
                           }\n\
                       }\n\
                   }"

              File.WriteAllText(eventFile, eventText)

              try
                  let configText = Tests.configFilesFromDir "./testfiles/stellarisconfig/config"

                  let settings =
                      { emptyStellarisSettings root with
                          rules =
                              Some
                                  { ruleFiles = configText
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stlGame = STLGame(settings)
                  let stl = stlGame :> IGame<STLComputedData>
                  let savedScopes =
                      stlGame.Lookup.savedEventTargets
                      |> Seq.choose (fun (name, _, scope) ->
                          if name == "current_marauder_diplomacy" then Some(scope.ToString()) else None)
                      |> Set.ofSeq

                  Expect.contains savedScopes "Any" "the unresolved FROM save should be retained as unknown scope evidence"
                  Expect.contains savedScopes "Species" "the owner_species save should retain its exact Species scope"
                  let marker = "marauder_country_scope_marker"
                  let markerIndex = eventText.IndexOf(marker, System.StringComparison.Ordinal)
                  Expect.isGreaterThan markerIndex -1 "the event-target scope marker should exist"
                  let before = eventText.Substring(0, markerIndex)
                  let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
                  let lastLineBreak = before.LastIndexOf('\n')
                  let column = if lastLineBreak < 0 then markerIndex else markerIndex - lastLineBreak - 1
                  let context = stl.ScopesAtPos (mkPos line column) eventFile eventText

                  Expect.isSome context "the ambiguous event target should have a scope context"
                  Expect.equal
                      (context.Value.CurrentScope.ToString())
                      "Any"
                      "an unresolved save must prevent a different save from fixing the target to Species"

                  let wrongScopeErrors =
                      stl.ValidationErrors()
                      |> List.filter (fun error ->
                          System.String.Equals(
                              Path.GetFullPath(error.range.FileName),
                              Path.GetFullPath(eventFile),
                              System.StringComparison.OrdinalIgnoreCase
                          )
                          && error.message.Contains("has_country_flag", System.StringComparison.OrdinalIgnoreCase)
                          && (error.code = "CW243" || error.code = "CW245"))

                  Expect.isEmpty
                      wrongScopeErrors
                      $"the conservatively unknown target should not report a Species/Country mismatch: %A{wrongScopeErrors}"
              finally
                  if Directory.Exists(root) then Directory.Delete(root, true)
          testCase "event target parameter values normalize after substitution"
          <| fun () ->
              let input =
                  "inner_effect = {\n\
                            event_target:$OWNER$ = { clear_orders = yes }\n\
                            exists = event_target:$OWNER$\n\
                            }\n\
                            outer_effect = {\n\
                            inner_effect = { OWNER = event_target:kuat_friendly_faction }\n\
                            }"

              let used = buildEffects input |> usedTargetsOf "outer_effect"

              Expect.contains
                  used
                  "kuat_friendly_faction"
                  $"scope-valued parameter should normalize to the saved target key, got %A{used}"

              Expect.isFalse
                  (List.contains "event_target:kuat_friendly_faction" used)
                  $"scope-valued parameter should not keep a nested event_target prefix, got %A{used}"
          testWithCapturedLogs "STL game validation accepts global target saved in legacy optional scope"
          <| fun () ->
              let root =
                  Path.Combine(Path.GetTempPath(), "cwtools-event-target-" + System.Guid.NewGuid().ToString("N"))

              let eventsDir = Path.Combine(root, "events")
              let scriptedEffectsDir = Path.Combine(root, "common", "scripted_effects")
              Directory.CreateDirectory(eventsDir) |> ignore
              Directory.CreateDirectory(scriptedEffectsDir) |> ignore
              let eventFile = Path.Combine(eventsDir, "kuat_action_event.txt")
              let effectFile = Path.Combine(scriptedEffectsDir, "kuat_effects.txt")
              let eventText =
                  "event = {\n\
                            id = ai_action.14\n\
                            hide_window = yes\n\
                            is_triggered_only = yes\n\
                            trigger = {\n\
                            exists = event_target:kuat_friendly_faction\n\
                            any_galaxy_fleet = {\n\
                            exists = controller\n\
                            controller? = { is_at_war_with = event_target:kuat_friendly_faction }\n\
                            }\n\
                            }\n\
                            immediate = {\n\
                            event_target:kuat_friendly_faction = { clear_orders = yes }\n\
                            kuat_exe_auto_fleet_action = { OWNER = event_target:kuat_friendly_faction }\n\
                            }\n\
                            }\n\
                            fleet_event = {\n\
                            id = ai_action.6\n\
                            hide_window = yes\n\
                            is_triggered_only = yes\n\
                            immediate = {\n\
                            owner? = { save_global_event_target_as = kuat_friendly_faction }\n\
                            set_automatic_fleet_avaliable = { FRIENDLY_TARGET = event_target:kuat_friendly_faction }\n\
                            }\n\
                            }"
              let effectText =
                  "kuat_exe_auto_fleet_action = {\n\
                            event_target:$OWNER$ = { clear_orders = yes }\n\
                            exists = event_target:$OWNER$\n\
                            }"

              File.WriteAllText(eventFile, eventText)
              File.WriteAllText(effectFile, effectText)

              try
                  let configText = Tests.configFilesFromDir "./testfiles/stellarisconfig/config"

                  let settings =
                      { emptyStellarisSettings root with
                          rules =
                              Some
                                  { ruleFiles = configText
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>
                  let eventTargetErrors phase errors =
                      errors
                      |> List.filter (fun e ->
                          (e.code = "CW220" || e.code = "CW221")
                          && e.message.Contains("kuat_friendly_faction"))
                      |> fun matches ->
                          Expect.isEmpty matches $"{phase} should not report kuat_friendly_faction as unsaved: %A{matches}"

                  stl.ValidationErrors() |> eventTargetErrors "full validation"
                  stl.UpdateFile false eventFile (Some eventText) |> eventTargetErrors "UpdateFile validation"
              finally
                  if Directory.Exists(root) then Directory.Delete(root, true)
          testCase "save via nested parameterised call propagates to caller"
          <| fun () ->
              // Mirrors vanilla cosmic storms: try_spawn calls choose_location
              // with EVENT_TARGET_NAME, which does save_event_target_as = $EVENT_TARGET_NAME$
              let input =
                  "choose_location = {\n\
                            random_system = {\n\
                            save_event_target_as = $EVENT_TARGET_NAME$\n\
                            }\n\
                            }\n\
                            try_spawn = {\n\
                            choose_location = {\n\
                            EVENT_TARGET_NAME = new_storm_location\n\
                            }\n\
                            spawn_thing = {\n\
                            position = event_target:new_storm_location\n\
                            }\n\
                            }"

              let saved = buildEffects input |> savedTargetsOf "try_spawn"

              Expect.contains
                  saved
                  "new_storm_location"
                  $"caller should be credited with the nested parameterised save, got %A{saved}"
          testCase "parameter chains resolve across two levels of nesting"
          <| fun () ->
              let input =
                  "saver = {\n\
                            save_event_target_as = $TARGET$\n\
                            }\n\
                            wrapper = {\n\
                            saver = {\n\
                            TARGET = $NAME$\n\
                            }\n\
                            }\n\
                            caller = {\n\
                            wrapper = {\n\
                            NAME = my_target\n\
                            }\n\
                            }"

              let effects = buildEffects input
              let wrapperSaved = effects |> savedTargetsOf "wrapper"
              let callerSaved = effects |> savedTargetsOf "caller"

              Expect.contains
                  wrapperSaved
                  "$NAME$"
                  $"wrapper should keep the unresolved placeholder, got %A{wrapperSaved}"

              Expect.contains
                  callerSaved
                  "my_target"
                  $"caller should resolve the full parameter chain, got %A{callerSaved}"
          testWithCapturedLogs "parameterized and wrapped event target saves preserve scope"
          <| fun () ->
              let root =
                  Path.Combine(Path.GetTempPath(), "cwtools-event-target-scope-" + System.Guid.NewGuid().ToString("N"))

              let eventsDir = Path.Combine(root, "events")
              let scriptedEffectsDir = Path.Combine(root, "common", "scripted_effects")
              Directory.CreateDirectory(eventsDir) |> ignore
              Directory.CreateDirectory(scriptedEffectsDir) |> ignore
              let eventFile = Path.Combine(eventsDir, "event_target_scope_events.txt")
              let effectFile = Path.Combine(scriptedEffectsDir, "event_target_scope_effects.txt")
              let eventText =
                  "namespace = target_scope\n\
                   country_event = {\n\
                       id = target_scope.1\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       immediate = {\n\
                           save_parameterized_target = { TARGET = parameter_country_target }\n\
                           save_parameterized_global_target = { TARGET = parameter_global_country_target }\n\
                           save_wrapped_planet_target = { TARGET = wrapped_planet_target }\n\
                           event_target:parameter_country_target = {\n\
                               set_country_flag = parameter_country_scope_marker\n\
                           }\n\
                           event_target:parameter_global_country_target = {\n\
                               set_country_flag = parameter_global_country_scope_marker\n\
                           }\n\
                           event_target:wrapped_planet_target = {\n\
                               set_planet_flag = wrapped_planet_scope_marker\n\
                           }\n\
                       }\n\
                   }"
              let effectText =
                  "save_parameterized_target = {\n\
                       save_event_target_as = $TARGET$\n\
                   }\n\
                   save_parameterized_global_target = {\n\
                       save_global_event_target_as = $TARGET$\n\
                   }\n\
                   save_wrapped_planet_target = {\n\
                       random_owned_planet = {\n\
                           save_parameterized_target = { TARGET = $TARGET$ }\n\
                       }\n\
                   }"

              File.WriteAllText(eventFile, eventText)
              File.WriteAllText(effectFile, effectText)

              let posOf (needle: string) =
                  let marker = eventText.IndexOf(needle, System.StringComparison.Ordinal)
                  Expect.isGreaterThan marker -1 $"scope marker {needle} was not found"
                  let before = eventText.Substring(0, marker)
                  let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
                  let lastLineBreak = before.LastIndexOf('\n')
                  let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
                  mkPos line column

              try
                  let configText = Tests.configFilesFromDir "./testfiles/stellarisconfig/config"

                  let settings =
                      { emptyStellarisSettings root with
                          rules =
                              Some
                                  { ruleFiles = configText
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>

                  let expectScope expected marker =
                      let context = stl.ScopesAtPos (posOf marker) eventFile eventText
                      Expect.isSome context $"{marker} should have a scope context"
                      Expect.equal
                          (context.Value.CurrentScope.ToString())
                          expected
                          $"{marker} should resolve through the saved event target"

                  expectScope "Country" "parameter_country_scope_marker"
                  expectScope "Country" "parameter_global_country_scope_marker"
                  expectScope "Planet" "wrapped_planet_scope_marker"
              finally
                  if Directory.Exists(root) then Directory.Delete(root, true)
          testWithCapturedLogs "parameterized and nested inline scripts preserve event target scope"
          <| fun () ->
              let root =
                  Path.Combine(Path.GetTempPath(), "cwtools-inline-event-target-scope-" + System.Guid.NewGuid().ToString("N"))

              let eventsDir = Path.Combine(root, "events")
              let inlineScriptsDir = Path.Combine(root, "common", "inline_scripts", "event_target_scope")
              Directory.CreateDirectory(eventsDir) |> ignore
              Directory.CreateDirectory(inlineScriptsDir) |> ignore
              let eventFile = Path.Combine(eventsDir, "inline_event_target_scope_events.txt")
              let directFile = Path.Combine(inlineScriptsDir, "save_target.txt")
              let globalFile = Path.Combine(inlineScriptsDir, "save_global_target.txt")
              let planetFile = Path.Combine(inlineScriptsDir, "save_planet_target.txt")
              let eventText =
                  "namespace = inline_target_scope\n\
                   country_event = {\n\
                       id = inline_target_scope.1\n\
                       hide_window = yes\n\
                       is_triggered_only = yes\n\
                       immediate = {\n\
                           inline_script = {\n\
                               script = event_target_scope/save_target\n\
                               TARGET = inline_country_target\n\
                           }\n\
                           inline_script = {\n\
                               script = event_target_scope/save_global_target\n\
                               TARGET = inline_global_country_target\n\
                           }\n\
                           inline_script = {\n\
                               script = event_target_scope/save_planet_target\n\
                               TARGET = inline_planet_target\n\
                           }\n\
                           event_target:inline_country_target = {\n\
                               set_country_flag = inline_country_scope_marker\n\
                           }\n\
                           event_target:inline_global_country_target = {\n\
                               set_country_flag = inline_global_country_scope_marker\n\
                           }\n\
                           event_target:inline_planet_target = {\n\
                               set_planet_flag = inline_planet_scope_marker\n\
                           }\n\
                       }\n\
                   }"

              File.WriteAllText(eventFile, eventText)
              File.WriteAllText(directFile, "save_event_target_as = $TARGET$")
              File.WriteAllText(globalFile, "save_global_event_target_as = $TARGET$")
              File.WriteAllText(
                  planetFile,
                  "random_owned_planet = {\n\
                       inline_script = {\n\
                           script = event_target_scope/save_target\n\
                           TARGET = $TARGET$\n\
                       }\n\
                   }"
              )

              let posOf (needle: string) =
                  let marker = eventText.IndexOf(needle, System.StringComparison.Ordinal)
                  Expect.isGreaterThan marker -1 $"scope marker {needle} was not found"
                  let before = eventText.Substring(0, marker)
                  let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
                  let lastLineBreak = before.LastIndexOf('\n')
                  let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
                  mkPos line column

              try
                  let configText = Tests.configFilesFromDir "./testfiles/stellarisconfig/config"

                  let settings =
                      { emptyStellarisSettings root with
                          rules =
                              Some
                                  { ruleFiles = configText
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>

                  let expectScope expected marker =
                      let context = stl.ScopesAtPos (posOf marker) eventFile eventText
                      Expect.isSome context $"{marker} should have a scope context"
                      Expect.equal
                          (context.Value.CurrentScope.ToString())
                          expected
                          $"{marker} should resolve through the inline-script event target"

                  expectScope "Country" "inline_country_scope_marker"
                  expectScope "Country" "inline_global_country_scope_marker"
                  expectScope "Planet" "inline_planet_scope_marker"
              finally
                  if Directory.Exists(root) then Directory.Delete(root, true)
          testCase "leaf call without params propagates concrete saves"
          <| fun () ->
              let input =
                  "save_it = {\n\
                            save_event_target_as = concrete_target\n\
                            }\n\
                            outer = {\n\
                            save_it = yes\n\
                            }"

              let saved = buildEffects input |> savedTargetsOf "outer"

              Expect.contains
                  saved
                  "concrete_target"
                  $"leaf-style call should propagate concrete saves, got %A{saved}"
          testCase "global save via nested parameterised call propagates to caller"
          <| fun () ->
              // Mirrors vanilla shroud leaders: hire_effect does
              // save_global_event_target_as = $GLOBAL_EVENT_TARGET$
              let input =
                  "hire_effect = {\n\
                            save_global_event_target_as = $GLOBAL_EVENT_TARGET$\n\
                            }\n\
                            outer_effect = {\n\
                            hire_effect = {\n\
                            GLOBAL_EVENT_TARGET = ganthuata\n\
                            }\n\
                            }"

              let globals = buildEffects input |> globalTargetsOf "outer_effect"

              Expect.contains
                  globals
                  "ganthuata"
                  $"caller should be credited with the nested global save, got %A{globals}"
          testCase "call-site substitution credits parameterised saves in effect blocks"
          <| fun () ->
              let input =
                  "hire_effect = {\n\
                            save_global_event_target_as = $GLOBAL_EVENT_TARGET$\n\
                            }\n\
                            event_block = {\n\
                            hidden_effect = {\n\
                            hire_effect = {\n\
                            GLOBAL_EVENT_TARGET = ganthuata\n\
                            }\n\
                            }\n\
                            }"

              let root = parseRoot input

              let hireEffect =
                  root.Children
                  |> List.find (fun n -> n.Key == "hire_effect")
                  |> mkScriptedEffect

              let effectsByName = Map.ofList [ hireEffect.Name.lower, hireEffect ]

              let eventBlock = root.Children |> List.find (fun n -> n.Key == "event_block")

              let saves =
                  CWTools.Validation.Stellaris.STLEventValidation.findSubstitutedCallSaves effectsByName eventBlock

              Expect.contains
                  saves
                  "ganthuata"
                  $"call-site scan should substitute the global save parameter, got %A{saves}"
          testCase "validate clause with conditional parameter prefix matches actual rule"
          <| fun () ->
              let config =
                  "types = {\n\
                       type[scripted_trigger] = {\n\
                           path = \"game/common/scripted_triggers\"\n\
                       }\n\
                   }\n\
                   alias[trigger:distance] = {\n\
                       source = scope[any]\n\
                       type = scalar\n\
                       use_bypasses = bool\n\
                       min_distance = int\n\
                       max_distance = int\n\
                   }\n\
                   scripted_trigger = {\n\
                       alias_name[trigger] = alias_match_left[trigger]\n\
                   }\n"

              let input =
                  "my_trigger = {\n\
                       [[ag_distance_max]distance = {\n\
                           source = root\n\
                           type = euclidean\n\
                           use_bypasses = yes\n\
                           min_distance = 1\n\
                           max_distance = 5\n\
                       }\n\
                   }\n"

              UtilityParser.initializeScopes None None

              let rules, types, _, _, _ =
                  parseConfig
                      (scopeManager.ParseScope())
                      scopeManager.AllScopes
                      (scopeManager.ParseScope () "Any")
                      scopeManager.ScopeGroups
                      "rules.cwt"
                      config

              match CKParser.parseString input "common/scripted_triggers/test.txt" with
              | Success(r, _, _) ->
                  let node =
                      STLProcess.shipProcess.ProcessNode () "root" range.Zero r

                  let rulesWrapper = RulesWrapper(rules |> List.toArray)

                  let validationService =
                      RuleValidationService(
                          rulesWrapper,
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

                  let errors = validationService.ManualRuleValidate("common/scripted_triggers/test.txt", node)
                  match errors with
                  | OK -> ()
                  | Invalid(_, es) -> failtest $"Expected no errors, but got %A{es}"
              | Failure(err, _, _) -> failwith err ]
