module LocalisationValidationTests

open TestHelpers

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

          testWithCapturedLogs "does not duplicate filepath prefixes or extensions"
          <| fun () ->
              let files =
                  [| "gfx/FX/buttonstate_onlydisable.shader" |]
                      .ToFrozenSet(System.StringComparer.OrdinalIgnoreCase)

              let check value =
                  CSharpHelpers.FieldValidatorsHelper.CheckFilePathField(
                      value,
                      files,
                      Some "gfx/FX/",
                      Some ".shader",
                      true
                  )

              let completePathValid, _ = check "gfx/FX/buttonstate_onlydisable.shader"
              let inferredPathValid, _ = check "buttonstate_onlydisable"
              let differentlyCasedPathValid, _ = check "GFX/fx/BUTTONSTATE_ONLYDISABLE.SHADER"
              let missingPathValid, missingPath = check "gfx/FX/missing.shader"

              Expect.isTrue completePathValid "a complete path must not receive a second prefix or extension"
              Expect.isTrue inferredPathValid "a short path should still receive the configured prefix and extension"
              Expect.isTrue differentlyCasedPathValid "filepath lookup should retain case-insensitive matching"
              Expect.isFalse missingPathValid "a genuinely missing file should still fail"
              Expect.equal missingPath "gfx/FX/missing.shader" "the diagnostic path must not contain .shader.shader"

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
    let validateWithCommands commands command =
        let staticSettings: CWTools.Process.Localisation.LegacyLocStaticSettings =
            { questionMarkVariable = true
              usesVariableCommands = false
              parameterVariables = true
              locPrimaryScopes = [ "From", id ]
              scopedLocEffectsMap = EffectMap()
              commands = commands
              variableCommands = [] }

        CWTools.Process.Localisation.ChangeLocScope.createLegacyLocalisationCommandValidator
            staticSettings
            (dynamicSettings ())
            defaultContext
            command

    let validate = validateWithCommands []

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
              | result -> failtestf "Expected lowercase variable fallback, got %A" result

          testCase "unknown first segment still validates chained commands"
          <| fun () ->
              let commands =
                  [ "GetName", []; "GetIcon", []; "GetNamePlural", [] ]

              match validateWithCommands commands "borg_agri_drone.GetIcon" with
              | CWTools.Process.Localisation.Found _ -> ()
              | result -> failtestf "Expected chained command after unknown first segment to be found, got %A" result

              match validateWithCommands commands "borg_agri_drone.BogusCommand" with
              | CWTools.Process.Localisation.LocNotFound "BogusCommand" -> ()
              | result -> failtestf "Expected unknown chained command to be invalid, got %A" result ]


