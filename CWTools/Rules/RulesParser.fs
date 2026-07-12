namespace CWTools.Rules


open FParsec
open CWTools.Utilities.Position
open CWTools.Utilities
open CWTools.Parser.Types
open CWTools.Common
open CWTools.Common.STLConstants
open CWTools.Process.STLProcess
open CWTools.Process
open CWTools.Utilities.Utils
open System
open System.Globalization
open CWTools.Parser
open CWTools.Rules
open Shared

module private RulesParserImpl =
    let internal specificFieldFromString x =
        SpecificField(SpecificValue(StringResource.stringManager.InternIdentifierToken x))

    let internal specificFieldFromId x = SpecificField(SpecificValue(x))

    let private parseSeverity =
        function
        | "error" -> Severity.Error
        | "warning" -> Severity.Warning
        | "info" -> Severity.Information
        | "information" -> Severity.Information
        | "hint" -> Severity.Hint
        | s -> failwithf $"Invalid severity %s{s}"

    let defaultOptions = Options.DefaultOptions

    let defaultFloat =
        ValueField(
            ValueType.Float(
                RulesParserConstants.floatFieldDefaultMinimum,
                RulesParserConstants.floatFieldDefaultMaximum
            )
        )

    let defaultInt =
        ValueField(
            ValueType.Int(RulesParserConstants.IntFieldDefaultMinimum, RulesParserConstants.IntFieldDefaultMaximum)
        )

    let private getNodeComments (clause: IClause) =
        let findComments (t: range) s (a: Child) =
            match struct (s, a) with
            | struct (struct (b, c), _) when b -> struct (b, c)
            | struct ((_, c), CommentC comment) when comment.Comment.StartsWith('#') ->
                struct (false, comment.Comment :: c)
            | struct ((_, c), CommentC _) -> struct (false, c)
            | struct ((_, c), NodeC n) when n.Position.Code = t.Code -> struct (true, c)
            | struct ((_, c), LeafC v) when v.Position.Code = t.Code -> struct (true, c)
            | struct ((_, c), LeafValueC v) when v.Position.Code = t.Code -> struct (true, c)
            | struct ((_, c), ValueClauseC vc) when vc.Position.Code = t.Code -> struct (true, c)
            | _ -> struct (false, [])

        let one =
            clause.Leaves
            |> Seq.map (fun e ->
                LeafC e,
                clause.AllArray
                |> Array.fold (findComments e.Position) struct (false, [])
                |> structSnd)
            |> List.ofSeq
        //log "%s %A" node.Key (node.All |> List.rev)
        //log "%A" one
        let two =
            clause.Nodes
            |> Seq.map (fun e ->
                NodeC e,
                clause.AllArray
                |> Array.fold (findComments e.Position) (false, [])
                |> structSnd)
            |> List.ofSeq

        let three =
            clause.LeafValues
            |> Seq.toList
            |> List.map (fun e ->
                LeafValueC e, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> structSnd)

        let four =
            clause.ValueClauses
            |> Seq.toList
            |> List.map (fun e ->
                ValueClauseC e, clause.AllArray |> Array.fold (findComments e.Position) (false, []) |> structSnd)

        let new2 = one @ two @ three @ four
        new2

    let internal getSettingFromString (full: string) (key: string) =
        let setting = full.Substring(key.Length)

        if
            not (
                (setting.StartsWith '[' || setting.StartsWith '(')
                && (setting.EndsWith ']' || setting.EndsWith ')')
            )
        then
            None
        else
            Some(setting.Substring(1, setting.Length - 2))

    let private getRangeSettingFromString (full: string) =
        let start = full.IndexOfAny([| '['; '(' |])

        if start < 0 then
            None
        else
            let setting = full.Substring start

            if
                (setting.StartsWith '[' || setting.StartsWith '(')
                && (setting.EndsWith ']' || setting.EndsWith ')')
            then
                Some(setting.Substring(1, setting.Length - 2))
            else
                None

    let private getFloatSettingFromString (full: string) =
        match getRangeSettingFromString full with
        | Some s ->
            let split = s.Split("..", 2, StringSplitOptions.None)

            let parseDecimal (s: string) =
                let s = s.Trim()

                match s, Decimal.TryParse(s, NumberStyles.Float, CultureInfo.InvariantCulture) with
                | "inf", _ -> Some(decimal RulesParserConstants.floatFieldDefaultMaximum)
                | "-inf", _ -> Some(decimal RulesParserConstants.floatFieldDefaultMinimum)
                | _, (true, num) -> Some num
                | _, (false, _) -> None

            if split.Length < 2 then
                None
            else
                match (parseDecimal split.[0]), (parseDecimal split.[1]) with
                | Some min, Some max -> Some(min, max)
                | _ -> None
        | None -> None


    let private getIntSettingFromString (full: string) =
        match getRangeSettingFromString full with
        | Some s ->
            let split = s.Split("..", 2)

            let parseInt (s: string) =
                let s = s.Trim()

                match s, Int64.TryParse(s, NumberStyles.Integer, CultureInfo.InvariantCulture) with
                | "inf", _ -> Some RulesParserConstants.IntFieldDefaultMaximum
                | "-inf", _ -> Some RulesParserConstants.IntFieldDefaultMinimum
                | _, (true, num) -> Some num
                | _, (false, _) -> None

            if split.Length < 2 then
                None
            else
                match (parseInt split.[0]), (parseInt split.[1]) with
                | Some min, Some max -> Some(min, max)
                | _ -> None
        | None -> None

    let private getAliasSettingsFromString (full: string) =
        match getSettingFromString full "alias" with
        | Some s ->
            let split = s.Split(':', 2)

            if split.Length < 2 then None else Some(split[0], split[1])
        | None -> None

    let private getSingleAliasSettingsFromString (full: string) =
        match getSettingFromString full "single_alias" with
        | Some s ->
            let split = s.Split(':', 2)

            if split.Length < 2 then
                None
            else
                Some(split.[0], split.[1])
        | None -> None

    let private getPathOptions (node: Node) =
        let paths = (node.TagsText "path")

        paths
        |> Array.iteri (fun i path -> paths[i] <- path.Replace("game/", "").Replace("game\\", ""))

        let pathStrict = node.TagText "path_strict" == "yes"

        let pathFile =
            if node.Has "path_file" then
                Some(node.TagText "path_file")
            else
                None

        let pathExtension =
            if node.Has "path_extension" then
                Some(node.TagText "path_extension")
            else
                None

        { paths = paths
          pathStrict = pathStrict
          pathFile = pathFile
          pathExtension = pathExtension }

    let inline private replaceScopes parseScope (comments: string list) =
        match comments |> List.tryFind (fun s -> s.Contains("replace_scope")) with
        | Some s ->
            let s = s.Trim('#')
            let parsed = CKParser.parseString s "config"

            match parsed with
            | Failure _ -> None
            | Success(s, _, _) ->
                let n =
                    (STLProcess.shipProcess.ProcessNode EntityType.Other "root" (mkZeroFile "config") s)

                match n.Child "replace_scope" with
                | Some c ->
                    let this =
                        if c.Has "this" then
                            c.TagText "this" |> parseScope |> Some
                        else
                            None

                    let root =
                        if c.Has "root" then
                            c.TagText "root" |> parseScope |> Some
                        else
                            None

                    let from =
                        if c.Has "from" then
                            c.TagText "from" |> parseScope |> Some
                        else
                            None

                    let fromfrom =
                        if c.Has "fromfrom" then
                            c.TagText "fromfrom" |> parseScope |> Some
                        else
                            None

                    let fromfromfrom =
                        if c.Has "fromfromfrom" then
                            c.TagText "fromfromfrom" |> parseScope |> Some
                        else
                            None

                    let fromfromfromfrom =
                        if c.Has "fromfromfromfrom" then
                            c.TagText "fromfromfromfrom" |> parseScope |> Some
                        else
                            None

                    let froms = [ from; fromfrom; fromfromfrom; fromfromfromfrom ] |> List.choose id

                    let prev =
                        if c.Has "prev" then
                            c.TagText "prev" |> parseScope |> Some
                        else
                            None

                    let prevprev =
                        if c.Has "prevprev" then
                            c.TagText "prevprev" |> parseScope |> Some
                        else
                            None

                    let prevprevprev =
                        if c.Has "prevprevprev" then
                            c.TagText "prevprevprev" |> parseScope |> Some
                        else
                            None

                    let prevprevprevprev =
                        if c.Has "prevprevprevprev" then
                            c.TagText "prevprevprevprev" |> parseScope |> Some
                        else
                            None

                    let prevs = [ prev; prevprev; prevprevprev; prevprevprevprev ] |> List.choose id

                    Some
                        { root = root
                          this = this
                          froms = Some froms
                          prevs = Some prevs }
                | None -> None
        | None -> None


    let private getOptionsFromComments
        parseScope
        allScopes
        anyScope
        (operator: Operator)
        (keyRequiredQuotes: bool)
        (valueRequiredQuotes: bool)
        (comments: string list)
        =
        let commentSetting name =
            comments
            |> List.tryPick (fun s ->
                let trimmed = s.Trim().TrimStart('#').Trim()
                let equalsIndex = trimmed.IndexOf '='

                if equalsIndex >= 0 then
                    let key = trimmed.Substring(0, equalsIndex).Trim()

                    if String.Equals(key, name, StringComparison.OrdinalIgnoreCase) then
                        Some(trimmed.Substring(equalsIndex + 1).Trim())
                    else
                        None
                else
                    None)

        let min, max, strictmin =
            match commentSetting "cardinality" with
            | Some c ->
                let nums = c.Split("..", 2)

                try
                    let minText, strictMin =
                        if nums.[0].StartsWith '~' then
                            nums.[0].Substring(1), false
                        else
                            nums.[0], true

                    match minText, nums.[1] with
                    | min, "inf" -> (int min), RulesParserConstants.CardinalityDefaultMaximum, strictMin
                    | min, max -> (int min), (int max), strictMin
                with _ ->
                    1, 1, true
            | None -> 1, 1, true

        let description =
            match comments |> List.filter (fun s -> s.StartsWith "##") with
            | [] -> None
            | [ x ] -> Some(x.Trim('#'))
            | xs -> Some(xs |> List.map (fun x -> x.Trim('#')) |> String.concat Environment.NewLine)

        let pushScope =
            commentSetting "push_scope" |> Option.map parseScope

        let reqScope =
            match comments |> List.tryFind (fun s -> s.StartsWith("# scope =")) with
            | Some s ->
                let rhs = s.Substring(s.IndexOf '=' + 1).Trim()

                match rhs.StartsWith('{') && rhs.EndsWith('}') with
                | true ->
                    rhs.Trim('{', '}')
                    |> (fun s -> s.Split(' '))
                    |> Array.filter (fun s -> s <> "")
                    |> Array.map parseScope
                    |> List.ofArray
                | false -> let scope = rhs |> parseScope in if scope = anyScope then allScopes else [ scope ]
            | None -> []

        let severity =
            commentSetting "severity" |> Option.map parseSeverity

        let referenceDetails =
            match comments |> List.tryFind (fun s -> s.Contains("outgoingReferenceLabel")) with
            | Some s -> s.Substring(s.IndexOf '=' + 1).Trim() |> (fun s -> true, s) |> Some
            | None ->
                match comments |> List.tryFind (fun s -> s.Contains("incomingReferenceLabel")) with
                | Some s -> s.Substring(s.IndexOf '=' + 1).Trim() |> (fun s -> false, s) |> Some
                | None -> None

        let comparison = operator = Operator.EqualEqual

        let errorIfMatched =
            commentSetting "error_if_only_match"

        let completionType =
            commentSetting "completion_type"

        let typePrefixFrom =
            commentSetting "type_prefix_from"

        let typeSuffixPatterns =
            match
                commentSetting "type_suffix_patterns"
                |> Option.orElseWith (fun () -> commentSetting "type_suffix_pattern")
            with
            | Some s ->
                s.Trim().Trim('{', '}').Split([| ' '; '\t'; ',' |], StringSplitOptions.RemoveEmptyEntries)
                |> Array.map (fun value -> value.Trim().Trim('"'))
                |> Array.filter (String.IsNullOrWhiteSpace >> not)
                |> Array.distinct
                |> Array.toList
            | _ -> []

        let parseStringListSetting (value: string) =
            value.Trim().Trim('{', '}')
                .Split([| ' '; '\t'; ',' |], StringSplitOptions.RemoveEmptyEntries)
            |> Array.map (fun v -> v.Trim().Trim('"').TrimStart('.').ToLowerInvariant())
            |> Array.filter (String.IsNullOrWhiteSpace >> not)
            |> Array.distinct
            |> Array.toList

        let fileExtensions =
            commentSetting "file_extensions"
            |> Option.map parseStringListSetting
            |> Option.defaultValue []

        let colorType =
            commentSetting "color_type"
            |> Option.map (fun v -> v.Trim().Trim('"').ToLowerInvariant())
            |> Option.filter (String.IsNullOrWhiteSpace >> not)

        let inject =
            commentSetting "inject"
            |> Option.map (fun v -> v.Trim().Trim('"'))
            |> Option.filter (String.IsNullOrWhiteSpace >> not)

        { min = min
          max = max
          strictMin = strictmin
          leafvalue = false
          description = description
          pushScope = pushScope
          replaceScopes = replaceScopes parseScope comments
          severity = severity
          requiredScopes = reqScope
          comparison = comparison
          referenceDetails = referenceDetails
          keyRequiredQuotes = keyRequiredQuotes
          valueRequiredQuotes = valueRequiredQuotes
          typeHint = None
          completionType = completionType
          errorIfOnlyMatch = errorIfMatched
          typePrefixFrom = typePrefixFrom
          typeSuffixPatterns = typeSuffixPatterns
          fileExtensions = fileExtensions
          colorType = colorType
          inject = inject }

    let fastStartsWith (x: string) y =
        x.StartsWith(y, StringComparison.OrdinalIgnoreCase)

    let fastEndsWith (x: string) y =
        x.EndsWith(y, StringComparison.OrdinalIgnoreCase)

    let rec internal processKey parseScope anyScope scopeGroup =
        function
        | "$any" -> ScalarField ScalarValue
        | "scalar" -> ScalarField ScalarValue
        | "wildcard_scalar" -> ScalarField ScalarValue
        | "bool" -> ValueField ValueType.Bool
        | "percentage_field" -> ValueField ValueType.Percent
        | "int_percentage_field" -> ValueField ValueType.Percent
        | "localisation" -> LocalisationField(false, false)
        | "localisation_synced" -> LocalisationField(true, false)
        | "localisation_inline" -> LocalisationField(false, true)
        | "filepath" -> FilepathField(None, None)
        | x when fastStartsWith x "filepath[" ->
            match getSettingFromString x "filepath" with
            | Some setting ->
                match setting.Contains ',' with
                | true ->
                    match setting.Split(',', 2) with
                    | [| folder; extension |] -> FilepathField(Some folder, Some extension)
                    | _ -> FilepathField(Some setting, None)
                | false -> FilepathField(Some setting, None)
            | None -> FilepathField(None, None)
        | "filename" -> FilenameField None
        | x when fastStartsWith x "filename[" ->
            match getSettingFromString x "filename" with
            | Some folder -> FilenameField(Some folder)
            | None -> FilenameField None
        | "abs_filepath"
        | "absolute_filepath" -> AbsoluteFilepathField
        | "date_field" -> ValueField Date
        | x when fastStartsWith x "date_field[" || fastStartsWith x "date_field(" -> ValueField Date
        | "datetime_field" -> ValueField DateTime
        | x when fastStartsWith x "datetime_field[" || fastStartsWith x "datetime_field(" -> ValueField DateTime
        | x when fastStartsWith x "prefix_field[" ->
            match getSettingFromString x "prefix_field" with
            | Some inner when not (String.IsNullOrWhiteSpace inner) ->
                PrefixedField(processKey parseScope anyScope scopeGroup (inner.Trim()))
            | _ -> ScalarField ScalarValue
        | x when fastStartsWith x "<" && fastEndsWith x ">" -> TypeField(TypeType.Simple(x.Trim([| '<'; '>' |])))
        | x when x.Contains '<' && x.Contains '>' ->
            let x = x.Trim('"')
            let prefixI = x.IndexOf '<'
            let suffixI = x.IndexOf '>'

            TypeField(
                TypeType.Complex(
                    x.Substring(0, prefixI),
                    x.Substring(prefixI + 1, suffixI - prefixI - 1),
                    x.Substring(suffixI + 1)
                )
            )
        | "int" -> defaultInt
        | x when fastStartsWith x "int[" || fastStartsWith x "int(" ->
            match getIntSettingFromString x with
            | Some(min, max) -> ValueField(ValueType.Int(min, max))
            | None -> defaultInt
        | "float" -> defaultFloat
        | x when fastStartsWith x "float[" || fastStartsWith x "float(" ->
            match getFloatSettingFromString x with
            | Some(min, max) -> ValueField(ValueType.Float(min, max))
            | None -> defaultFloat
        | x when fastStartsWith x "enum[" ->
            match getSettingFromString x "enum" with
            | Some name -> ValueField(ValueType.Enum name)
            | None -> ValueField(ValueType.Enum "")
        | x when fastStartsWith x "icon[" ->
            match getSettingFromString x "icon" with
            | Some folder -> IconField folder
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "alias_match_left[" ->
            match getSettingFromString x "alias_match_left" with
            | Some alias -> AliasField alias
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "alias_name[" ->
            match getSettingFromString x "alias_name" with
            | Some alias -> AliasField alias
            | None -> ScalarField ScalarValue
        | "scope_field" -> ScopeField [ anyScope ]
        | "variable_field" ->
            VariableField(
                false,
                false,
                (RulesParserConstants.floatFieldDefaultMinimum, RulesParserConstants.floatFieldDefaultMaximum)
            )
        | x when fastStartsWith x "variable_field[" || fastStartsWith x "variable_field(" ->
            match getFloatSettingFromString x with
            | Some(min, max) -> VariableField(false, false, (min, max))
            | None ->
                VariableField(
                    false,
                    false,
                    (RulesParserConstants.floatFieldDefaultMinimum, RulesParserConstants.floatFieldDefaultMaximum)
                )
        | "int_variable_field" ->
            VariableField(
                true,
                false,
                (decimal RulesParserConstants.IntFieldDefaultMinimum,
                 decimal RulesParserConstants.IntFieldDefaultMaximum)
            )
        | x when fastStartsWith x "int_variable_field[" || fastStartsWith x "int_variable_field(" ->
            match getIntSettingFromString x with
            | Some(min, max) -> VariableField(true, false, (decimal min, decimal max))
            | None ->
                VariableField(
                    true,
                    false,
                    (decimal RulesParserConstants.IntFieldDefaultMinimum,
                     decimal RulesParserConstants.IntFieldDefaultMaximum)
                )
        | "variable_field_32" ->
            VariableField(
                false,
                true,
                (RulesParserConstants.floatFieldDefaultMinimum, RulesParserConstants.floatFieldDefaultMaximum)
            )
        | x when fastStartsWith x "variable_field_32[" || fastStartsWith x "variable_field_32(" ->
            match getFloatSettingFromString x with
            | Some(min, max) -> VariableField(false, true, (min, max))
            | None ->
                VariableField(
                    false,
                    true,
                    (RulesParserConstants.floatFieldDefaultMinimum, RulesParserConstants.floatFieldDefaultMaximum)
                )
        | "int_variable_field_32" ->
            VariableField(
                true,
                true,
                (decimal RulesParserConstants.IntFieldDefaultMinimum,
                 decimal RulesParserConstants.IntFieldDefaultMaximum)
            )
        | x when fastStartsWith x "int_variable_field_32[" || fastStartsWith x "int_variable_field_32(" ->
            match getIntSettingFromString x with
            | Some(min, max) -> VariableField(true, true, (decimal min, decimal max))
            | None ->
                VariableField(
                    true,
                    true,
                    (decimal RulesParserConstants.IntFieldDefaultMinimum,
                     decimal RulesParserConstants.IntFieldDefaultMaximum)
                )
        | "value_field" ->
            ValueScopeMarkerField(
                false,
                (RulesParserConstants.floatFieldDefaultMinimum, RulesParserConstants.floatFieldDefaultMaximum)
            )
        | x when fastStartsWith x "value_field[" || fastStartsWith x "value_field(" ->
            match getFloatSettingFromString x with
            | Some(min, max) -> ValueScopeMarkerField(false, (min, max))
            | None ->
                ValueScopeMarkerField(
                    false,
                    (RulesParserConstants.floatFieldDefaultMinimum, RulesParserConstants.floatFieldDefaultMaximum)
                )
        | "int_value_field" ->
            ValueScopeMarkerField(
                true,
                (decimal RulesParserConstants.IntFieldDefaultMinimum,
                 decimal RulesParserConstants.IntFieldDefaultMaximum)
            )
        | x when fastStartsWith x "int_value_field[" || fastStartsWith x "int_value_field(" ->
            match getIntSettingFromString x with
            | Some(min, max) -> ValueScopeMarkerField(true, (decimal min, decimal max))
            | None ->
                ValueScopeMarkerField(
                    true,
                    (decimal RulesParserConstants.IntFieldDefaultMinimum,
                     decimal RulesParserConstants.IntFieldDefaultMaximum)
                )
        | x when fastStartsWith x "value_set[" ->
            match getSettingFromString x "value_set" with
            | Some variable -> VariableSetField variable
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "value[" ->
            match getSettingFromString x "value" with
            | Some variable -> VariableGetField variable
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "dynamic_value[" ->
            match getSettingFromString x "dynamic_value" with
            | Some variable -> DynamicValueField variable
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "scope[" ->
            match getSettingFromString x "scope" with
            | Some target -> ScopeField [ (parseScope target) ]
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "event_target" ->
            match getSettingFromString x "event_target" with
            | Some target -> ScopeField [ (parseScope target) ]
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "single_alias_right" ->
            match getSettingFromString x "single_alias_right" with
            | Some alias -> SingleAliasField alias
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "alias_keys_field" ->
            match getSettingFromString x "alias_keys_field" with
            | Some aliasKey -> AliasValueKeysField aliasKey
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "alias_params_field" ->
            match getSettingFromString x "alias_params_field" with
            | Some setting ->
                match setting.Split(',', 2) |> Array.map (fun p -> p.Trim()) with
                | [| aliasName; selectorField |] when aliasName <> "" && selectorField <> "" ->
                    AliasParamsField(aliasName, selectorField)
                | [| aliasName |] when aliasName <> "" -> AliasParamsField(aliasName, aliasName)
                | _ -> ScalarField ScalarValue
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "stellaris_name_format" ->
            match getSettingFromString x "stellaris_name_format" with
            | Some aliasKey -> ValueField(STLNameFormat aliasKey)
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "name_format[" ->
            match getSettingFromString x "name_format" with
            | Some formatType -> NameFormatField formatType
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "scope_group[" ->
            match getSettingFromString x "scope_group" with
            | Some aliasKey ->
                match scopeGroup |> Map.tryFind aliasKey with
                | Some scopes -> ScopeField scopes
                | None -> ScalarField(ScalarValue)
            | None -> ScalarField ScalarValue
        | "portrait_dna_field" -> ValueField CK2DNA
        | "portrait_properties_field" -> ValueField CK2DNAProperty
        | "colour_field" -> MarkerField(Marker.ColourField None)
        | "color_field" -> MarkerField(Marker.ColourField None)
        | x when fastStartsWith x "colour[" ->
            getSettingFromString x "colour"
            |> Option.map (fun value -> value.Trim().Trim('"').ToLowerInvariant())
            |> Marker.ColourField
            |> MarkerField
        | x when fastStartsWith x "color[" ->
            getSettingFromString x "color"
            |> Option.map (fun value -> value.Trim().Trim('"').ToLowerInvariant())
            |> Marker.ColourField
            |> MarkerField
        | "ir_country_tag_field" -> MarkerField Marker.IRCountryTag
        | "ir_family_name_field" -> ValueField IRFamilyName
        | "$command" -> CommandField
        | "$script_value_reference" -> ScriptValueReferenceField
        | "$define_reference" -> DefineReferenceField
        | "$array_define_reference" -> ArrayDefineReferenceField
        | x when fastStartsWith x "$tags[" ->
            match getSettingFromString x "$tags" with
            | Some name -> TagsField(name, false)
            | None -> ScalarField ScalarValue
        | x when fastStartsWith x "$tags_condition[" ->
            match getSettingFromString x "$tags_condition" with
            | Some name -> TagsField(name, true)
            | None -> ScalarField ScalarValue
        | "$database_object" -> DatabaseObjectField
        | x when fastStartsWith x "glob.i:" -> PatternField(GlobPattern, x.Substring(7), true)
        | x when fastStartsWith x "glob:" -> PatternField(GlobPattern, x.Substring(5), false)
        | x when fastStartsWith x "ant.i:" -> PatternField(AntPattern, x.Substring(6), true)
        | x when fastStartsWith x "ant:" -> PatternField(AntPattern, x.Substring(4), false)
        | x when fastStartsWith x "re.i:" -> PatternField(RegexPattern, x.Substring(5), true)
        | x when fastStartsWith x "re:" -> PatternField(RegexPattern, x.Substring(3), false)
        | "$shader_effect" -> ShaderEffectField
        | "$mesh_locator" -> MeshLocatorField
        | "$technology_with_level" -> TechnologyWithLevelField
        | "$parameter" -> ParameterField
        | "$parameter_value" -> ParameterValueField
        | "$localisation_parameter" -> LocalisationParameterField
        | "ignore_field" -> IgnoreMarkerField
        | x ->
            // eprintfn "ps %s" x
            SpecificField(SpecificValue(StringResource.stringManager.InternIdentifierToken(x.Trim([| '\"' |]))))



    let private configNode
        processChildConfig
        parseScope
        allScopes
        anyScope
        scopeGroup
        (node: Node)
        (comments: string list)
        (key: string)
        =
        let children = getNodeComments node

        let options =
            getOptionsFromComments parseScope allScopes anyScope Operator.Equals node.KeyId.quoted false comments

        let innerRules =
            children
            |> Seq.choose (processChildConfig parseScope allScopes anyScope scopeGroup)
            |> Seq.toArray

        let rule =
            match key with
            | x when x.StartsWith "subtype[" ->
                match getSettingFromString x "subtype" with
                | Some st when st.StartsWith '!' -> SubtypeRule(st.Substring(1), false, innerRules)
                | Some st -> SubtypeRule(st, true, innerRules)
                | None -> failwith $"Invalid subtype string %s{x}"
            | _ when node.KeyPrefixId.IsSome && node.ValuePrefixId.IsSome -> NodeRule(JominiGuiField, innerRules)
            | x -> NodeRule(processKey parseScope anyScope scopeGroup (x.Trim('"')), innerRules)

        NewRule(rule, options)

    let private configValueClause
        processChildConfig
        parseScope
        allScopes
        anyScope
        scopeGroup
        (valueclause: ValueClause)
        (comments: string list)
        =
        let children = getNodeComments valueclause

        let options =
            getOptionsFromComments parseScope allScopes anyScope Operator.Equals false false comments

        let innerRules =
            children
            |> Seq.choose (processChildConfig parseScope allScopes anyScope scopeGroup)
            |> Seq.toArray

        let rule = ValueClauseRule innerRules
        NewRule(rule, options)

    let private rgbRule =
        LeafValueRule(ValueField(ValueType.Int(0, 255))),
        { min = 3
          max = 4
          strictMin = true
          leafvalue = true
          description = None
          pushScope = None
          replaceScopes = None
          severity = None
          requiredScopes = []
          comparison = false
          referenceDetails = None
          keyRequiredQuotes = false
          valueRequiredQuotes = false
          typeHint = None
          completionType = None
          errorIfOnlyMatch = None
          typePrefixFrom = None
          typeSuffixPatterns = []
          fileExtensions = []
          colorType = None
          inject = None }

    let private hsvRule =
        LeafValueRule(ValueField(ValueType.Float(0.0M, 2.0M))),
        { min = 3
          max = 4
          strictMin = true
          leafvalue = true
          description = None
          pushScope = None
          replaceScopes = None
          severity = None
          requiredScopes = []
          comparison = false
          referenceDetails = None
          keyRequiredQuotes = false
          valueRequiredQuotes = false
          typeHint = None
          completionType = None
          errorIfOnlyMatch = None
          typePrefixFrom = None
          typeSuffixPatterns = []
          fileExtensions = []
          colorType = None
          inject = None }

    let private configLeaf parseScope allScopes anyScope scopeGroup (leaf: Leaf) (comments: string list) (key: string) =
        let leftfield = processKey parseScope anyScope scopeGroup (key.Trim('"'))

        let options =
            getOptionsFromComments
                parseScope
                allScopes
                anyScope
                leaf.Operator
                leaf.KeyId.quoted
                leaf.ValueId.quoted
                comments

        let rightkey = leaf.Value.ToString()

        match key, rightkey with
        | _, x when x.StartsWith("colour[") ->
            let colourRules =
                match getSettingFromString x "colour" with
                | Some "rgb" -> [| rgbRule |]
                | Some "hsv" -> [| hsvRule |]
                | _ -> [| rgbRule; hsvRule |]

            NewRule(NodeRule(leftfield, colourRules), options)
        | l, r when l.StartsWith "clause_single_alias" && r.StartsWith "single_alias_right" ->
            match getSettingFromString l "clause_single_alias", getSettingFromString r "single_alias_right" with
            | Some ls, Some rs ->
                let leftfield = LeafValueRule(SingleAliasClauseField(ls, rs))
                NewRule(leftfield, options)
            | _ ->
                let rightfield = processKey parseScope anyScope scopeGroup (rightkey.Trim('"'))
                let leafRule = LeafRule(leftfield, rightfield)
                NewRule(leafRule, options)
        | _, _ ->
            let rightfield = processKey parseScope anyScope scopeGroup (rightkey.Trim('"'))
            let leafRule = LeafRule(leftfield, rightfield)
            NewRule(leafRule, options)

    let private configLeafValue
        parseScope
        allScopes
        anyScope
        scopeGroup
        (leafvalue: LeafValue)
        (comments: string list)
        =
        let field =
            processKey parseScope anyScope scopeGroup (leafvalue.Value.ToRawString())

        let options =
            { getOptionsFromComments
                  parseScope
                  allScopes
                  anyScope
                  Operator.Equals
                  false
                  leafvalue.ValueId.quoted
                  comments with
                leafvalue = true }

        NewRule(LeafValueRule(field), options)

    let private configRootLeaf
        processChildConfig
        parseScope
        allScopes
        anyScope
        scopeGroup
        (leaf: Leaf)
        (comments: string list)
        =
        match leaf.Key with
        | x when x.StartsWith "alias[" ->
            match getAliasSettingsFromString x with
            | Some(a, rn) ->
                let innerRule = configLeaf parseScope allScopes anyScope scopeGroup leaf comments rn
                AliasRule(a, innerRule)
            | None ->
                let rule =
                    configLeaf parseScope allScopes anyScope scopeGroup leaf comments leaf.Key

                TypeRule(x, rule)
        | x when x.StartsWith "single_alias[" ->
            match getSettingFromString x "single_alias" with
            | Some a ->
                let innerRule = configLeaf parseScope allScopes anyScope scopeGroup leaf comments x
                SingleAliasRule(a, innerRule)
            | None ->
                let rule =
                    configLeaf parseScope allScopes anyScope scopeGroup leaf comments leaf.Key

                TypeRule(x, rule)
        | x ->
            let rule =
                configLeaf parseScope allScopes anyScope scopeGroup leaf comments leaf.Key

            TypeRule(x, rule)

    let private configRootNode
        processChildConfig
        parseScope
        allScopes
        anyScope
        scopeGroup
        (node: Node)
        (comments: string list)
        =
        let children = getNodeComments node

        let options =
            getOptionsFromComments parseScope allScopes anyScope Operator.Equals false false comments

        let innerRules =
            children
            |> Seq.choose (processChildConfig parseScope allScopes anyScope scopeGroup)
            |> Seq.toArray

        match node.Key with
        | x when x.StartsWith "alias[" ->
            match getAliasSettingsFromString x with
            | Some(a, rn) ->
                let innerRule =
                    configNode processChildConfig parseScope allScopes anyScope scopeGroup node comments rn
                // log "%s %A" a innerRule
                AliasRule(a, innerRule)
            | None ->
                TypeRule(
                    x,
                    NewRule(
                        NodeRule(
                            SpecificField(SpecificValue(StringResource.stringManager.InternIdentifierToken x)),
                            innerRules
                        ),
                        options
                    )
                )
        | x when x.StartsWith "single_alias[" ->
            match getSettingFromString x "single_alias" with
            | Some a ->
                let innerRule =
                    configNode processChildConfig parseScope allScopes anyScope scopeGroup node comments x

                SingleAliasRule(a, innerRule)
            | None ->
                TypeRule(
                    x,
                    NewRule(
                        NodeRule(
                            SpecificField(SpecificValue(StringResource.stringManager.InternIdentifierToken x)),
                            innerRules
                        ),
                        options
                    )
                )
        | x ->
            TypeRule(
                x,
                NewRule(
                    NodeRule(
                        SpecificField(SpecificValue(StringResource.stringManager.InternIdentifierToken x)),
                        innerRules
                    ),
                    options
                )
            )

    let rec private processChildConfig
        parseScope
        allScopes
        anyScope
        scopeGroup
        ((child, comments): Child * string list)
        =
        match child with
        | NodeC n -> Some(configNode processChildConfig parseScope allScopes anyScope scopeGroup n comments n.Key)
        | ValueClauseC vc ->
            Some(configValueClause processChildConfig parseScope allScopes anyScope scopeGroup vc comments)
        | LeafC l -> Some(configLeaf parseScope allScopes anyScope scopeGroup l comments l.Key)
        | LeafValueC lv -> Some(configLeafValue parseScope allScopes anyScope scopeGroup lv comments)
        | _ -> None

    let private extendedMetadataRootKeys =
        set [ "priorities"; "system_scopes"; "locales"; "database_object_types"; "on_actions" ]

    let private processChildConfigRoot
        parseScope
        allScopes
        anyScope
        scopeGroup
        ((child, comments): Child * string list)
        =
        match child with
        | NodeC n when n.Key == "types" -> None
        | NodeC n when extendedMetadataRootKeys.Contains n.Key -> None
        | NodeC n -> Some(configRootNode processChildConfig parseScope allScopes anyScope scopeGroup n comments)
        | LeafC l when extendedMetadataRootKeys.Contains l.Key -> None
        | LeafC l -> Some(configRootLeaf processChildConfig parseScope allScopes anyScope scopeGroup l comments)
        // |LeafValueC lv -> Some (configLeafValue lv comments)
        | _ -> None

    // Types

    let private processType parseScope allScopes anyScope scopeGroup (node: Node) (comments: string list) =
        let parseLocalisation (child: Child, comments: string list) =
            match child with
            | LeafC loc ->
                let required = comments |> List.exists (fun s -> s.Contains "required")
                let optional = comments |> List.exists (fun s -> s.Contains "optional")
                let primary = comments |> List.exists (fun s -> s.Contains "primary")
                let key = loc.Key
                let value = loc.Value.ToRawString()

                match value.IndexOf '$' with
                | -1 ->
                    Some
                        { name = key
                          prefix = ""
                          suffix = ""
                          required = required
                          optional = optional
                          replaceScopes = replaceScopes parseScope comments
                          explicitField = Some value
                          primary = primary }
                | dollarIndex ->
                    let prefix = value.Substring(0, dollarIndex)
                    let suffix = value.Substring(dollarIndex + 1)

                    Some
                        { name = key
                          prefix = prefix
                          suffix = suffix
                          required = required
                          optional = optional
                          replaceScopes = replaceScopes parseScope comments
                          explicitField = None
                          primary = primary }
            | _ -> None

        let parseSubTypeLocalisation (subtype: Node) =
            match subtype.Key.StartsWith("subtype[") with
            | true ->
                match getSettingFromString subtype.Key "subtype" with
                | Some st ->
                    let res = getNodeComments subtype |> List.choose parseLocalisation
                    Some(st, res)
                | _ -> None
            | _ -> None

        let parseModifier (child: Child, comments: string list) =
            match child with
            | LeafC modifier ->
                let value = modifier.Key

                let category =
                    modifier.Value.ToRawString() |> modifierCategoryManager.ParseModifier()

                let explicit = comments |> List.exists (fun s -> s.Contains "explicit")

                let description =
                    match comments |> List.tryFind (fun s -> s.StartsWith "##") with
                    | Some d -> Some(d.TrimStart('#'))
                    | None -> None

                match value.IndexOf '$' with
                | -1 ->
                    Some
                        { TypeModifier.prefix = ""
                          suffix = ""
                          category = category
                          documentation = description
                          explicit = explicit }
                | dollarIndex ->
                    let prefix = value.Substring(0, dollarIndex)
                    let suffix = value.Substring(dollarIndex + 1)

                    Some
                        { TypeModifier.prefix = prefix
                          suffix = suffix
                          category = category
                          documentation = description
                          explicit = explicit }
            | _ -> None

        let parseSubTypeModifier (subtype: Node) =
            match subtype.Key.StartsWith("subtype[") with
            | true ->
                match getSettingFromString subtype.Key "subtype" with
                | Some st ->
                    let res = getNodeComments subtype |> List.choose parseModifier
                    Some(st, res)
                | _ -> None
            | _ -> None

        let parseSubType (child: Child, comments: string list) =
            match child with
            | NodeC subtype when subtype.Key.StartsWith "subtype" ->
                let typekeyfilter =
                    match comments |> List.tryFind (fun s -> s.Contains "type_key_filter") with
                    | Some c -> Some(c.Substring(c.IndexOf '=' + 1).Trim())
                    | None -> None

                let displayName =
                    match comments |> List.tryFind (fun s -> s.Contains "display_name") with
                    | Some c -> Some(c.Substring(c.IndexOf '=' + 1).Trim())
                    | None -> None

                let abbreviation =
                    match comments |> List.tryFind (fun s -> s.Contains "abbreviation") with
                    | Some c -> Some(c.Substring(c.IndexOf '=' + 1).Trim())
                    | None -> None

                let pushScope =
                    match comments |> List.tryFind (fun s -> s.Contains("push_scope")) with
                    | Some s -> s.Substring(s.IndexOf '=' + 1).Trim() |> parseScope |> Some
                    | None -> None

                let startsWith =
                    match comments |> List.tryFind (fun s -> s.Contains "starts_with") with
                    | Some c -> Some(c.Substring(c.IndexOf '=' + 1).Trim())
                    | None -> None

                let typeKeyRegex =
                    match comments |> List.tryFind (fun s -> s.Contains "type_key_regex") with
                    | Some c when c.Contains '=' -> Some(c.Substring(c.IndexOf '=' + 1).Trim().Trim('"'))
                    | _ -> None

                let onlyIfNot =
                    match comments |> List.tryFind (fun s -> s.Contains "only_if_not") with
                    | Some c ->
                        let valid = c.Contains '='

                        if valid then
                            let rhs = c.Substring(c.IndexOf '=' + 1).Trim()

                            let values =
                                match rhs.StartsWith('{') && rhs.EndsWith('}') with
                                | true -> rhs.Trim('{', '}') |> (fun s -> s.Split(' ')) |> List.ofArray
                                | false -> [ rhs ]

                            values
                        else
                            []
                    | None -> []

                let rules =
                    (getNodeComments subtype
                     |> Seq.choose (processChildConfig parseScope allScopes anyScope scopeGroup))
                    |> Seq.toArray

                match getSettingFromString subtype.Key "subtype" with
                | Some key ->
                    Some
                        { name = key
                          rules = rules
                          typeKeyField = typekeyfilter
                          typeKeyRegex = typeKeyRegex
                          pushScope = pushScope
                          localisation = []
                          startsWith = startsWith
                          displayName = displayName
                          abbreviation = abbreviation
                          onlyIfNot = onlyIfNot
                          modifiers = [] }
                | None -> None
            | _ -> None

        let getSkipRootKey (node: Node) =
            let createSkipRoot (s: string) =
                if s == "any" then
                    SkipRootKey.AnyKey
                else
                    SkipRootKey.SpecificKey s

            let skipRootKeyLeaves = node.Leafs "skip_root_key" |> List.ofSeq

            match skipRootKeyLeaves with
            | [ x ] when x.ValueText = "any" -> [ SkipRootKey.AnyKey ]
            | [ x ] -> [ SkipRootKey.SpecificKey x.ValueText ]
            | x :: xs ->
                let shouldMatch = x.Operator = Operator.Equals
                [ SkipRootKey.MultipleKeys((x :: xs) |> List.map (fun y -> y.ValueText), shouldMatch) ]
            | [] ->
                node.Child "skip_root_key"
                |> Option.map (fun c -> c.LeafValues |> Seq.map (fun lv -> createSkipRoot (lv.Value.ToRawString())))
                |> Option.defaultValue Seq.empty
                |> Seq.toList

        // match node.Has "skip_root_key", node.TagText "skip_root_key" with
        // |_, "any" -> [SkipRootKey.AnyKey]
        // |true, "" -> node.Child "skip_root_key" |> Option.map (fun c -> c.LeafValues |> Seq.map (fun lv -> createSkipRoot (lv.Value.ToRawString())))
        //                                         |> Option.defaultValue Seq.empty
        //                                         |> Seq.toList
        // |true, x -> [SkipRootKey.SpecificKey x]
        // |false, _ -> []
        let validTypeKeys =
            [| "name_field"
               "type_per_file"
               "skip_root_key"
               "should_be_used"
               "path"
               "path_strict"
               "path_file"
               "path_extension"
               "starts_with"
               "type_key_regex"
               "severity"
               "unique"
               "error_unknown_keys" |]

        let checkTypeChildren (child: Child) =
            match child with
            | LeafC leaf ->
                if Array.contains leaf.Key validTypeKeys then
                    ()
                else
                    log $"Unexpected leaf %s{leaf.Key} found in type definition at %A{leaf.Position}"
            | NodeC node ->
                match node.Key with
                | "localisation" -> ()
                | "modifiers" -> ()
                | "obsolete_keys" -> ()
                | x when x.StartsWith "subtype" -> ()
                | x -> log $"Unexpected node %s{x} found in type definition at %A{node.Position}"
            | LeafValueC leafvalue ->
                log $"Unexpected leafvalue %s{leafvalue.Key} found in type definition at %A{leafvalue.Position}"
            | ValueClauseC vc -> log $"Unexpected valueclause found in type definition at %A{vc.Position}"
            | CommentC _ -> ()

        match node.Key with
        | x when x.StartsWith("type") ->
            node.AllArray |> Array.iter checkTypeChildren
            let typename = getSettingFromString node.Key "type"

            let namefield =
                if node.Has "name_field" then
                    Some(node.TagText "name_field")
                else
                    None

            let type_per_file = node.TagText "type_per_file" == "yes"

            let key_prefix =
                if node.Has "type_key_prefix" then
                    Some(node.TagText "type_key_prefix")
                else
                    None

            let pathOptions = getPathOptions node

            let startsWith =
                if node.Has "starts_with" then
                    Some(node.TagText "starts_with")
                else
                    None

            let typeKeyRegex =
                match comments |> List.tryFind (fun s -> s.Contains "type_key_regex") with
                | Some c when c.Contains '=' -> Some(c.Substring(c.IndexOf '=' + 1).Trim().Trim('"'))
                | _ -> None

            let skiprootkey = getSkipRootKey node
            let subtypes = getNodeComments node |> List.choose parseSubType
            let warningOnly = node.TagText "severity" == "warning"
            let unique = node.TagText "unique" == "yes"

            let shouldBeReferenced =
                match node.TagText "should_be_used" with
                | "yes" -> RefRequired
                | "unless_subtyped" -> RefRequiredUnlessSubtyped
                | _ -> RefNotRequired

            let unknownKeyHandling =
                match node.TagText "error_unknown_keys" with
                | "yes" -> UnknownKeyError
                | "suggest" -> UnknownKeySuggest
                | _ -> UnknownKeyIgnore

            let obsoleteKeys =
                node.Child "obsolete_keys"
                |> Option.map (fun o ->
                    o.Leaves
                    |> Seq.map (fun leaf -> leaf.Key.ToLowerInvariant(), leaf.ValueText)
                    |> Map.ofSeq)
                |> Option.defaultValue Map.empty

            let localisation =
                node.Child "localisation"
                |> Option.map (fun l -> getNodeComments l |> List.choose parseLocalisation)
                |> Option.defaultValue []

            let modifiers =
                node.Child "modifiers"
                |> Option.map (fun l -> getNodeComments l |> List.choose parseModifier)
                |> Option.defaultValue []

            let subtypelocalisations =
                node.Child "localisation"
                |> Option.map (fun l -> l.Children |> List.choose parseSubTypeLocalisation)
                |> Option.defaultValue []

            let subtypeModifiers =
                node.Child "modifiers"
                |> Option.map (fun l -> l.Children |> List.choose parseSubTypeModifier)
                |> Option.defaultValue []

            let subtypes =
                subtypes
                |> List.map (fun st ->
                    let loc =
                        subtypelocalisations
                        |> List.filter (fun (stl, _) -> stl = st.name)
                        |> List.collect snd in

                    { st with localisation = loc })

            let subtypes =
                subtypes
                |> List.map (fun st ->
                    let mods =
                        subtypeModifiers
                        |> List.filter (fun (stl, _) -> stl = st.name)
                        |> List.collect snd in

                    { st with modifiers = mods })

            let typekeyfilter =
                match comments |> List.tryFind (fun s -> s.Contains "type_key_filter") with
                | Some c ->
                    //log "c %A" c
                    let valid = c.Contains '=' || c.Contains "<>"

                    if valid then
                        let negative = c.Contains "<>"

                        let rhs =
                            if negative then
                                c.Substring(c.IndexOf "<>" + 2).Trim()
                            else
                                c.Substring(c.IndexOf '=' + 1).Trim()

                        let values =
                            match rhs.StartsWith('{') && rhs.EndsWith('}') with
                            | true -> rhs.Trim('{', '}') |> (fun s -> s.Split(' ')) |> List.ofArray
                            | false -> [ rhs ]

                        Some(values, negative)
                    else
                        None
                | None -> None

            let rootCompletionFromSubtypes =
                match comments |> List.tryFind (fun s -> s.Contains "root_completion") with
                | Some c when c.Contains '=' ->
                    c.Substring(c.IndexOf '=' + 1).Trim().Equals("subtypes", StringComparison.OrdinalIgnoreCase)
                | _ -> false

            let graphData =
                match comments |> List.tryFind (fun s -> s.Contains "graph_related_types") with
                | Some c ->
                    let valid = c.Contains '='

                    if valid then
                        let rhs = c.Substring(c.IndexOf '=' + 1).Trim()

                        let values =
                            match rhs.StartsWith('{') && rhs.EndsWith('}') with
                            | true -> rhs.Trim('{', '}') |> (fun s -> s.Split(' ')) |> List.ofArray
                            | false -> [ rhs ]

                        values
                    else
                        []
                | None -> []

            match typename with
            | Some tn ->
                Some
                    { name = tn
                      nameField = namefield
                      type_per_file = type_per_file
                      pathOptions = pathOptions
                      conditions = None
                      subtypes = subtypes
                      typeKeyFilter = typekeyfilter
                      typeKeyRegex = typeKeyRegex
                      rootCompletionFromSubtypes = rootCompletionFromSubtypes
                      skipRootKey = skiprootkey
                      warningOnly = warningOnly
                      localisation = localisation
                      modifiers = modifiers
                      startsWith = startsWith
                      unique = unique
                      shouldBeReferenced = shouldBeReferenced
                      unknownKeyHandling = unknownKeyHandling
                      obsoleteKeys = obsoleteKeys
                      graphRelatedTypes = graphData
                      keyPrefix = key_prefix }
            | None -> None
        | _ -> None



    let private processChildType parseScope allScopes anyScope scopeGroup ((child, comments): Child * string list) =
        match child with
        | NodeC n when n.Key == "types" ->
            let inner ((child2, comments2): Child * string list) =
                match child2 with
                | NodeC n2 -> (processType parseScope allScopes anyScope scopeGroup n2 comments2)
                | _ -> None

            Some(getNodeComments n |> List.choose inner)
        | _ -> None

    let private processEnum (node: Node) (comments: string list) =
        match node.Key with
        | x when x.StartsWith("enum") ->
            let enumname = getSettingFromString node.Key "enum"

            let values =
                node.LeafValues
                |> Array.ofSeq
                |> Array.map (fun lv -> lv.Value.ToString().Trim('\"'), None)

            match enumname with
            | Some en ->
                let description =
                    match comments |> List.tryFind (fun s -> s.StartsWith "##") with
                    | Some d -> d.Trim('#')
                    | None -> en

                Some
                    { key = en
                      values = values |> Array.map fst
                      description = description
                      valuesWithRange = values }
            | None -> None
        | _ -> None

    let private processChildEnum ((child, comments): Child * string list) =
        match child with
        | NodeC n when n.Key == "enums" ->
            let inner ((child2, comments2): Child * string list) =
                match child2 with
                | NodeC n2 -> (processEnum n2 comments2)
                | _ -> None

            Some(getNodeComments n |> List.choose inner)
        | _ -> None

    let private processComplexEnum (node: Node) (comments: string list) =
        match node.Key with
        | x when x.StartsWith("complex_enum") ->
            let enumname = getSettingFromString node.Key "complex_enum"
            let pathOptions = getPathOptions node
            let nametree = node.Child "name"
            let start_from_root = node.TagText "start_from_root" == "yes"

            match (enumname, nametree) with
            | Some en, Some nt ->
                let description =
                    match comments |> List.tryFind (fun s -> s.StartsWith "##") with
                    | Some d -> d.Trim('#')
                    | None -> en

                Some
                    { name = en
                      pathOptions = pathOptions
                      nameTree = nt
                      start_from_root = start_from_root
                      description = description }
            | _ -> None
        | _ -> None

    let private processComplexChildEnum ((child, comments): Child * string list) =
        match child with
        | NodeC n when n.Key == "enums" ->
            let inner ((child2, comments2): Child * string list) =
                match child2 with
                | NodeC n2 -> (processComplexEnum n2 comments2)
                | _ -> None

            Some(getNodeComments n |> List.choose inner)
        | _ -> None


    let private processValue (node: Node) (comments: string list) =
        match node.Key with
        | x when x.StartsWith("value") ->
            let enumname = getSettingFromString node.Key "value"

            let values =
                node.LeafValues
                |> List.ofSeq
                |> List.map (fun lv -> lv.Value.ToString().Trim('\"'))

            match enumname with
            | Some en -> Some(en, values)
            | None -> None
        | _ -> None

    let private processChildValue ((child, comments): Child * string list) =
        match child with
        | NodeC n when n.Key == "values" ->
            let inner ((child2, comments2): Child * string list) =
                match child2 with
                | NodeC n2 -> (processValue n2 comments2)
                | _ -> None

            Some(getNodeComments n |> List.choose inner)
        | _ -> None



    let replaceSingleAliases (rules: RootRule array) =
        let singlealiases =
            rules
            |> Array.choose (function
                | SingleAliasRule(name, inner) -> Some(SingleAliasRule(name, inner))
                | _ -> None)

        let singlealiasesmap =
            singlealiases
            |> Array.choose (function
                | SingleAliasRule(name, inner) -> Some(name, inner)
                | _ -> None)
            |> Map.ofArray

        let aliasInStack name stack =
            stack |> List.exists (fun n -> String.Equals(n, name, StringComparison.OrdinalIgnoreCase))

        let rec cataRule stack rule : NewRule =
            match rule with
            | NodeRule(l, r), o -> (NodeRule(l, r |> Array.map (cataRule stack)), o)
            | ValueClauseRule r, o -> (ValueClauseRule(r |> Array.map (cataRule stack)), o)
            | SubtypeRule(a, b, i), o -> (SubtypeRule(a, b, (i |> Array.map (cataRule stack))), o)
            | LeafRule(l, SingleAliasField name), o when aliasInStack name stack -> rule
            | LeafRule(l, SingleAliasField name), o ->
                let nextStack = name :: stack

                match singlealiasesmap |> Map.tryFind name with
                | Some(LeafRule(al, ar), ao) ->
                    // log (sprintf "Replaced single alias leaf %A %s with leaf %A" (l |> function |ValueField (Specific x) -> StringResource.stringManager.GetStringForIDs x |_ -> "") name (al |> function |ValueField (Specific x) -> StringResource.stringManager.GetStringForIDs x |_ -> ""))
                    cataRule nextStack (LeafRule(l, ar), o)
                | Some(NodeRule(al, ar), ao) ->
                    // log (sprintf "Replaced single alias leaf %A %s with node %A" (l |> function |ValueField (Specific x) -> StringResource.stringManager.GetStringForIDs x |_ -> "") name (al |> function |ValueField (Specific x) -> StringResource.stringManager.GetStringForIDs x |_ -> ""))
                    NodeRule(l, ar |> Array.map (cataRule nextStack)), o
                | x ->
                    log (
                        sprintf
                            "Failed to find defined single alias %s when replacing single alias leaf %A. Found %A"
                            name
                            (l
                             |> function
                                 | SpecificField(SpecificValue x) -> StringResource.stringManager.GetStringForIDs x
                                 | _ -> "")
                            x
                    )

                    rule
            /// TODO: Add clause key validation
            | LeafValueRule(SingleAliasClauseField(_, name)), o when aliasInStack name stack -> rule
            | LeafValueRule(SingleAliasClauseField(clauseKey, name)), o ->
                let nextStack = name :: stack

                match singlealiasesmap |> Map.tryFind name with
                | Some(NodeRule(al, ar), ao) -> ValueClauseRule(ar |> Array.map (cataRule nextStack)), o
                | x ->
                    log $"Failed to find defined single alias %s{name} when replacing single alias clause. Found %A{x}"

                    rule

            | _ -> rule

        let rulesMapper =
            function
            | TypeRule(name, rule) -> TypeRule(name, cataRule [] rule)
            | AliasRule(name, rule) -> AliasRule(name, cataRule [] rule)
            | SingleAliasRule(name, rule) -> SingleAliasRule(name, cataRule [] rule)

        rules |> Array.map rulesMapper

    let applyConfigInjections (sourceRulesByFile: (string * RootRule list) list) (rules: RootRule array) =
        let normalisePath (path: string) =
            path.Replace('\\', '/').TrimStart('/').ToLowerInvariant()

        let findSourceRules sourcePath =
            let expected = normalisePath sourcePath

            sourceRulesByFile
            |> List.tryPick (fun (filename, fileRules) ->
                let actual = normalisePath filename

                if actual = expected || actual.EndsWith("/" + expected, StringComparison.OrdinalIgnoreCase) then
                    Some fileRules
                else
                    None)

        let segmentMatches (pattern: string) (value: string) =
            if pattern = "*" then
                true
            elif pattern.Contains('*') || pattern.Contains('?') then
                let regex =
                    "^"
                    + System.Text.RegularExpressions.Regex.Escape(pattern)
                        .Replace(@"\*", ".*")
                        .Replace(@"\?", ".")
                    + "$"

                System.Text.RegularExpressions.Regex.IsMatch(
                    value,
                    regex,
                    System.Text.RegularExpressions.RegexOptions.IgnoreCase
                    ||| System.Text.RegularExpressions.RegexOptions.CultureInvariant
                )
            else
                String.Equals(pattern, value, StringComparison.OrdinalIgnoreCase)

        let fieldName =
            function
            | SpecificField(SpecificValue value) ->
                Some(CWTools.Utilities.StringResource.stringManager.GetStringForID value.normal)
            | _ -> None

        let rootName =
            function
            | TypeRule(name, _)
            | AliasRule(name, _)
            | SingleAliasRule(name, _) -> name

        let rootRule =
            function
            | TypeRule(_, rule)
            | AliasRule(_, rule)
            | SingleAliasRule(_, rule) -> rule

        let ruleName (rule, _) =
            match rule with
            | NodeRule(left, _)
            | LeafRule(left, _) -> fieldName left
            | SubtypeRule(name, _, _) -> Some name
            | LeafValueRule _
            | ValueClauseRule _ -> None

        let childRules =
            function
            | NodeRule(_, children)
            | ValueClauseRule children
            | SubtypeRule(_, _, children) -> Some children
            | _ -> None

        let rec findInRule segments newRule =
            match segments with
            | [] -> [ newRule ]
            | segment :: tail ->
                match ruleName newRule with
                | Some name when segmentMatches segment name ->
                    if tail.IsEmpty then
                        [ newRule ]
                    else
                        match childRules (fst newRule) with
                        | Some children -> children |> Array.toList |> List.collect (findInRule tail)
                        | None -> []
                | _ -> []

        let findInRoot segments root =
            match segments with
            | [] -> []
            | segment :: tail when segmentMatches segment (rootName root) ->
                let rule = rootRule root

                if tail.IsEmpty then
                    [ rule ]
                else
                    match childRules (fst rule) with
                    | Some children -> children |> Array.toList |> List.collect (findInRule tail)
                    | None -> []
            | _ -> []

        let resolveInject (expression: string) =
            match expression.Split('@', 2, StringSplitOptions.RemoveEmptyEntries) with
            | [| sourcePath; memberPath |] ->
                let segments =
                    memberPath.Replace('\\', '/').Split([| '/' |], StringSplitOptions.RemoveEmptyEntries)
                    |> Array.toList

                findSourceRules sourcePath
                |> Option.map (fun fileRules -> fileRules |> List.collect (findInRoot segments))
            | _ -> None

        let hasInject (_, options: Options) = options.inject.IsSome

        let rec injectRule newRule : NewRule =
            let rule, options = newRule

            let injected =
                options.inject
                |> Option.bind resolveInject
                |> Option.defaultValue []

            let injected =
                if injected |> List.exists hasInject then
                    [||]
                else
                    injected |> List.toArray

            let injectChildren children =
                children |> Array.map injectRule |> fun existing -> Array.append existing injected

            match rule with
            | NodeRule(left, children) -> NodeRule(left, injectChildren children), options
            | ValueClauseRule children -> ValueClauseRule(injectChildren children), options
            | SubtypeRule(name, isSubtypeValue, children) ->
                SubtypeRule(name, isSubtypeValue, injectChildren children), options
            | _ -> newRule

        let mapRoot =
            function
            | TypeRule(name, rule) -> TypeRule(name, injectRule rule)
            | AliasRule(name, rule) -> AliasRule(name, injectRule rule)
            | SingleAliasRule(name, rule) -> SingleAliasRule(name, injectRule rule)

        rules |> Array.map mapRoot


    let replaceColourField (rules: RootRule array) =

        let colorLeafRule (colorType: string option) =
            match colorType |> Option.map (fun s -> s.Trim().ToLowerInvariant()) with
            | Some "hex" -> Choice2Of2(ScalarField ScalarValue)
            | Some "rgb" ->
                Choice1Of2(
                    ValueField(ValueType.Float(0.0M, 255.0M)),
                    { defaultOptions with
                        min = 3
                        max = 4 }
                )
            | Some "hsv360" ->
                Choice1Of2(
                    ValueField(ValueType.Float(0.0M, 360.0M)),
                    { defaultOptions with
                        min = 3
                        max = 4 }
                )
            | Some "hsv" ->
                Choice1Of2(
                    ValueField(ValueType.Float(0.0M, 2.0M)),
                    { defaultOptions with
                        min = 3
                        max = 4 }
                )
            | _ ->
                Choice1Of2(
                    ValueField(ValueType.Float(-256.0M, 256.0M)),
                    { defaultOptions with
                        min = 3
                        max = 3 }
                )

        let rec cataRule rule : NewRule array =
            match rule with
            | LeafRule(l, MarkerField(ColourField explicitColorType)), o ->
                match colorLeafRule (explicitColorType |> Option.orElse o.colorType) with
                | Choice1Of2(valueRule, valueOptions) ->
                    [| NodeRule(l, [| LeafValueRule valueRule, valueOptions |]), o |]
                | Choice2Of2 scalarRule -> [| LeafRule(l, scalarRule), o |]
            | LeafRule(l, MarkerField IRCountryTag), o ->
                [| LeafRule(l, ValueField(ValueType.Enum "country_tags")), o
                   LeafRule(l, VariableGetField "dynamic_country_tag"), o |]
            | LeafRule(MarkerField IRCountryTag, r), o ->
                [| LeafRule(ValueField(ValueType.Enum "country_tags"), r), o
                   LeafRule(VariableGetField "dynamic_country_tag", r), o |]
            | NodeRule(MarkerField IRCountryTag, r), o ->
                [| NodeRule(ValueField(ValueType.Enum "country_tags"), r |> Array.collect cataRule), o
                   NodeRule(VariableGetField "dynamic_country_tag", r |> Array.collect cataRule), o |]
            | NodeRule(l, r), o -> [| NodeRule(l, r |> Array.collect cataRule), o |]
            | ValueClauseRule r, o -> [| ValueClauseRule(r |> Array.collect cataRule ), o |]
            | SubtypeRule(a, b, i), o -> [| (SubtypeRule(a, b, (i |> Array.collect cataRule )), o) |]
            | _ -> [| rule |]

        let rulesMapper =
            function
            | TypeRule(name, rule) -> cataRule rule |> Array.map (fun x -> TypeRule(name, x))
            | AliasRule(name, rule) -> cataRule rule |> Array.map (fun x -> AliasRule(name, x))
            | SingleAliasRule(name, rule) -> cataRule rule |> Array.map (fun x -> SingleAliasRule(name, x))

        rules |> Array.collect rulesMapper

    /// stellarisScopeTrigger -> num_moons = owner -> num_moons = owner.trigger:num_moons
    let replaceValueMarkerFields (useFormulas: bool) (stellarisScopeTrigger: bool) (rules: RootRule array) =
        let rec cataRule rule : NewRule array =
            match rule with
            | LeafRule(ValueScopeMarkerField(i, m), ValueScopeMarkerField(i2, m2)), o when useFormulas ->
                [| LeafRule(ValueScopeField(i, m), ValueScopeField(i2, m2)), o
                   LeafRule(ValueScopeField(i, m), SingleAliasField("formula")), o
                   LeafRule(ValueScopeField(i, m), SingleAliasField("range")), o |]
            | LeafRule(ValueScopeMarkerField(i, m), ValueScopeMarkerField(i2, m2)), o when
                o.comparison && stellarisScopeTrigger
                ->
                [| LeafRule(ValueScopeField(i, m), ValueScopeField(i2, m2)), o
                   LeafRule(ValueScopeField(i, m), ScopeField(o.requiredScopes)), o |]
            | LeafRule(ValueScopeMarkerField(i, m), ValueScopeMarkerField(i2, m2)), o ->
                [| LeafRule(ValueScopeField(i, m), ValueScopeField(i2, m2)), o |]
            | LeafRule(l, ValueScopeMarkerField(i2, m2)), o when useFormulas ->
                [| LeafRule(l, ValueScopeField(i2, m2)), o
                   LeafRule(l, SingleAliasField("formula")), o
                   LeafRule(l, SingleAliasField("range")), o |]
            | LeafRule(l, ValueScopeMarkerField(i2, m2)), o when o.comparison && stellarisScopeTrigger ->
                [| LeafRule(l, ValueScopeField(i2, m2)), o
                   LeafRule(l, ScopeField(o.requiredScopes)), o |]
            | LeafRule(l, ValueScopeMarkerField(i2, m2)), o -> [| LeafRule(l, ValueScopeField(i2, m2)), o |]
            | LeafRule(ValueScopeMarkerField(i, m), r), o -> [| LeafRule(ValueScopeField(i, m), r), o |]
            | NodeRule(ValueScopeMarkerField(i, m), r), o ->
                [| NodeRule(ValueScopeField(i, m), r |> Array.collect cataRule), o |]
            | NodeRule(l, r), o -> [| NodeRule(l, r |> Array.collect cataRule), o |]
            | ValueClauseRule r, o -> [| ValueClauseRule(r |> Array.collect cataRule ), o |]
            | SubtypeRule(a, b, i), o -> [| (SubtypeRule(a, b, (i |> Seq.collect cataRule |> Seq.toArray)), o) |]
            | _ -> [| rule |]

        let rulesMapper =
            function
            | TypeRule(name, rule) -> cataRule rule |> Array.map (fun x -> TypeRule(name, x))
            | AliasRule(name, rule) -> cataRule rule |> Array.map (fun x -> AliasRule(name, x))
            | SingleAliasRule(name, rule) -> cataRule rule |> Array.map (fun x -> SingleAliasRule(name, x))

        rules |> Array.collect rulesMapper

    let replaceIgnoreMarkerFields (rules: RootRule array) =
        let rec cataRule rule : NewRule array =
            match rule with
            | LeafRule(field, IgnoreMarkerField), o -> [| NodeRule(IgnoreField field, [||]), o |]
            | NodeRule(l, r), o -> [| NodeRule(l, r |> Array.collect cataRule), o |]
            | ValueClauseRule r, o -> [| ValueClauseRule(r |> Array.collect cataRule), o |]
            | SubtypeRule(a, b, i), o -> [| (SubtypeRule(a, b, (i |> Array.collect cataRule)), o) |]
            | _ -> [| rule |]

        let rulesMapper =
            function
            | TypeRule(name, rule) -> cataRule rule |> Array.map (fun x -> TypeRule(name, x))
            | AliasRule(name, rule) -> cataRule rule |> Array.map (fun x -> AliasRule(name, x))
            | SingleAliasRule(name, rule) -> cataRule rule |> Array.map (fun x -> SingleAliasRule(name, x))

        rules |> Array.collect rulesMapper

    let private commentText (comment: string) =
        comment.Trim().TrimStart('#').Trim()

    let private descriptionFromComments (comments: string list) =
        comments
        |> List.choose (fun c ->
            let t = c.Trim()
            if t.StartsWith("#") && not (t.Contains "=") then
                let cleaned = commentText t
                if cleaned = "" then None else Some cleaned
            else
                None)
        |> function
            | [] -> None
            | xs -> Some(String.concat Environment.NewLine xs)

    let private optionFromComments (name: string) (comments: string list) =
        comments
        |> List.tryPick (fun c ->
            let t = c.Trim()
            if t.StartsWith("#") && t.Contains("=") then
                let body = commentText t
                let split = body.Split('=', 2)
                if split.Length = 2 && split.[0].Trim().Equals(name, StringComparison.OrdinalIgnoreCase) then
                    Some(split.[1].Trim().Trim('"'))
                else
                    None
            else
                None)

    let private boolOption text =
        match text with
        | "" -> None
        | x when x.Equals("yes", StringComparison.OrdinalIgnoreCase)
              || x.Equals("true", StringComparison.OrdinalIgnoreCase) -> Some true
        | x when x.Equals("no", StringComparison.OrdinalIgnoreCase)
              || x.Equals("false", StringComparison.OrdinalIgnoreCase) -> Some false
        | _ -> None

    let private parseExtendedMetadata parseScope (root: Node) =
        let parsePriority (leaf: Leaf) =
            let path = leaf.Key.Replace("\\", "/")
            path,
            { path = path
              strategy = leaf.ValueText }

        let parseSystemScope comments (node: Node) =
            node.Key,
            { id = node.Key
              baseId =
                let text = node.TagText "base_id"
                if String.IsNullOrWhiteSpace text then None else Some text
              name =
                let text = node.TagText "name"
                if String.IsNullOrWhiteSpace text then None else Some text
              description = descriptionFromComments comments }

        let parseOverrideModeInfo comments (node: Node) =
            node.Key,
            { id = node.Key
              name =
                let text = node.TagText "name"
                if String.IsNullOrWhiteSpace text then None else Some text
              description = descriptionFromComments comments }

        let parseLocale comments (node: Node) =
            let codes =
                node.Child "codes"
                |> Option.map (fun c -> c.LeafValues |> Seq.map _.ValueText |> Seq.toArray)
                |> Option.defaultValue [||]

            node.Key,
            { id = node.Key
              codes = codes
              supports = boolOption (node.TagText "supports")
              description = descriptionFromComments comments }

        let parseDatabaseObjectType (node: Node) =
            let optionalTag key =
                let text = node.TagText key
                if String.IsNullOrWhiteSpace text then None else Some text

            match optionalTag "type", optionalTag "localisation" with
            | None, None -> None
            | objectType, localisationPrefix ->
                Some(
                    node.Key,
                    { name = node.Key
                      objectType = objectType
                      swapType = optionalTag "swap_type"
                      localisationPrefix = localisationPrefix }
                )

        let parseOnAction comments name =
            match optionFromComments "event_type" comments with
            | Some eventType when not (String.IsNullOrWhiteSpace eventType) ->
                Some(
                    name,
                    { name = name
                      eventType = eventType
                      hint = optionFromComments "hint" comments
                      replaceScopes = replaceScopes parseScope comments
                      description = descriptionFromComments comments }
                )
            | _ -> None

        let childComments (node: Node) = getNodeComments node

        let directComments (node: Node) =
            node.AllArray
            |> Array.choose (function
                | CommentC comment when comment.Comment.StartsWith("#") -> Some comment.Comment
                | _ -> None)
            |> List.ofArray

        let priorities =
            root.Child "priorities"
            |> Option.map (fun n -> n.Leaves |> Seq.map parsePriority |> Map.ofSeq)
            |> Option.defaultValue Map.empty

        let overrideModesInfo =
            root.Child "override_modes_info"
            |> Option.map (fun n ->
                childComments n
                |> Seq.choose (function
                    | NodeC child, comments -> Some(parseOverrideModeInfo (comments @ directComments child) child)
                    | _ -> None)
                |> Map.ofSeq)
            |> Option.defaultValue Map.empty

        let systemScopes =
            root.Child "system_scopes"
            |> Option.map (fun n ->
                childComments n
                |> Seq.choose (function
                    | NodeC child, comments -> Some(parseSystemScope comments child)
                    | _ -> None)
                |> Map.ofSeq)
            |> Option.defaultValue Map.empty

        let locales =
            root.Child "locales"
            |> Option.map (fun n ->
                childComments n
                |> Seq.choose (function
                    | NodeC child, comments -> Some(parseLocale comments child)
                    | _ -> None)
                |> Map.ofSeq)
            |> Option.defaultValue Map.empty

        let databaseObjectTypes =
            root.Child "database_object_types"
            |> Option.map (fun n ->
                n.Children
                |> Seq.choose parseDatabaseObjectType
                |> Map.ofSeq)
            |> Option.defaultValue Map.empty

        let onActions =
            root.Child "on_actions"
            |> Option.map (fun n ->
                childComments n
                |> Seq.choose (function
                    | NodeC child, comments -> parseOnAction (comments @ directComments child) child.Key
                    | LeafC leaf, comments -> parseOnAction comments leaf.Key
                    | LeafValueC leafValue, comments -> parseOnAction comments leafValue.ValueText
                    | _ -> None)
                |> Map.ofSeq)
            |> Option.defaultValue Map.empty

        { priorities = priorities
          overrideModesInfo = overrideModesInfo
          systemScopes = systemScopes
          locales = locales
          databaseObjectTypes = databaseObjectTypes
          onActions = onActions }

    let processConfig parseScope allScopes anyScope scopeGroup (node: Node) =
        let nodes = getNodeComments node

        let rules =
            nodes
            |> List.choose (processChildConfigRoot parseScope allScopes anyScope scopeGroup)

        let types =
            nodes
            |> List.choose (processChildType parseScope allScopes anyScope scopeGroup)
            |> List.collect id

        let enums = nodes |> List.choose processChildEnum |> List.collect id
        let complexenums = nodes |> List.choose processComplexChildEnum |> List.collect id
        let values = nodes |> List.choose processChildValue |> List.collect id
        let metadata = parseExtendedMetadata parseScope node
        rules, types, enums, complexenums, values, metadata

module RulesConsistencyValidation =
    let rec cataRule (f: 'a list -> RuleType -> 'a list) (oldState) (rule: RuleType) : 'a list =
        let newState = f oldState rule
        let recurse = cataRule f

        match rule with
        | SubtypeRule(_, _, rules)
        | NodeRule(_, rules)
        | ValueClauseRule rules -> rules |> Seq.map fst |> Seq.fold recurse newState
        | LeafValueRule _
        | LeafRule _ -> newState

    let getAllTypesReferenceInRules (acc: string list) (rule: RuleType) =
        match rule with
        | NodeRule(TypeField(TypeType.Simple(name = name)), _)
        | NodeRule(TypeField(TypeType.Complex(name = name)), _)
        | LeafRule(TypeField(TypeType.Simple(name = name)), _)
        | LeafRule(TypeField(TypeType.Complex(name = name)), _)
        | LeafRule(_, TypeField(TypeType.Simple(name = name)))
        | LeafRule(_, TypeField(TypeType.Complex(name = name)))
        | LeafValueRule(TypeField(TypeType.Simple(name = name)))
        | LeafValueRule(TypeField(TypeType.Complex(name = name)))
        | LeafRule(PrefixedField(TypeField(TypeType.Simple(name = name))), _)
        | LeafRule(PrefixedField(TypeField(TypeType.Complex(name = name))), _)
        | LeafRule(_, PrefixedField(TypeField(TypeType.Simple(name = name))))
        | LeafRule(_, PrefixedField(TypeField(TypeType.Complex(name = name))))
        | LeafValueRule(PrefixedField(TypeField(TypeType.Simple(name = name))))
        | LeafValueRule(PrefixedField(TypeField(TypeType.Complex(name = name)))) -> name :: acc
        | _ -> acc

    let checkForUndefinedTypes (rules: RootRule seq) (typedefs: TypeDefinition list) =
        let referencedTypes =
            rules
            |> Seq.collect (function
                | TypeRule(_, (rule, _))
                | AliasRule(_, (rule, _))
                | SingleAliasRule(_, (rule, _)) -> cataRule getAllTypesReferenceInRules [] rule)
            |> Seq.distinct

        let missing =
            referencedTypes
            |> Seq.choose (fun t ->
                match t.Split('.') with
                | [| key |] when typedefs |> List.exists (fun x -> x.name = key) |> not -> Some key
                | [| key; subtype |] when
                    typedefs
                    |> List.exists (fun x -> x.name = key && x.subtypes |> List.exists (fun st -> st.name = subtype))
                    |> not
                    ->
                    Some(key + "." + subtype)
                | _ -> None)
            |> Array.ofSeq

        if missing |> Array.isEmpty |> not then
            logWarning $"The following types were referenced in rules but not defined in rules %A{missing}"


module RulesParser =
    open RulesParserImpl
    let defaultOptions = defaultOptions
    let specificField = specificFieldFromString
    let specificFieldFromId = specificFieldFromId
    let internal getSettingFromString = getSettingFromString
    let processTagAsField = processKey
    let requiredSingle: Options = { defaultOptions with min = 1; max = 1 }

    let requiredMany =
        { defaultOptions with
            min = 1
            max = 100 }

    let optionalSingle: Options = { defaultOptions with min = 0; max = 1 }

    let optionalMany: Options =
        { defaultOptions with
            min = 0
            max = 100 }

    let defaultFloat =
        ValueField(
            ValueType.Float(
                RulesParserConstants.floatFieldDefaultMinimum,
                RulesParserConstants.floatFieldDefaultMaximum
            )
        )

    let defaultInt =
        ValueField(
            ValueType.Int(RulesParserConstants.IntFieldDefaultMinimum, RulesParserConstants.IntFieldDefaultMaximum)
        )

    let parseConfigWithMetadata parseScope allScopes anyScope scopeGroup filename fileString =
        //log "parse"
        let parsed = CKParser.parseString fileString filename

        match parsed with
        | Failure(e, _, _) ->
            log $"config file %s{filename} failed with %s{e}"
            ([], [], [], [], [], ExtendedConfigMetadata.empty)
        | Success(s, _, _) ->
            //log "parsed %A" s
            let root = simpleProcess.ProcessNode () "root" (mkZeroFile filename) s
            //log "processConfig"
            processConfig parseScope allScopes anyScope scopeGroup root

    let parseConfig parseScope allScopes anyScope scopeGroup filename fileString =
        let rules, types, enums, complexenums, values, _ =
            parseConfigWithMetadata parseScope allScopes anyScope scopeGroup filename fileString

        let rules =
            rules
            |> Array.ofList
            |> applyConfigInjections [ filename, rules ]
            |> Array.toList

        rules, types, enums, complexenums, values

    let parseConfigs
        parseScope
        allScopes
        anyScope
        scopeGroup
        useFormulas
        stellarisScopeTriggers
        (files: (string * string) list)
        =
        let parsedFiles =
            files
            |> Seq.map (fun (filename, fileString) ->
                filename, parseConfigWithMetadata parseScope allScopes anyScope scopeGroup filename fileString)
            |> Seq.toList

        let rules, types, enums, complexenums, values, metadata =
            parsedFiles
            |> Seq.fold
                (fun (rs, ts, es, ces, vs, md) (_, (r, t, e, ce, v, fileMd)) ->
                    r @ rs, t @ ts, e @ es, ce @ ces, v @ vs, ExtendedConfigMetadata.merge md fileMd)
                ([], [], [], [], [], ExtendedConfigMetadata.empty)

        let sourceRulesByFile =
            parsedFiles
            |> List.map (fun (filename, (fileRules, _, _, _, _, _)) -> filename, fileRules)

        let rules =
            rules
            |> Array.ofList
            |> applyConfigInjections sourceRulesByFile
            |> replaceValueMarkerFields useFormulas stellarisScopeTriggers
            |> replaceSingleAliases
            |> replaceColourField
            |> replaceIgnoreMarkerFields
        // File.AppendAllText ("test.test", sprintf "%O" rules)
        rules, types, enums, complexenums, values, metadata
