namespace CWTools.CwtLanguage

/// Support tags for CWT constructs (mirrors docs/cwt-rule-config.md).
/// Shared works in every profile; Legacy/Jomini are profile families;
/// Advanced needs care; GameSpecific depends on game data.
type CwtSupport =
    | Shared
    | Legacy
    | Jomini
    | Advanced
    | GameSpecific

type CwtRootBlock =
    { name: string
      description: string
      support: CwtSupport }

type CwtDirective =
    { name: string
      /// One of: none | text | cardinality | severity | scope | scope-map |
      /// list | inject | type. Validated by CwtLanguageService.
      valueKind: string
      description: string
      support: CwtSupport }

type CwtFieldExpression =
    { pattern: string
      description: string
      support: CwtSupport }

/// Versioned CWT meta-model. The version is bumped only when the tables
/// change shape in a way consumers must react to; it never mirrors the
/// product version (handoff doc §4.3).
type CwtMetaSchema =
    { version: int
      rootBlocks: CwtRootBlock list
      directives: CwtDirective list
      fieldExpressions: CwtFieldExpression list }

module CwtMetaSchema =

    /// Explicit schema version; bump on breaking table changes only.
    let schemaVersion = 1

    /// Known root blocks. Unknown root keys are NOT errors: CWT root blocks
    /// are extensible rule containers (the parser treats any top-level key
    /// as a rule block). The table drives completion and hover only.
    let rootBlocks: CwtRootBlock list =
        [ { name = "types"; description = "Type definitions with subtypes and localisation rules."; support = Shared }
          { name = "enums"; description = "Static and complex enum definitions."; support = Shared }
          { name = "complex_enums"; description = "Complex enum definitions with root/suffix patterns."; support = Shared }
          { name = "values"; description = "Named value definitions."; support = Shared }
          { name = "aliases"; description = "Trigger/effect/field alias definitions."; support = Shared }
          { name = "scopes"; description = "Scope names, aliases and inheritance."; support = Shared }
          { name = "scope_groups"; description = "Named reusable scope sets."; support = Shared }
          { name = "links"; description = "Scope and value link definitions."; support = Shared }
          { name = "modifier_categories"; description = "Modifier category scope support."; support = Shared }
          { name = "localisation_commands"; description = "Legacy localisation command rules."; support = Legacy }
          { name = "localisation_links"; description = "Legacy localisation link rules."; support = Legacy }
          { name = "priorities"; description = "File override strategy metadata (LIOS/FIOS/...)."; support = Jomini }
          { name = "override_modes_info"; description = "Legend for override strategies."; support = Jomini }
          { name = "system_scopes"; description = "Metadata for This/Root/Prev/From system scopes."; support = Jomini }
          { name = "locales"; description = "Locale ids and language codes."; support = Jomini }
          { name = "database_object_types"; description = "Metadata for $database_object references."; support = Jomini }
          { name = "on_actions"; description = "on_action event type hints and scope replacements."; support = Jomini } ]

    /// `##` rule options attached to the following rule. `## required` and
    /// similar boolean options appear without a value.
    let directives: CwtDirective list =
        [ { name = "cardinality"; valueKind = "cardinality"; description = "Allowed count, e.g. 0..100; inf means unbounded. Default 1..1."; support = Shared }
          { name = "severity"; valueKind = "severity"; description = "Override diagnostic severity (error/warning/info/hint)."; support = Shared }
          { name = "scope"; valueKind = "scope"; description = "Restrict the input scope in which a rule is valid."; support = Shared }
          { name = "push_scope"; valueKind = "scope"; description = "Enter a new this scope when matching a block."; support = Shared }
          { name = "replace_scope"; valueKind = "scope"; description = "Replace one system scope inside the nested rule."; support = Shared }
          { name = "replace_scopes"; valueKind = "scope-map"; description = "Replace system scopes, e.g. { this = country root = country }."; support = Shared }
          { name = "completion_type"; valueKind = "type"; description = "Use completions from a specific type."; support = Shared }
          { name = "error_if_only_match"; valueKind = "text"; description = "Report a custom error when only this rule matches."; support = Shared }
          { name = "type_prefix_from"; valueKind = "text"; description = "Derive type prefix context from another field."; support = Advanced }
          { name = "type_suffix_patterns"; valueKind = "list"; description = "Suffix-derived type completion candidates, e.g. { _desc _tooltip }."; support = Shared }
          { name = "type_suffix_pattern"; valueKind = "text"; description = "Single suffix-derived type completion pattern."; support = Shared }
          { name = "file_extensions"; valueKind = "list"; description = "Restrict file completion extensions, e.g. { dds png }."; support = Shared }
          { name = "color_type"; valueKind = "text"; description = "Adjust generated colour_field rules, e.g. hsv360."; support = Shared }
          { name = "inject"; valueKind = "inject"; description = "Inject child rules from another rule file, e.g. common/foo.cwt@type/path."; support = Advanced }
          { name = "incomingReferenceLabel"; valueKind = "text"; description = "Label incoming reference relationships."; support = Advanced }
          { name = "outgoingReferenceLabel"; valueKind = "text"; description = "Label outgoing reference relationships."; support = Advanced }
          { name = "required"; valueKind = "none"; description = "Mark a rule as required (legacy option used by type localisation rules)."; support = Advanced }
          { name = "optional"; valueKind = "none"; description = "Mark a rule as optional (legacy option used by type localisation rules)."; support = Advanced }
          { name = "primary"; valueKind = "none"; description = "Mark the primary localisation field for a type."; support = Shared }
          { name = "type_key_filter"; valueKind = "text"; description = "Restrict type-key matching, e.g. type_key_filter = part."; support = Advanced }
          { name = "type_key_regex"; valueKind = "text"; description = "Restrict type keys with a regular expression."; support = Advanced }
          { name = "display_name"; valueKind = "text"; description = "Display name used in completion/hover."; support = Shared }
          { name = "abbreviation"; valueKind = "text"; description = "Short subtype label used in displays."; support = Shared }
          { name = "starts_with"; valueKind = "text"; description = "Require a key prefix when discovering definitions."; support = Shared }
          { name = "root_completion"; valueKind = "text"; description = "Choose the source for root completion, e.g. subtypes."; support = Shared }
          { name = "graph_related_types"; valueKind = "list"; description = "Types related in dependency graph views."; support = Shared }
          { name = "supported_scopes"; valueKind = "text"; description = "Scopes supported by an alias or modifier rule."; support = Shared }
          { name = "event_type"; valueKind = "text"; description = "Event type hint for on_action metadata."; support = Jomini }
          { name = "hint"; valueKind = "text"; description = "Short hint text for metadata blocks."; support = Jomini } ]

    /// Field expression families (docs/cwt-rule-config.md §field-expression).
    /// `pattern` is matched against a token; bracketed forms carry arguments
    /// validated by CwtLanguageService.
    let fieldExpressions: CwtFieldExpression list =
        [ { pattern = "scalar"; description = "Any single scalar value."; support = Shared }
          { pattern = "wildcard_scalar"; description = "Scalar that also matches quoted values."; support = Shared }
          { pattern = "$any"; description = "Any value, including blocks."; support = Shared }
          { pattern = "bool"; description = "yes/no boolean."; support = Shared }
          { pattern = "int"; description = "Integer, optionally int[min..max] or int[min..inf]."; support = Shared }
          { pattern = "float"; description = "Floating point, optionally float[min..max]."; support = Shared }
          { pattern = "date_field"; description = "Paradox date value."; support = Shared }
          { pattern = "datetime_field"; description = "Date and time value."; support = Shared }
          { pattern = "percentage_field"; description = "Percentage value."; support = Shared }
          { pattern = "localisation"; description = "Localisation key."; support = Shared }
          { pattern = "localisation_synced"; description = "Synced/default-language localisation key."; support = Shared }
          { pattern = "localisation_inline"; description = "Inline localisation text or key."; support = Shared }
          { pattern = "enum[x]"; description = "Value from enum x."; support = Shared }
          { pattern = "complex_enum[x]"; description = "Value from complex enum x."; support = Shared }
          { pattern = "value[x]"; description = "Defined variable value."; support = Shared }
          { pattern = "value_set[x]"; description = "Value from a value set."; support = Shared }
          { pattern = "dynamic_value[x]"; description = "Dynamically expanded value."; support = Shared }
          { pattern = "value_field"; description = "Defined variable or number."; support = Shared }
          { pattern = "value_field[x]"; description = "Defined variable or number with bounds."; support = Shared }
          { pattern = "int_value_field"; description = "Defined variable or integer."; support = Shared }
          { pattern = "int_value_field[x]"; description = "Defined variable or integer with bounds."; support = Shared }
          { pattern = "variable_field"; description = "Script variable reference."; support = Shared }
          { pattern = "variable_field[x]"; description = "Script variable reference with bounds."; support = Shared }
          { pattern = "int_variable_field"; description = "Integer script variable reference."; support = Shared }
          { pattern = "int_variable_field[x]"; description = "Integer script variable reference with bounds."; support = Shared }
          { pattern = "variable_field_32"; description = "32-bit script variable reference."; support = Shared }
          { pattern = "variable_field_32[x]"; description = "32-bit script variable reference with bounds."; support = Shared }
          { pattern = "int_variable_field_32"; description = "32-bit integer script variable reference."; support = Shared }
          { pattern = "int_variable_field_32[x]"; description = "32-bit integer script variable reference with bounds."; support = Shared }
          { pattern = "<type>"; description = "Reference to a defined type."; support = Shared }
          { pattern = "prefix<type>suffix"; description = "Type reference with prefix/suffix literals."; support = Shared }
          { pattern = "prefix_field[x]"; description = "Prefixed value reference, e.g. prefix_field[localisation]."; support = Shared }
          { pattern = "alias_name[x]"; description = "Name of an alias."; support = Shared }
          { pattern = "alias_match_left[x]"; description = "Left side of an alias."; support = Shared }
          { pattern = "single_alias_right[x]"; description = "Right side of a single alias."; support = Shared }
          { pattern = "alias_keys_field[x]"; description = "Keys of an alias."; support = Shared }
          { pattern = "alias_params_field[x]"; description = "Parameters of an alias."; support = Shared }
          { pattern = "scope[x]"; description = "A scope name."; support = Shared }
          { pattern = "scope_field"; description = "Any scope."; support = Shared }
          { pattern = "scope_group[x]"; description = "A scope from a named group."; support = Shared }
          { pattern = "event_target[x]"; description = "Event target of a scope."; support = Shared }
          { pattern = "colour_field"; description = "Colour value (rgb/hsv/hex variants)."; support = Shared }
          { pattern = "color_field"; description = "US spelling of colour_field."; support = Shared }
          { pattern = "colour[x]"; description = "Colour with format arguments."; support = Shared }
          { pattern = "color[x]"; description = "US spelling of colour[x]."; support = Shared }
          { pattern = "filepath[x]"; description = "Path under a resource folder."; support = Shared }
          { pattern = "filename[x]"; description = "File name with a given extension."; support = Shared }
          { pattern = "abs_filepath"; description = "Absolute path."; support = Shared }
          { pattern = "icon[x]"; description = "Icon reference by resource folder."; support = Shared }
          { pattern = "$localisation_parameter"; description = "Localisation parameter placeholder."; support = Shared }
          { pattern = "$script_value_reference"; description = "Script value reference."; support = Shared }
          { pattern = "$define_reference"; description = "Define reference."; support = Shared }
          { pattern = "$array_define_reference"; description = "Array define reference."; support = Shared }
          { pattern = "$database_object"; description = "Database object reference."; support = Jomini }
          { pattern = "$tags[x]"; description = "Tag set membership."; support = Jomini }
          { pattern = "$tags_condition[x]"; description = "Tag set condition."; support = Jomini }
          { pattern = "$shader_effect"; description = "Shader effect reference."; support = GameSpecific }
          { pattern = "$mesh_locator"; description = "Mesh locator reference."; support = GameSpecific }
          { pattern = "$technology_with_level"; description = "Technology with level."; support = GameSpecific }
          { pattern = "name_format[x]"; description = "Name-format expression."; support = GameSpecific }
          { pattern = "stellaris_name_format[x]"; description = "Stellaris name-format expression."; support = GameSpecific }
          { pattern = "portrait_dna_field"; description = "Crusader Kings II portrait DNA."; support = GameSpecific }
          { pattern = "portrait_properties_field"; description = "Crusader Kings II portrait properties."; support = GameSpecific }
          { pattern = "ir_country_tag_field"; description = "Imperator country tag."; support = GameSpecific }
          { pattern = "ir_family_name_field"; description = "Imperator family name."; support = GameSpecific }
          { pattern = "glob:pattern"; description = "Glob pattern."; support = Shared }
          { pattern = "glob.i:pattern"; description = "Case-insensitive glob pattern."; support = Shared }
          { pattern = "ant:pattern"; description = "Ant-style pattern."; support = Shared }
          { pattern = "ant.i:pattern"; description = "Case-insensitive ant pattern."; support = Shared }
          { pattern = "re:pattern"; description = "Regular expression."; support = Shared }
          { pattern = "re.i:pattern"; description = "Case-insensitive regular expression."; support = Shared }
          { pattern = "ignore_field"; description = "Skip matching for this field."; support = Advanced } ]

    /// Stable singleton.
    let schema: CwtMetaSchema =
        { version = schemaVersion
          rootBlocks = rootBlocks
          directives = directives
          fieldExpressions = fieldExpressions }

    /// Directive lookup by name (case-insensitive).
    let tryDirective (name: string) =
        directives
        |> List.tryFind (fun d -> d.name.Equals(name, System.StringComparison.OrdinalIgnoreCase))

    /// Field expression entry whose pattern exactly matches a token.
    let tryFieldExpression (token: string) =
        fieldExpressions
        |> List.tryFind (fun f -> f.pattern.Equals(token, System.StringComparison.OrdinalIgnoreCase))
