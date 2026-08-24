use cwtools_rule_ir::{SubtypeDefinition, TypeDefinition, parse_document};
use cwtools_rules_engine::{
    CompileError, DynamicTypeReference, MAX_DEPTH, QueryError, RuleCatalog, ScopeUniverse,
    ValidationOutcome, diagnostic_message_key,
};

fn catalog(source: &str) -> RuleCatalog {
    let document = parse_document("integration.cwt", source).expect("valid rule fixture");
    RuleCatalog::compile(
        &[document],
        ScopeUniverse::new([
            "country".into(),
            "planet".into(),
            "ship".into(),
            "fleet".into(),
            "system".into(),
            "moon".into(),
        ]),
    )
    .expect("catalog compiles")
}
#[test]
fn typed_references_follow_nested_rule_context() {
    let c =
        catalog("root = { target = <event> nested = { other = <technology> scalar = scalar } }");
    let refs = c
        .typed_references(
            "root",
            "target = event_a nested = { other = tech_a scalar = event_a } unrelated = event_a",
            10,
        )
        .unwrap();
    assert_eq!(
        refs.iter()
            .map(|reference| (reference.type_name.as_str(), reference.value.as_str()))
            .collect::<Vec<_>>(),
        [("event", "event_a"), ("technology", "tech_a")]
    );
}

#[test]
fn typed_references_strip_complex_type_affixes() {
    let c = catalog("root = { target = pre<event>suf }");
    let refs = c
        .typed_references("root", "target = preevent_asuf", 10)
        .unwrap();
    assert_eq!(refs.len(), 1);
    assert_eq!(refs[0].type_name, "event");
    assert_eq!(refs[0].value, "event_a");
    assert!(refs[0].is_outgoing);
    assert_eq!(refs[0].reference_label, None);
    assert!(refs[0].fuzzy);
    assert!(
        c.typed_references("root", "target = wrong", 10)
            .unwrap()
            .is_empty()
    );
}

#[test]
fn typed_references_follow_type_rule_on_left() {
    let c = catalog("root = { <event> = scalar }");
    let refs = c.typed_references("root", "event_a = yes", 10).unwrap();
    assert_eq!(refs[0].type_name, "event");
    assert_eq!(refs[0].value, "event_a");
}

#[test]
fn value_scope_references_use_caller_resolver_and_trim_pipe_suffix() {
    let c = catalog("root = { amount = value_field }");
    let mut calls = Vec::new();
    let refs = c
        .typed_references_with(
            "root",
            "amount = scripted_value|fallback",
            10,
            |value, _scope| {
                calls.push(value.to_owned());
                (value == "scripted_value").then(|| DynamicTypeReference {
                    type_name: "script_value".into(),
                    value: "resolved_value".into(),
                })
            },
        )
        .unwrap();
    assert_eq!(calls, ["scripted_value"]);
    assert_eq!(refs[0].type_name, "script_value");
    assert_eq!(refs[0].value, "resolved_value");
    assert_eq!(refs[0].associated_type, None);
    assert!(
        c.typed_references("root", "amount = scripted_value", 10)
            .unwrap()
            .is_empty()
    );
}

#[test]
fn value_scope_reference_resolver_is_bounded() {
    let c = catalog("root = { amount = value_field other = value_field }");
    assert_eq!(
        c.typed_references_with("root", "amount = one other = two", 1, |value, _scope| Some(
            DynamicTypeReference {
                type_name: "script_value".into(),
                value: value.into(),
            }
        ),),
        Err(QueryError::TooManyResults)
    );
}

#[test]
fn typed_references_preserve_incoming_reference_label() {
    let c = catalog("root = { ## incomingReferenceLabel = source\n target = <event> }");
    let refs = c.typed_references("root", "target = event_a", 10).unwrap();
    assert!(!refs[0].is_outgoing);
    assert_eq!(refs[0].reference_label.as_deref(), Some("source"));
    assert!(!refs[0].fuzzy);
}

#[test]
fn typed_references_are_bounded_and_reject_malformed_source() {
    let c = catalog("root = { target = <event> }");
    assert_eq!(
        c.typed_references("root", "target = event_a", 0),
        Err(QueryError::TooManyResults)
    );
    assert_eq!(
        c.typed_references("root", "target = {", 10),
        Err(QueryError::ParseFailed)
    );
}

#[test]
fn computed_data_uses_variable_set_rules_and_active_nested_context() {
    let c = catalog(
        "root = { variable = value_set[variable] nested = { flag = value_set[country_flag] scalar = scalar } }",
    );
    let data = c
        .computed_data(
            "root",
            "variable = scope@foo.bar?x nested = { flag = active scalar = ignored } unknown = nope",
            10,
        )
        .unwrap();
    assert_eq!(
        data.variable_sets
            .iter()
            .map(|item| (item.kind.as_str(), item.value.as_str()))
            .collect::<Vec<_>>(),
        [("variable", "scope@foo.bar?x"), ("country_flag", "active")]
    );
}

#[test]
fn computed_data_extracts_variable_set_from_leaf_key() {
    let c = catalog("root = { value_set[event_target] = scalar }");
    let data = c.computed_data("root", "target_a = yes", 10).unwrap();
    assert_eq!(data.variable_sets[0].kind, "event_target");
    assert_eq!(data.variable_sets[0].value, "target_a");
}

#[test]
fn computed_data_extracts_variable_set_from_node_key_and_children() {
    let c = catalog("root = { value_set[global_event_target] = { child = value_set[flag] } }");
    let data = c
        .computed_data("root", "target_a = { child = inner }", 10)
        .unwrap();
    assert_eq!(
        data.variable_sets
            .iter()
            .map(|item| (item.kind.as_str(), item.value.as_str()))
            .collect::<Vec<_>>(),
        [("global_event_target", "target_a"), ("flag", "inner")]
    );
}

#[test]
fn computed_data_tracks_current_scope_for_saved_targets() {
    let c =
        catalog("root = { ## push_scope = country\n nested = { save = value_set[event_target] } }");
    let data = c
        .computed_data("root", "nested = { save = target_a }", 10)
        .unwrap();
    assert_eq!(data.variable_sets[0].scope.as_deref(), Some("country"));
}

#[test]
fn computed_data_marks_alias_blocks_and_enforces_bound() {
    let c = catalog(
        "alias[effect:do_effect] = scalar alias[trigger:has_flag] = scalar root = { effects = { alias[effect] = scalar } triggers = { alias[trigger] = scalar } }",
    );
    let source = "effects = { do_effect = yes } triggers = { has_flag = yes }";
    let data = c.computed_data("root", source, 2).unwrap();
    assert_eq!(data.effect_blocks.len(), 1);
    assert_eq!(data.trigger_blocks.len(), 1);
    assert_eq!(
        c.computed_data("root", source, 1),
        Err(QueryError::TooManyResults)
    );
}

#[test]
fn computed_data_rejects_malformed_source() {
    let c = catalog("root = { variable = value_set[variable] }");
    assert_eq!(
        c.computed_data("root", "variable = {", 10),
        Err(QueryError::ParseFailed)
    );
}

fn subtype(name: &str, rules: &str) -> SubtypeDefinition {
    let document = parse_document(
        "subtype.cwt",
        &format!("types = {{ type[test] = {{ subtype[{name}] = {{ {rules} }} }} }}"),
    )
    .unwrap();
    document.types[0].subtypes[0].clone()
}

#[test]
fn type_subtype_applicator_uses_full_validation_and_missing_rules_are_valid() {
    let c = catalog("root = scalar");
    let mut definition = TypeDefinition {
        name: "test".into(),
        ..TypeDefinition::default()
    };
    definition.subtypes = vec![
        subtype(
            "valid",
            "required = scalar ## cardinality = 0..1\n optional = scalar",
        ),
        subtype("invalid_value", "required = bool"),
        subtype("invalid_shape", "required = { nested = scalar }"),
    ];
    let matched = c
        .apply_type_subtypes(&definition, "entry", "required = maybe")
        .unwrap();
    assert_eq!(matched.names, ["valid"]);
}

#[test]
fn type_subtype_applicator_applies_selectors_only_if_not_and_scope() {
    let c = catalog("root = scalar");
    let mut primary = subtype("primary", "marker = scalar");
    primary.type_key_field = Some("Country_Event".into());
    primary.push_scope = Some("country".into());
    let mut regex = subtype("regex", "marker = scalar");
    regex.type_key_regex = Some("^country_.*$".into());
    regex.only_if_not = vec!["PRIMARY".into()];
    let mut invalid_regex = subtype("invalid_regex", "marker = scalar");
    invalid_regex.type_key_regex = Some("[".into());
    let mut definition = TypeDefinition {
        name: "test".into(),
        ..TypeDefinition::default()
    };
    definition.subtypes = vec![primary, regex, invalid_regex];
    let matched = c
        .apply_type_subtypes(&definition, "country_event", "marker = yes")
        .unwrap();
    assert_eq!(matched.names, ["primary"]);
    assert_eq!(
        matched.scope,
        Some(cwtools_rules_engine::SubtypeScopeTransition::Push(
            "country".into()
        ))
    );
}

#[test]
fn type_subtype_applicator_rejects_malformed_source() {
    let c = catalog("root = scalar");
    assert_eq!(
        c.apply_type_subtypes(&TypeDefinition::default(), "entry", "broken = {"),
        Err(QueryError::ParseFailed)
    );
}

fn codes(c: &RuleCatalog, root: &str, source: &str) -> Vec<String> {
    c.validate_source(root, source)
        .diagnostics
        .into_iter()
        .map(|d| d.code)
        .collect()
}
fn has(c: &RuleCatalog, root: &str, source: &str, code: &str) -> bool {
    codes(c, root, source).iter().any(|x| x == code)
}

#[test]
fn compile_ordinary_root() {
    assert!(!codes(&catalog("root = { value = scalar }"), "root", "value = x").len() > 0);
}
#[test]
fn compile_alias_root() {
    let c = catalog("alias[root_alias] = { value = scalar }");
    assert!(!c.completion("root_alias", "").is_empty());
}
#[test]
fn compile_single_alias_root() {
    let c = catalog("single_alias[root_one] = scalar");
    assert!(codes(&c, "root_one", "x").is_empty());
}
#[test]
fn compile_type_root_is_not_validation_root() {
    let c = catalog("type[root_type] = { value = scalar }");
    assert!(has(&c, "root_type", "value = x", "RULE130"));
}
#[test]
fn duplicate_ordinary_roots_are_rejected() {
    let d1 = parse_document("a", "root = scalar").unwrap();
    let d2 = parse_document("b", "root = bool").unwrap();
    assert!(matches!(
        RuleCatalog::compile(&[d1, d2], ScopeUniverse::default()),
        Err(CompileError::DuplicateRoot(_))
    ));
}
#[test]
fn root_names_are_ascii_case_insensitive() {
    let c = catalog("root = { value = scalar }");
    assert!(codes(&c, "ROOT", "value = x").is_empty());
}
#[test]
fn unknown_root_rule_code() {
    assert!(has(&catalog("root = scalar"), "missing", "x", "RULE130"));
}
#[test]
fn malformed_source_rule_code() {
    assert!(has(
        &catalog("root = scalar"),
        "root",
        "broken = {",
        "RULE001"
    ));
}
#[test]
fn unknown_field_rule_code() {
    assert!(has(
        &catalog("root = { known = scalar }"),
        "root",
        "unknown = x",
        "RULE101"
    ));
}
#[test]
fn missing_required_field_rule_code() {
    assert!(has(
        &catalog("root = { known = scalar }"),
        "root",
        "",
        "RULE110"
    ));
}
#[test]
fn too_many_field_occurrences_rule_code() {
    assert!(has(
        &catalog("root = { known = scalar }"),
        "root",
        "known = a\nknown = b",
        "RULE111"
    ));
}
#[test]
fn scalar_accepts_bare_values() {
    assert!(codes(&catalog("root = { known = scalar }"), "root", "known = a").is_empty());
}
#[test]
fn scalar_rejects_clause_shape() {
    assert!(has(
        &catalog("root = { known = scalar }"),
        "root",
        "known = { x = y }",
        "RULE103"
    ));
}
#[test]
fn nested_node_accepts_clause() {
    let c = catalog("root = { nested = { value = scalar } }");
    assert!(codes(&c, "root", "nested = { value = x }").is_empty());
}
#[test]
fn node_rejects_bare_shape() {
    assert!(has(
        &catalog("root = { nested = { value = scalar } }"),
        "root",
        "nested = x",
        "RULE102"
    ));
}
#[test]
fn bool_accepts_yes() {
    assert!(codes(&catalog("root = { flag = bool }"), "root", "flag = yes").is_empty());
}
#[test]
fn bool_rejects_arbitrary_value() {
    assert!(has(
        &catalog("root = { flag = bool }"),
        "root",
        "flag = maybe",
        "RULE120"
    ));
}
#[test]
fn integer_lower_bound_is_enforced() {
    assert!(has(
        &catalog("root = { n = int[1..10] }"),
        "root",
        "n = 0",
        "RULE120"
    ));
}
#[test]
fn integer_upper_bound_is_enforced() {
    assert!(has(
        &catalog("root = { n = int[1..10] }"),
        "root",
        "n = 11",
        "RULE120"
    ));
}
#[test]
fn integer_inclusive_bounds_accept_edges() {
    let c = catalog("root = { n = int[1..10] }");
    assert!(codes(&c, "root", "n = 1").is_empty() && codes(&c, "root", "n = 10").is_empty());
}
#[test]
fn float_range_rejects_outside_value() {
    assert!(has(
        &catalog("root = { n = float[-1.5..2.5] }"),
        "root",
        "n = 3",
        "RULE120"
    ));
}
#[test]
fn float_range_accepts_inside_value() {
    assert!(
        codes(
            &catalog("root = { n = float[-1.5..2.5] }"),
            "root",
            "n = 1.25"
        )
        .is_empty()
    );
}
#[test]
fn percent_rejects_above_hundred() {
    assert!(has(
        &catalog("root = { p = percent }"),
        "root",
        "p = 100.1",
        "RULE120"
    ));
}
#[test]
fn percent_accepts_zero_and_hundred() {
    let c = catalog("root = { p = percentage_field }");
    assert!(codes(&c, "root", "p = 0%").is_empty() && codes(&c, "root", "p = 100%").is_empty());
}
#[test]
fn date_accepts_leap_day() {
    assert!(
        codes(
            &catalog("root = { d = date_field }"),
            "root",
            "d = 2024.02.29"
        )
        .is_empty()
    );
}
#[test]
fn date_rejects_invalid_day() {
    assert!(has(
        &catalog("root = { d = date_field }"),
        "root",
        "d = 2023.02.29",
        "RULE120"
    ));
}
#[test]
fn date_rejects_invalid_month() {
    assert!(has(
        &catalog("root = { d = date_field }"),
        "root",
        "d = 2023.13.01",
        "RULE120"
    ));
}
#[test]
fn datetime_accepts_valid_clock() {
    assert!(
        codes(
            &catalog("root = { d = datetime_field }"),
            "root",
            "d = 2024.01.01.23.59.59"
        )
        .is_empty()
    );
}
#[test]
fn datetime_rejects_invalid_clock() {
    assert!(has(
        &catalog("root = { d = datetime_field }"),
        "root",
        "d = 2024.01.01.24.00.00",
        "RULE120"
    ));
}
#[test]
fn enum_accepts_declared_value() {
    let c = catalog("enums = { enum[color] = { red blue } }\nroot = { c = enum[color] }");
    assert!(codes(&c, "root", "c = red").is_empty());
}
#[test]
fn enum_rejects_undeclared_value() {
    let c = catalog("enums = { enum[color] = { red blue } }\nroot = { c = enum[color] }");
    assert!(has(&c, "root", "c = green", "RULE120"));
}
#[test]
fn enum_completion_is_filtered_by_prefix() {
    let c = catalog("enums = { enum[color] = { red blue } }\nroot = { c = enum[color] }");
    let x = c.completion("root", "b");
    assert!(x.contains(&"blue".to_string()) && !x.contains(&"red".to_string()));
}
#[test]
fn field_completion_is_filtered_by_prefix() {
    let c = catalog("root = { alpha = scalar\nbeta = bool }");
    assert_eq!(c.completion("root", "a"), vec!["alpha"]);
}
#[test]
fn completion_is_sorted_deterministically() {
    let c = catalog("root = { zulu = scalar\nalpha = scalar\nmid = scalar }");
    let x = c.completion("root", "");
    assert_eq!(x, vec!["alpha", "mid", "zulu"]);
}
#[test]
fn info_returns_description() {
    let c = catalog("root = { ## description = Human value\nvalue = scalar }");
    assert_eq!(c.info("root", "value").as_deref(), Some("Human value"));
}
#[test]
fn info_is_case_insensitive() {
    let c = catalog("root = { ## description = Human value\nvalue = scalar }");
    assert_eq!(c.info("root", "VALUE").as_deref(), Some("Human value"));
}
#[test]
fn info_missing_field_is_none() {
    assert!(
        catalog("root = { value = scalar }")
            .info("root", "missing")
            .is_none()
    );
}
#[test]
fn required_scope_accepts_matching_catalog_scope() {
    let c = catalog("## required = country\nroot = { value = scalar }");
    assert!(!has(&c, "root", "value = x", "RULE140"));
}
#[test]
fn required_scope_rejects_absent_scope() {
    let c = catalog("## required = galaxy\nroot = { value = scalar }");
    assert!(has(&c, "root", "value = x", "RULE140"));
}
#[test]
fn explicit_initial_scope_satisfies_requirement() {
    let c = catalog("## required = galaxy\nroot = { value = scalar }");
    assert!(
        !c.validate_source_with_scope("root", "value = x", Some("galaxy"))
            .diagnostics
            .iter()
            .any(|d| d.code == "RULE140")
    );
}
#[test]
fn cardinality_minimum_is_enforced() {
    assert!(has(
        &catalog("root = { ## cardinality = 2..inf\nvalue = scalar }"),
        "root",
        "value = x",
        "RULE110"
    ));
}
#[test]
fn cardinality_infinite_max_allows_repetition() {
    let c = catalog("root = { ## cardinality = 0..inf\nvalue = scalar }");
    assert!(!has(
        &c,
        "root",
        "value = a\nvalue = b\nvalue = c",
        "RULE111"
    ));
}
#[test]
fn specific_value_accepts_exact_match() {
    assert!(codes(&catalog("root = { mode = fixed }"), "root", "mode = fixed").is_empty());
}
#[test]
fn specific_value_rejects_other_match() {
    assert!(has(
        &catalog("root = { mode = fixed }"),
        "root",
        "mode = other",
        "RULE120"
    ));
}
#[test]
fn unknown_specific_is_still_a_specific_constraint() {
    assert!(has(
        &catalog("root = { mode = never_seen }"),
        "root",
        "mode = seen",
        "RULE120"
    ));
}
#[test]
fn unicode_field_names_validate() {
    let c = catalog("root = { 名称 = scalar }");
    assert!(codes(&c, "root", "名称 = 舰船").is_empty());
}
#[test]
fn unicode_values_preserve_byte_ranges() {
    let c = catalog("root = { value = scalar }");
    let r = c.validate_source("root", "value = 舰船");
    assert!(r.diagnostics.is_empty());
}
#[test]
fn diagnostics_are_deterministically_sorted() {
    let c = catalog("root = { a = bool\nb = int[1..2] }");
    let r = c.validate_source("root", "b = 9\na = maybe");
    assert!(r
        .diagnostics
        .windows(2)
        .all(|w| (w[0].range.start, w[0].code.clone()) <= (w[1].range.start, w[1].code.clone())));
}
#[test]
fn scope_universe_is_deterministic() {
    let a = ScopeUniverse::new(["z".into(), "a".into()]);
    let b = ScopeUniverse::new(["a".into(), "z".into()]);
    assert_eq!(a, b);
}
#[test]
fn deep_nested_rules_compile_within_limit() {
    let mut s = String::from("root = { value = scalar }");
    for _ in 0..3 {
        s = "root = { nested = { value = scalar } }".into();
    }
    assert!(
        catalog(&s)
            .completion("root", "")
            .contains(&"nested".into())
    );
}
#[test]
fn max_depth_constant_is_positive() {
    assert_eq!(MAX_DEPTH, 256);
}
#[test]
fn empty_source_reports_missing_root_children() {
    assert!(has(
        &catalog("root = { value = scalar }"),
        "root",
        "",
        "RULE110"
    ));
}
#[test]
fn comments_do_not_create_fields() {
    let c = catalog("root = { # comment\nvalue = scalar }");
    assert_eq!(c.completion("root", ""), vec!["value"]);
}
#[test]
fn unknown_root_completion_is_empty() {
    assert!(
        catalog("root = scalar")
            .completion("missing", "")
            .is_empty()
    );
}

#[test]
fn alias_left_grouped_leaf_accepts_value() {
    let c = catalog(
        r"alias[effect:foo] = scalar
root = { alias[effect] = scalar }",
    );
    assert!(codes(&c, "root", "foo = x").is_empty());
}

#[test]
fn alias_left_grouped_leaf_rejects_shape() {
    let c = catalog(
        r"alias[effect:foo] = scalar
root = { alias[effect] = scalar }",
    );
    assert!(has(&c, "root", "foo = { nested = x }", "RULE103"));
}

#[test]
fn alias_left_grouped_leaf_rejects_value() {
    let c = catalog(
        r"alias[effect:foo] = int[1..3]
root = { alias[effect] = int[1..3] }",
    );
    assert!(has(&c, "root", "foo = 9", "RULE120"));
}

#[test]
fn alias_left_grouped_node_accepts_shape() {
    let c = catalog(
        r"alias[effect:foo] = { amount = scalar }
root = { alias[effect] = { amount = scalar } }",
    );
    assert!(codes(&c, "root", "foo = { amount = x }").is_empty());
}

#[test]
fn alias_left_grouped_node_rejects_value_shape() {
    let c = catalog(
        r"alias[effect:foo] = { amount = scalar }
root = { alias[effect] = { amount = scalar } }",
    );
    assert!(has(&c, "root", "foo = x", "RULE102"));
}

#[test]
fn missing_alias_target_reports_rule130() {
    let c = catalog("root = { alias[effect] = scalar }");
    assert!(has(&c, "root", "foo = x", "RULE130"));
}

#[test]
fn single_alias_right_accepts_matching_leaf() {
    let c = catalog(
        r"single_alias[target] = scalar
root = { value = single_alias_right[target] }",
    );
    assert!(codes(&c, "root", "value = x").is_empty());
}

#[test]
fn single_alias_right_rejects_shape() {
    let c = catalog(
        r"single_alias[target] = scalar
root = { value = single_alias_right[target] }",
    );
    assert!(has(&c, "root", "value = { x = y }", "RULE103"));
}

#[test]
fn single_alias_right_rejects_missing_target() {
    let c = catalog("root = { value = single_alias_right[missing] }");
    assert!(has(&c, "root", "value = x", "RULE130"));
}

#[test]
fn alias_cycle_reports_rule130() {
    let c = catalog(
        "alias[effect:a] = alias[effect]\nalias[effect:b] = alias[effect]\nroot = { alias[effect] = scalar }",
    );
    assert!(has(&c, "root", "a = b", "RULE130"));
}

#[test]
fn validation_nesting_over_max_depth_reports_rule150() {
    let mut source = String::from("x = ");
    for _ in 0..(MAX_DEPTH + 2) {
        source.push_str("{ x = ");
    }
    source.push('x');
    for _ in 0..(MAX_DEPTH + 2) {
        source.push_str(" }");
    }
    let c = catalog("root = { x = { x = scalar } }");
    assert!(has(&c, "root", &source, "RULE001"));
}

#[test]
fn compile_nesting_over_max_depth_is_too_deep() {
    let mut source = String::from("root = ");
    for _ in 0..(MAX_DEPTH + 2) {
        source.push_str("{ x = ");
    }
    source.push_str("scalar");
    for _ in 0..(MAX_DEPTH + 2) {
        source.push_str(" }");
    }
    let mut kind = cwtools_rule_ir::RuleKind::Leaf {
        left: cwtools_rule_ir::NewField::Specific("value".into()),
        right: cwtools_rule_ir::NewField::Scalar,
    };
    for _ in 0..(MAX_DEPTH + 2) {
        kind = cwtools_rule_ir::RuleKind::Node {
            left: cwtools_rule_ir::NewField::Specific("x".into()),
            rules: vec![cwtools_rule_ir::NewRule {
                kind,
                options: cwtools_rule_ir::Options {
                    min: 1,
                    max: 1,
                    ..Default::default()
                },
                range: cwtools_script_syntax::ByteRange { start: 0, end: 0 },
                comments: vec![],
            }],
        };
    }
    let document = cwtools_rule_ir::Document {
        file: "too-deep.cwt".into(),
        rules: vec![cwtools_rule_ir::RootRule::Ordinary(
            "root".into(),
            cwtools_rule_ir::NewRule {
                kind,
                options: cwtools_rule_ir::Options {
                    min: 1,
                    max: 1,
                    ..Default::default()
                },
                range: cwtools_script_syntax::ByteRange { start: 0, end: 0 },
                comments: vec![],
            },
        )],
        types: vec![],
        enums: vec![],
        complex_enums: vec![],
        metadata: cwtools_rule_ir::ExtendedMetadata::default(),
        values: vec![],
        directives: std::collections::BTreeMap::default(),
        comments: vec![],
        order: vec![],
        source,
    };
    assert!(matches!(
        RuleCatalog::compile(&[document], ScopeUniverse::default()),
        Err(CompileError::TooDeep)
    ));
}

#[test]
fn cardinality_overflow_points_at_rule_source_occurrence() {
    let c = catalog("root = { ## cardinality = 1..2\nvalue = scalar }");
    let source = "value = a\nvalue = b\nvalue = c";
    let result = c.validate_source("root", source);
    let diagnostic = result
        .diagnostics
        .iter()
        .find(|d| d.code == "RULE111")
        .expect("overflow diagnostic");
    let third = source.find("value = c").expect("first overflow occurrence");
    assert_eq!(diagnostic.range.start, third);
}

#[test]
fn cardinality_overflow_range_covers_rule_source_occurrence() {
    let c = catalog("root = { ## cardinality = 1..2\nvalue = scalar }");
    let source = "value = a\nvalue = b\nvalue = c";
    let result = c.validate_source("root", source);
    let diagnostic = result
        .diagnostics
        .iter()
        .find(|d| d.code == "RULE111")
        .expect("overflow diagnostic");
    let third = source.find("value = c").expect("third occurrence");
    assert_eq!(diagnostic.range.start, third);
    assert!(diagnostic.range.end > diagnostic.range.start);
}

#[test]
fn parameter_accepts_named_dollar_value() {
    assert!(codes(&catalog("root = { p = $parameter }"), "root", "p = $name$").is_empty());
}
#[test]
fn parameter_accepts_underscore_name() {
    assert!(codes(&catalog("root = { p = $parameter }"), "root", "p = $_name$").is_empty());
}
#[test]
fn parameter_accepts_fallback() {
    assert!(
        codes(
            &catalog("root = { p = $parameter }"),
            "root",
            "p = $name$|fallback"
        )
        .is_empty()
    );
}
#[test]
fn parameter_rejects_missing_closing_dollar() {
    assert!(has(
        &catalog("root = { p = $parameter }"),
        "root",
        "p = $name",
        "RULE120"
    ));
}
#[test]
fn parameter_rejects_digit_initial_name() {
    assert!(has(
        &catalog("root = { p = $parameter }"),
        "root",
        "p = $1name$",
        "RULE120"
    ));
}
#[test]
fn parameter_rejects_empty_fallback() {
    assert!(has(
        &catalog("root = { p = $parameter }"),
        "root",
        "p = $name$|",
        "RULE120"
    ));
}
#[test]
fn parameter_rejects_whitespace_name() {
    assert!(has(
        &catalog("root = { p = $parameter }"),
        "root",
        "p = $bad name$",
        "RULE120"
    ));
}
#[test]
fn parameter_value_accepts_literal() {
    assert!(
        codes(
            &catalog("root = { p = $parameter_value }"),
            "root",
            "p = literal"
        )
        .is_empty()
    );
}
#[test]
fn parameter_value_accepts_parameter() {
    assert!(
        codes(
            &catalog("root = { p = $parameter_value }"),
            "root",
            "p = $value$"
        )
        .is_empty()
    );
}
#[test]
fn parameter_value_accepts_number() {
    assert!(
        codes(
            &catalog("root = { p = $parameter_value }"),
            "root",
            "p = -1.25"
        )
        .is_empty()
    );
}
#[test]
fn parameter_value_rejects_empty() {
    assert!(has(
        &catalog("root = { p = $parameter_value }"),
        "root",
        "p = ",
        "RULE001"
    ));
}
#[test]
fn parameter_value_accepts_first_loose_expression_token() {
    assert!(
        codes(
            &catalog("root = { p = $parameter_value }"),
            "root",
            "p = two words"
        )
        .is_empty()
    );
}
#[test]
fn localisation_parameter_accepts_parameter() {
    assert!(
        codes(
            &catalog("root = { p = $localisation_parameter }"),
            "root",
            "p = $loc$"
        )
        .is_empty()
    );
}
#[test]
fn localisation_parameter_rejects_invalid_parameter() {
    assert!(has(
        &catalog("root = { p = $localisation_parameter }"),
        "root",
        "p = loc",
        "RULE120"
    ));
}
#[test]
fn simple_type_accepts_value() {
    let c = catalog("types = { type[id] = { value = scalar } }\nroot = { id = <id> }");
    assert!(codes(&c, "root", "id = x").is_empty());
}
#[test]
fn simple_type_rejects_missing_type() {
    let c = catalog("root = { id = <missing> }");
    assert!(has(&c, "root", "id = x", "RULE130"));
}
#[test]
fn simple_type_rejects_bad_value() {
    let c = catalog("types = { type[id] = { value = bool } }\nroot = { id = <id> }");
    assert!(has(&c, "root", "id = maybe", "RULE120"));
}
#[test]
fn simple_type_cycle_is_terminating() {
    let c = catalog(
        "types = { type[a] = { value = <b> } type[b] = { value = <a> } }\nroot = { value = <a> }",
    );
    assert!(codes(&c, "root", "value = x").is_empty());
}
#[test]
fn simple_type_int_constraint_is_enforced() {
    let c = catalog("types = { type[small] = { value = int[1..3] } }\nroot = { value = <small> }");
    assert!(has(&c, "root", "value = 9", "RULE120"));
}
#[test]
fn simple_type_int_constraint_accepts_edge() {
    let c = catalog("types = { type[small] = { value = int[1..3] } }\nroot = { value = <small> }");
    assert!(codes(&c, "root", "value = 3").is_empty());
}
#[test]
fn complex_type_accepts_prefix_suffix() {
    let c = catalog("types = { type[id] = { value = scalar } }\nroot = { value = pre<id>suf }");
    assert!(codes(&c, "root", "value = preXsuf").is_empty());
}
#[test]
fn complex_type_rejects_prefix() {
    let c = catalog("types = { type[id] = { value = scalar } }\nroot = { value = pre<id>suf }");
    assert!(has(&c, "root", "value = Xsuf", "RULE120"));
}
#[test]
fn complex_type_rejects_suffix() {
    let c = catalog("types = { type[id] = { value = scalar } }\nroot = { value = pre<id>suf }");
    assert!(has(&c, "root", "value = preX", "RULE120"));
}
#[test]
fn complex_type_rejects_empty_inner() {
    let c = catalog("types = { type[id] = { value = scalar } }\nroot = { value = pre<id>suf }");
    assert!(has(&c, "root", "value = presuf", "RULE120"));
}
#[test]
fn complex_type_reports_missing_inner_type() {
    let c = catalog("root = { value = pre<missing>suf }");
    assert!(has(&c, "root", "value = preXsuf", "RULE130"));
}
#[test]
fn compile_error_unknown_scope_for_root_option() {
    let d = parse_document("x", "## scope = galaxy\nroot = scalar").unwrap();
    assert!(
        matches!(RuleCatalog::compile(&[d], ScopeUniverse::new(["country".into()])), Err(CompileError::UnknownScope(s)) if s == "galaxy")
    );
}
#[test]
fn compile_scope_option_accepts_known_scope() {
    let d = parse_document("x", "## scope = country\nroot = scalar").unwrap();
    assert!(RuleCatalog::compile(&[d], ScopeUniverse::new(["country".into()])).is_ok());
}
#[test]
fn nested_required_scopes_accept_matching_scope() {
    let c = catalog(
        "## required = country\nroot = { nested = { ## required = planet\nvalue = scalar } }",
    );
    assert!(!has(&c, "root", "nested = { value = x }", "RULE140"));
}
#[test]
fn nested_required_scopes_reject_missing_scope() {
    let c = catalog(
        "## required = country\nroot = { nested = { ## required = galaxy\nvalue = scalar } }",
    );
    assert!(has(&c, "root", "nested = { value = x }", "RULE140"));
}
#[test]
fn parse_newfield_parameter_variant() {
    let d = parse_document("x", "root = { p = $parameter }").unwrap();
    assert!(format!("{d:?}").contains("Parameter"));
}
#[test]
fn parse_newfield_parameter_value_variant() {
    let d = parse_document("x", "root = { p = $parameter_value }").unwrap();
    assert!(format!("{d:?}").contains("ParameterValue"));
}
#[test]
fn parse_newfield_localisation_parameter_variant() {
    let d = parse_document("x", "root = { p = $localisation_parameter }").unwrap();
    assert!(format!("{d:?}").contains("LocalisationParameter"));
}
#[test]
fn parse_newfield_complex_variant() {
    let d = parse_document("x", "root = { p = pre<id>suf }").unwrap();
    assert!(format!("{d:?}").contains("Complex"));
}
#[test]
fn parse_newfield_scope_variant() {
    let d = parse_document("x", "root = { p = scope[a,b] }").unwrap();
    assert!(format!("{d:?}").contains("Scope"));
}

#[test]
fn subtype_primary_required_field_present_activates() {
    let c = catalog("root = { subtype[mode] = { marker = scalar } }");
    assert!(codes(&c, "root", "marker = yes").is_empty());
}

#[test]
fn subtype_primary_absent_does_not_activate_or_report_child_missing() {
    let c = catalog("root = { subtype[mode] = { marker = scalar } }");
    let diagnostics = codes(&c, "root", "other = yes");
    assert!(!diagnostics.contains(&"RULE110".to_string()));
    assert!(diagnostics.contains(&"RULE101".to_string()));
}

#[test]
fn subtype_primary_specific_value_selects_branch() {
    let c = catalog("root = { subtype[mode] = { mode = on\nmarker = scalar } }");
    assert!(codes(&c, "root", "mode = on\nmarker = yes").is_empty());
    assert!(has(&c, "root", "mode = off\nmarker = yes", "RULE101"));
}

#[test]
fn subtype_primary_shape_selects_node_branch() {
    let c = catalog("root = { subtype[config] = { config = { value = scalar } } }");
    assert!(codes(&c, "root", "config = { value = yes }").is_empty());
    assert!(has(&c, "root", "config = yes", "RULE101"));
}

#[test]
fn negated_same_name_activates_when_primary_is_inactive() {
    let c = catalog(
        "root = { subtype[mode] = { mode = on\npositive = scalar } subtype[!mode] = { negative = scalar } }",
    );
    assert!(codes(&c, "root", "negative = yes").is_empty());
}

#[test]
fn negated_same_name_is_suppressed_when_primary_is_active() {
    let c = catalog(
        "root = { subtype[mode] = { mode = on\npositive = scalar } subtype[!mode] = { negative = scalar } }",
    );
    assert!(has(&c, "root", "mode = on\nnegative = yes", "RULE101"));
}

#[test]
fn multiple_independent_primary_subtypes_can_activate() {
    let c = catalog(
        "root = { subtype[a] = { a = yes\nfrom_a = scalar } subtype[b] = { b = yes\nfrom_b = scalar } }",
    );
    assert!(codes(&c, "root", "a = yes\nb = yes\nfrom_a = x\nfrom_b = y").is_empty());
}

#[test]
fn independent_subtype_inactive_branch_does_not_require_children() {
    let c = catalog(
        "root = { subtype[a] = { a = yes\nfrom_a = scalar } subtype[b] = { b = yes\nfrom_b = scalar } }",
    );
    let d = codes(&c, "root", "a = yes\nfrom_a = x");
    assert!(!d.contains(&"RULE110".to_string()));
}

#[test]
fn ordinary_and_active_subtype_fields_merge() {
    let c = catalog("root = { ordinary = scalar subtype[mode] = { mode = on\nactive = scalar } }");
    assert!(codes(&c, "root", "ordinary = x\nmode = on\nactive = y").is_empty());
}

#[test]
fn ordinary_and_active_subtype_cardinality_is_enforced() {
    let c = catalog(
        "root = { ## cardinality = 1..1\nvalue = scalar subtype[mode] = { mode = on\n## cardinality = 1..1\nvalue = scalar } }",
    );
    assert!(has(
        &c,
        "root",
        "mode = on\nvalue = a\nvalue = b",
        "RULE111"
    ));
}

#[test]
fn nested_subtype_activates_inside_active_subtype() {
    let c = catalog(
        "root = { subtype[outer] = { outer = yes\nsubtype[inner] = { inner = yes\nleaf = scalar } } }",
    );
    assert!(codes(&c, "root", "outer = yes\ninner = yes\nleaf = x").is_empty());
}

#[test]
fn inactive_nested_subtype_does_not_report_missing_child() {
    let c = catalog(
        "root = { subtype[outer] = { outer = yes\nsubtype[inner] = { inner = yes\nleaf = scalar } } }",
    );
    let d = codes(&c, "root", "outer = no");
    assert!(!d.contains(&"RULE110".to_string()));
}

#[test]
fn subtype_wrapper_is_not_reported_as_unknown_field() {
    let d = parse_document("x", "root = { subtype[mode] = { value = scalar } }").unwrap();
    assert!(format!("{d:?}").contains("Subtype"));
}

#[test]
fn malformed_empty_subtype_name_is_an_ordinary_node() {
    let d = parse_document("x", "root = { subtype[] = { value = scalar } }").unwrap();
    let text = format!("{d:?}");
    assert!(!text.contains("Subtype {"));
    assert!(text.contains("subtype[]"));
}

#[test]
fn malformed_subtype_name_validates_as_normal_node() {
    let c = catalog("root = { subtype[] = { value = scalar } }");
    assert!(codes(&c, "root", "subtype[] = { value = x }").is_empty());
}

#[test]
fn completion_traverses_subtype_children() {
    let c = catalog("root = { subtype[mode] = { branch_value = scalar } }");
    assert!(
        c.completion("root", "branch")
            .contains(&"branch_value".to_string())
    );
}

#[test]
fn info_traverses_subtype_children() {
    let c = catalog(
        "root = { subtype[mode] = { ## description = Branch detail\nbranch_value = scalar } }",
    );
    assert_eq!(
        c.info("root", "branch_value").as_deref(),
        Some("Branch detail")
    );
}

#[test]
fn subtype_completion_is_sorted_and_deduplicated() {
    let c = catalog(
        "root = { subtype[a] = { zeta = scalar\nalpha = scalar } subtype[b] = { alpha = scalar\nbeta = scalar } }",
    );
    assert_eq!(c.completion("root", ""), vec!["alpha", "beta", "zeta"]);
}

#[test]
fn subtype_diagnostics_are_deterministic() {
    let c = catalog("root = { subtype[mode] = { mode = on\nvalue = bool } }");
    let a = codes(&c, "root", "mode = on\nvalue = maybe");
    let b = codes(&c, "root", "mode = on\nvalue = maybe");
    assert_eq!(a, b);
}

#[test]
fn subtype_diagnostic_order_is_deterministic_by_range() {
    let c = catalog("root = { subtype[mode] = { mode = on\na = bool\nb = int[1..2] } }");
    let r = c.validate_source("root", "mode = on\nb = 9\na = maybe");
    assert!(
        r.diagnostics
            .windows(2)
            .all(|w| w[0].range.start <= w[1].range.start)
    );
}

#[test]
fn subtype_activation_respects_max_validation_depth() {
    let c = catalog("root = { subtype[mode] = { mode = on\nvalue = scalar } }");
    let mut source = String::from("mode = on\nvalue = ");
    for _ in 0..(MAX_DEPTH + 2) {
        source.push_str("{ value = ");
    }
    source.push('x');
    for _ in 0..(MAX_DEPTH + 2) {
        source.push_str(" }");
    }
    assert!(has(&c, "root", &source, "RULE150") || has(&c, "root", &source, "RULE001"));
}

// ScopeFrame regression coverage: every frame slot is observable through scope values.
#[test]
fn scope_frame_root_initial_exact_required_pass_fail() {
    let c = catalog("## required = galaxy\nroot = { value = scalar }");
    assert!(codes(&c, "root", "value = x").contains(&"RULE140".to_string()));
    assert!(
        !c.validate_source_with_scope("root", "value = x", Some("galaxy"))
            .diagnostics
            .iter()
            .any(|d| d.code == "RULE140")
    );
}
#[test]
fn scope_frame_push_nested_required_passes() {
    let c = catalog(
        "root = { ## push_scope = planet\nchild = { ## required = planet\nvalue = scalar } }",
    );
    assert!(!has(&c, "root", "child = { value = x }", "RULE140"));
}
#[test]
fn scope_frame_parent_required_checked_before_push() {
    let c = catalog(
        "## required = country\nroot = { ## push_scope = planet\nchild = { value = scalar } }",
    );
    assert!(
        c.validate_source_with_scope("root", "child = { value = x }", Some("ship"))
            .diagnostics
            .iter()
            .any(|d| d.code == "RULE140")
    );
    assert!(
        !c.validate_source_with_scope("root", "child = { value = x }", Some("country"))
            .diagnostics
            .iter()
            .any(|d| d.code == "RULE140")
    );
}
#[test]
fn scope_frame_wrong_child_scope_fails() {
    let c = catalog(
        "root = { ## push_scope = planet\nchild = { ## required = ship\nvalue = scalar } }",
    );
    assert!(has(&c, "root", "child = { value = x }", "RULE140"));
}
#[test]
fn scope_frame_nested_double_push() {
    let c = catalog(
        "root = { ## push_scope = planet\na = { ## push_scope = ship\nb = { ## required = ship\nvalue = scalar } } }",
    );
    assert!(!has(&c, "root", "a = { b = { value = x } }", "RULE140"));
}
#[test]
fn scope_frame_sibling_isolation() {
    let c = catalog(
        "root = { ## push_scope = planet\na = { ## required = planet\nvalue = scalar }\nb = { ## required = planet\nvalue = scalar } }",
    );
    assert!(!has(
        &c,
        "root",
        "a = { value = x }\nb = { value = x }",
        "RULE140"
    ));
}
#[test]
fn scope_frame_replace_this_nested_passes() {
    let c = catalog(
        "root = { ## replace_scope = { this = ship }\nchild = { ## required = ship\nvalue = scalar } }",
    );
    assert!(!has(&c, "root", "child = { value = x }", "RULE140"));
}
#[test]
fn scope_frame_replace_this_wrong_fails() {
    let c = catalog(
        "root = { ## replace_scope = { this = ship }\nchild = { ## required = planet\nvalue = scalar } }",
    );
    assert!(has(&c, "root", "child = { value = x }", "RULE140"));
}
#[test]
fn scope_frame_replace_root_value_check() {
    let c = catalog(
        "root = { ## replace_scope = { root = system }\nchild = { value = scope[system] } }",
    );
    assert!(codes(&c, "root", "child = { value = system }").is_empty());
    assert!(has(&c, "root", "child = { value = country }", "RULE120"));
}
#[test]
fn scope_frame_replace_this_value_check() {
    let c =
        catalog("root = { ## replace_scope = { this = ship }\nchild = { value = scope[ship] } }");
    assert!(codes(&c, "root", "child = { value = ship }").is_empty());
    assert!(has(&c, "root", "child = { value = planet }", "RULE120"));
}
#[test]
fn scope_frame_replace_from_value_check() {
    let c =
        catalog("root = { ## replace_scope = { from = fleet }\nchild = { value = scope[fleet] } }");
    assert!(codes(&c, "root", "child = { value = fleet }").is_empty());
    assert!(has(&c, "root", "child = { value = country }", "RULE120"));
}
#[test]
fn scope_frame_replace_prev_value_check() {
    let c =
        catalog("root = { ## replace_scope = { prev = moon }\nchild = { value = scope[moon] } }");
    assert!(codes(&c, "root", "child = { value = moon }").is_empty());
    assert!(has(&c, "root", "child = { value = country }", "RULE120"));
}
#[test]
fn scope_frame_push_precedence_over_replace() {
    let c = catalog(
        "root = { ## push_scope = ship\n## replace_scope = { this = planet }\nchild = { value = scope[ship] } }",
    );
    assert!(codes(&c, "root", "child = { value = ship }").is_empty());
    assert!(has(&c, "root", "child = { value = planet }", "RULE120"));
}
#[test]
fn scope_frame_nested_unknown_push_compile_error() {
    let d = parse_document(
        "x",
        "root = { ## push_scope = galaxy\nchild = { value = scalar } }",
    )
    .unwrap();
    assert!(
        matches!(RuleCatalog::compile(&[d], ScopeUniverse::new(["country".into()])), Err(CompileError::UnknownScope(s)) if s == "galaxy")
    );
}
#[test]
fn scope_frame_unknown_replace_root_compile_error() {
    let d = parse_document(
        "x",
        "root = { ## replace_scope = { root = galaxy }\nchild = { value = scalar } }",
    )
    .unwrap();
    assert!(
        matches!(RuleCatalog::compile(&[d],ScopeUniverse::new(["country".into()])),Err(CompileError::UnknownScope(s)) if s=="galaxy")
    );
}
#[test]
fn scope_frame_unknown_replace_this_compile_error() {
    let d = parse_document(
        "x",
        "root = { ## replace_scope = { this = galaxy }\nchild = { value = scalar } }",
    )
    .unwrap();
    assert!(
        matches!(RuleCatalog::compile(&[d],ScopeUniverse::new(["country".into()])),Err(CompileError::UnknownScope(s)) if s=="galaxy")
    );
}
#[test]
fn scope_frame_unknown_replace_from_compile_error() {
    let d = parse_document(
        "x",
        "root = { ## replace_scope = { from = galaxy }\nchild = { value = scalar } }",
    )
    .unwrap();
    assert!(
        matches!(RuleCatalog::compile(&[d],ScopeUniverse::new(["country".into()])),Err(CompileError::UnknownScope(s)) if s=="galaxy")
    );
}
#[test]
fn scope_frame_unknown_replace_prev_compile_error() {
    let d = parse_document(
        "x",
        "root = { ## replace_scope = { prev = galaxy }\nchild = { value = scalar } }",
    )
    .unwrap();
    assert!(
        matches!(RuleCatalog::compile(&[d],ScopeUniverse::new(["country".into()])),Err(CompileError::UnknownScope(s)) if s=="galaxy")
    );
}
#[test]
fn scope_frame_empty_universe_accepts_literal() {
    let d = parse_document("x", "root = { value = scope[literal] }").unwrap();
    let c = RuleCatalog::compile(&[d], ScopeUniverse::default()).unwrap();
    assert!(codes(&c, "root", "value = literal").is_empty());
}
#[test]
fn scope_field_accepts_literal() {
    let c = catalog("root = { value = scope[literal] }");
    assert!(codes(&c, "root", "value = literal").is_empty());
}
#[test]
fn scope_field_accepts_current_fallback() {
    let c = catalog("root = { ## push_scope = planet\nchild = { value = scope[] } }");
    assert!(codes(&c, "root", "child = { value = planet }").is_empty());
}
#[test]
fn scope_field_accepts_root_fallback() {
    let c =
        catalog("root = { ## replace_scope = { root = country }\nchild = { value = scope[] } }");
    assert!(codes(&c, "root", "child = { value = country }").is_empty());
}
#[test]
fn scope_field_accepts_from_fallback() {
    let c = catalog("root = { ## replace_scope = { from = fleet }\nchild = { value = scope[] } }");
    assert!(codes(&c, "root", "child = { value = fleet }").is_empty());
}
#[test]
fn scope_field_accepts_prev_fallback() {
    let c = catalog("root = { ## replace_scope = { prev = moon }\nchild = { value = scope[] } }");
    assert!(codes(&c, "root", "child = { value = moon }").is_empty());
}
#[test]
fn scope_field_rejects_unknown_value() {
    let c = catalog("root = { value = scope[country] }");
    assert!(has(&c, "root", "value = galaxy", "RULE120"));
}
#[test]
fn scope_field_accepts_range_literal() {
    let c = catalog("root = { value = scope[country,planet] }");
    assert!(codes(&c, "root", "value = planet").is_empty());
}
#[test]
fn scope_frame_propagates_through_alias() {
    let c = catalog("alias[child:planet] = scope[planet]\nroot = { child = alias[child] }");
    assert!(codes(&c, "root", "child = planet").is_empty());
}
#[test]
fn scope_frame_propagates_through_type() {
    let c =
        catalog("types = { type[child] = { value = scope[planet] } }\nroot = { child = <child> }");
    assert!(codes(&c, "root", "child = planet").is_empty());
}
#[test]
fn scope_frame_propagates_through_subtype() {
    let c = catalog("root = { subtype[mode] = { mode = on\nvalue = scope[planet] } }");
    assert!(codes(&c, "root", "mode = on\nvalue = planet").is_empty());
}

fn cancelled(
    c: &RuleCatalog,
    root: &str,
    source: &str,
    limit: usize,
) -> (ValidationOutcome, usize) {
    use std::cell::Cell;
    let calls = Cell::new(0);
    let outcome = c.validate_source_cancellable(root, source, None, || {
        let n = calls.get();
        calls.set(n + 1);
        n >= limit
    });
    (outcome, calls.get())
}

#[test]
fn cancellation_pre_cancel_wins_before_parse() {
    let c = catalog("root = { value = scalar }");
    let (outcome, calls) = cancelled(&c, "root", "broken = {", 0);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
    assert_eq!(calls, 1);
}

#[test]
fn cancellation_post_parse_stops_before_root() {
    let c = catalog("root = { value = scalar }");
    let (outcome, calls) = cancelled(&c, "root", "value = x", 1);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
    assert!(calls >= 2);
}

#[test]
fn cancellation_mid_first_node_is_cancelled() {
    let c = catalog("root = { a = bool\n b = bool\n c = bool }");
    let (outcome, _) = cancelled(&c, "root", "a = maybe\nb = maybe\nc = maybe", 2);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
}

#[test]
fn cancellation_late_node_is_cancelled() {
    let c = catalog("root = { a = bool\n b = bool\n c = bool\n d = bool\n e = bool }");
    let (early, early_calls) = cancelled(
        &c,
        "root",
        "a = maybe\nb = maybe\nc = maybe\nd = maybe\ne = maybe",
        2,
    );
    let (late, late_calls) = cancelled(
        &c,
        "root",
        "a = maybe\nb = maybe\nc = maybe\nd = maybe\ne = maybe",
        20,
    );
    assert_eq!(early, ValidationOutcome::Cancelled);
    assert!(late_calls > early_calls);
    assert!(
        matches!(late, ValidationOutcome::Completed(_)) || late == ValidationOutcome::Cancelled
    );
}

#[test]
fn cancellation_cardinality_loop_is_cancelled() {
    let c = catalog("root = { ## cardinality = 1..1\n value = scalar }");
    let (outcome, _) = cancelled(&c, "root", "value = a\nvalue = b\nvalue = c", 3);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
}

#[test]
fn cancellation_alias_expansion_is_cancelled() {
    let c = catalog("alias[group:item] = { value = bool }\nroot = { item = alias[group] }");
    let (outcome, _) = cancelled(&c, "root", "item = nope", 2);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
}

#[test]
fn cancellation_single_alias_expansion_is_cancelled() {
    let c = catalog("single_alias[item] = { value = bool }\nroot = { item = single_alias[item] }");
    let (outcome, _) = cancelled(&c, "root", "item = nope", 2);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
}

#[test]
fn cancellation_type_expansion_is_cancelled() {
    let c = catalog("types = { type[item] = { value = bool } }\nroot = { item = <item> }");
    let (outcome, _) = cancelled(&c, "root", "item = nope", 2);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
}

#[test]
fn cancellation_complex_type_expansion_is_cancelled() {
    let c = catalog(
        "types = { type[item] = { value = bool } }\nroot = { item = prefix:<item>:suffix }",
    );
    let (outcome, _) = cancelled(&c, "root", "item = prefix:nope:suffix", 2);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
}

#[test]
fn cancellation_subtype_probe_is_cancelled() {
    let c = catalog("root = { subtype[mode] = { mode = yes\nvalue = bool } }");
    let (outcome, _) = cancelled(&c, "root", "mode = yes\nvalue = maybe", 2);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
}

#[test]
fn cancellation_nested_subtype_is_cancelled() {
    let c = catalog(
        "root = { subtype[outer] = { outer = yes\nsubtype[inner] = { inner = yes\nvalue = bool } } }",
    );
    let (outcome, _) = cancelled(&c, "root", "outer = yes\ninner = yes\nvalue = maybe", 3);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
}

#[test]
fn cancellation_scope_required_is_cancelled() {
    let c = catalog("## required = country\nroot = { value = scalar }");
    let (outcome, _) = cancelled(&c, "root", "value = x", 1);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
}

#[test]
fn cancellation_deep_recursion_is_cancelled() {
    let c = catalog("root = { child = { child = { child = { value = scalar } } } }");
    let (outcome, _) = cancelled(
        &c,
        "root",
        "child = { child = { child = { value = x } } }",
        3,
    );
    assert_eq!(outcome, ValidationOutcome::Cancelled);
}

#[test]
fn cancellation_precedes_invalid_source() {
    let c = catalog("root = { value = scalar }");
    assert_eq!(
        cancelled(&c, "root", "value = {", 0).0,
        ValidationOutcome::Cancelled
    );
    assert!(matches!(
        cancelled(&c, "root", "value = {", 100).0,
        ValidationOutcome::Completed(_)
    ));
}

#[test]
fn never_cancel_completed_matches_validate_source() {
    let c = catalog("root = { value = bool }");
    let ordinary = c.validate_source("root", "value = maybe");
    let outcome = c.validate_source_cancellable("root", "value = maybe", None, || false);
    assert_eq!(outcome, ValidationOutcome::Completed(ordinary));
}

#[test]
fn counter_threshold_zero_cancels() {
    let c = catalog("root = { value = scalar }");
    assert_eq!(
        cancelled(&c, "root", "value = x", 0).0,
        ValidationOutcome::Cancelled
    );
}

#[test]
fn counter_threshold_one_cancels_after_entry() {
    let c = catalog("root = { value = scalar }");
    assert_eq!(
        cancelled(&c, "root", "value = x", 1).0,
        ValidationOutcome::Cancelled
    );
}

#[test]
fn counter_threshold_high_completes() {
    let c = catalog("root = { value = scalar }");
    assert!(matches!(
        cancelled(&c, "root", "value = x", usize::MAX).0,
        ValidationOutcome::Completed(_)
    ));
}

#[test]
fn repeated_cancelled_calls_do_not_pollute_normal_validation() {
    let c = catalog("root = { value = bool }");
    for _ in 0..5 {
        assert_eq!(
            cancelled(&c, "root", "value = maybe", 0).0,
            ValidationOutcome::Cancelled
        );
    }
    assert_eq!(
        c.validate_source("root", "value = maybe").diagnostics.len(),
        1
    );
}

#[test]
fn cancelled_has_no_partial_result_pattern() {
    let c = catalog("root = { a = bool\n b = bool }");
    match cancelled(&c, "root", "a = maybe\nb = maybe", 2).0 {
        ValidationOutcome::Cancelled => {}
        ValidationOutcome::Completed(result) => panic!(
            "unexpected partial diagnostics: {}",
            result.diagnostics.len()
        ),
    }
}

#[test]
fn cancellation_closure_call_count_is_bounded_after_cancel() {
    let c = catalog("root = { a = bool\n b = bool\n c = bool\n d = bool }");
    let (outcome, calls) = cancelled(&c, "root", "a = maybe\nb = maybe\nc = maybe\nd = maybe", 2);
    assert_eq!(outcome, ValidationOutcome::Cancelled);
    assert!(calls <= 4);
}

#[test]
fn cancellation_is_local_to_one_validation() {
    let c = catalog("root = { value = bool }");
    let (first, _) = cancelled(&c, "root", "value = maybe", 0);
    assert_eq!(first, ValidationOutcome::Cancelled);
    assert!(
        c.validate_source("root", "value = yes")
            .diagnostics
            .is_empty()
    );
}

#[test]
fn cancelled_invalid_root_does_not_return_parse_diagnostic() {
    let c = catalog("root = scalar");
    assert_eq!(
        cancelled(&c, "missing", "broken = {", 0).0,
        ValidationOutcome::Cancelled
    );
}

#[test]
fn cancellation_with_scope_does_not_leak_scope_state() {
    let c = catalog("## required = country\nroot = { value = scalar }");
    assert_eq!(
        cancelled(&c, "root", "value = x", 0).0,
        ValidationOutcome::Cancelled
    );
    assert!(
        c.validate_source_with_scope("root", "value = x", Some("country"))
            .diagnostics
            .is_empty()
    );
}

#[test]
fn diagnostic_message_keys_are_stable() {
    let expected = [
        ("RULE001", "rules.syntax"),
        ("RULE101", "rules.unknown_field"),
        ("RULE102", "rules.expected_clause"),
        ("RULE103", "rules.expected_scalar"),
        ("RULE110", "rules.cardinality_minimum"),
        ("RULE111", "rules.cardinality_maximum"),
        ("RULE120", "rules.invalid_value"),
        ("RULE130", "rules.unresolved_reference"),
        ("RULE140", "rules.scope_mismatch"),
        ("RULE150", "rules.depth_exceeded"),
    ];
    for (code, key) in expected {
        assert_eq!(diagnostic_message_key(code), key);
    }
    assert_eq!(diagnostic_message_key("RULE999"), "rules.unknown");
}

#[test]
fn emitted_diagnostics_carry_canonical_message_keys() {
    let fixtures = [
        (catalog("root = { known = scalar }"), "root", "broken = {"),
        (catalog("root = { known = scalar }"), "root", "unknown = x"),
        (
            catalog("root = { known = { child = scalar } }"),
            "root",
            "known = x",
        ),
        (
            catalog("root = { known = scalar }"),
            "root",
            "known = { child = x }",
        ),
        (catalog("root = { known = scalar }"), "root", ""),
        (
            catalog("root = { known = scalar }"),
            "root",
            "known = a\nknown = b",
        ),
        (catalog("root = { known = bool }"), "root", "known = maybe"),
        (catalog("root = { known = <missing> }"), "root", "known = x"),
    ];
    for (catalog, root, source) in fixtures {
        for diagnostic in catalog.validate_source(root, source).diagnostics {
            assert_eq!(
                diagnostic.message_key,
                diagnostic_message_key(&diagnostic.code)
            );
        }
    }
}

#[test]
fn contextual_completion_uses_direct_root_children() {
    let c = catalog("root = { alpha = scalar node = { child = scalar } }");
    assert_eq!(
        c.completion_at("root", "", 0, "").unwrap(),
        vec!["alpha", "node"]
    );
}
#[test]
fn contextual_completion_enters_nested_clause() {
    let c = catalog("root = { root_field = scalar node = { child = scalar } }");
    let source = "node = { child = x }";
    assert_eq!(
        c.completion_at("root", source, 10, "").unwrap(),
        Vec::<String>::new()
    );
}
#[test]
fn contextual_completion_filters_prefix_and_sorts() {
    let c = catalog("root = { beta = scalar alpha = scalar alpine = scalar }");
    assert_eq!(
        c.completion_at("root", "", 0, "al").unwrap(),
        vec!["alpha", "alpine"]
    );
}
#[test]
fn contextual_completion_hides_satisfied_max_cardinality() {
    let c = catalog("root = { one = scalar ## cardinality = 0..2\nmany = scalar }");
    assert_eq!(
        c.completion_at("root", "one = x", 7, "").unwrap(),
        vec!["many"]
    );
}
#[test]
fn contextual_completion_keeps_remaining_cardinality() {
    let c = catalog("root = { ## cardinality = 0..2\nmany = scalar }");
    assert_eq!(
        c.completion_at("root", "many = x", 8, "").unwrap(),
        vec!["many"]
    );
}
#[test]
fn contextual_completion_includes_subtype_direct_children() {
    let c = catalog("root = { subtype[x] = { nested = scalar } ordinary = scalar }");
    assert_eq!(
        c.completion_at("root", "", 0, "").unwrap(),
        vec!["nested", "ordinary"]
    );
}
#[test]
fn contextual_completion_unknown_root_is_empty() {
    assert!(
        catalog("root = { a = scalar }")
            .completion_at("missing", "", 0, "")
            .unwrap()
            .is_empty()
    );
}
#[test]
fn contextual_completion_rejects_offset_past_end() {
    assert_eq!(
        catalog("root = { a = scalar }").completion_at("root", "", 1, ""),
        Err(QueryError::InvalidOffset)
    );
}
#[test]
fn contextual_completion_rejects_unicode_midpoint() {
    assert_eq!(
        catalog("root = { a = scalar }").completion_at("root", "雪", 1, ""),
        Err(QueryError::InvalidOffset)
    );
}
#[test]
fn contextual_completion_accepts_unicode_boundary() {
    assert!(
        catalog("root = { a = scalar }")
            .completion_at("root", "a = 雪", 7, "")
            .is_ok()
    );
}
#[test]
fn contextual_completion_accepts_incomplete_script_loss_aware() {
    assert!(
        catalog("root = { a = { child = scalar } }")
            .completion_at("root", "a = {", 5, "")
            .is_ok()
    );
}
#[test]
fn contextual_info_is_direct_and_case_insensitive() {
    let c = catalog(
        "root = {\n## description = Root detail\nAlpha = scalar\nnode = {\n## description = Child detail\nchild = scalar\n}\n}",
    );
    assert_eq!(
        c.info_at("root", "", 0, "alpha").unwrap().as_deref(),
        Some("Root detail")
    );
}
#[test]
fn contextual_info_does_not_leak_nested_fields_at_root() {
    let c = catalog("root = {\nnode = {\n## description = Child detail\nchild = scalar\n}\n}");
    assert_eq!(c.info_at("root", "", 0, "child").unwrap(), None);
}
#[test]
fn contextual_info_enters_nested_clause() {
    let c = catalog("root = {\nnode = {\n## description = Child detail\nchild = scalar\n}\n}");
    let source = "node = { child = x }";
    assert_eq!(
        c.info_at("root", source, 10, "child").unwrap().as_deref(),
        Some("Child detail")
    );
}
#[test]
fn contextual_completion_unwraps_synthetic_root_clause() {
    let c = catalog("root = { root_field = scalar node = { child = scalar } }");
    let source = "root = {\nnode = {\n\n}\n}";
    assert_eq!(
        c.completion_at("root", source, 18, "").unwrap(),
        vec!["child"]
    );
}
#[test]
fn contextual_info_unwraps_synthetic_root_clause() {
    let c = catalog("root = { node = { ### Child detail\nchild = scalar } }");
    let source = "root = {\nnode = {\nchild = x\n}\n}";
    assert_eq!(
        c.info_at("root", source, 20, "child").unwrap().as_deref(),
        Some(" Child detail")
    );
}
#[test]
fn contextual_info_unknown_field_is_none() {
    assert_eq!(
        catalog("root = { a = scalar }")
            .info_at("root", "", 0, "missing")
            .unwrap(),
        None
    );
}

#[test]
fn contextual_rhs_specific_completion() {
    let c = catalog("root = { mode = enabled }");
    assert_eq!(
        c.completion_at("root", "mode = en", 9, "en").unwrap(),
        vec!["enabled"]
    );
}
#[test]
fn contextual_rhs_specific_excludes_field_names() {
    let c = catalog("root = { mode = enabled other = scalar }");
    assert_eq!(
        c.completion_at("root", "mode = en", 9, "").unwrap(),
        vec!["enabled"]
    );
}
#[test]
fn contextual_rhs_enum_completion_is_sorted_and_filtered() {
    let c =
        catalog("enums = { enum[state] = { zulu alpha alpine } }\nroot = { state = enum[state] }");
    assert_eq!(
        c.completion_at("root", "state = al", 10, "al").unwrap(),
        vec!["alpha", "alpine"]
    );
}
#[test]
fn contextual_rhs_simple_type_completion() {
    let c =
        catalog("types = { type[id] = { value = first value = second } }\nroot = { id = <id> }");
    assert_eq!(
        c.completion_at("root", "id = f", 6, "f").unwrap(),
        vec!["first"]
    );
}
#[test]
fn contextual_rhs_complex_type_completion() {
    let c = catalog("types = { type[id] = { value = first } }\nroot = { id = pre<id>post }");
    assert_eq!(
        c.completion_at("root", "id = pre", 8, "pre").unwrap(),
        vec!["prefirstpost"]
    );
}
#[test]
fn contextual_rhs_unknown_type_is_empty() {
    let c = catalog("root = { id = <missing> }");
    assert!(c.completion_at("root", "id = x", 6, "").unwrap().is_empty());
}
#[test]
fn contextual_completion_loss_aware_unclosed_clause() {
    let c = catalog("root = { node = { child = scalar } }");
    assert_eq!(
        c.completion_at("root", "node = {", 8, "").unwrap(),
        vec!["child"]
    );
}
#[test]
fn contextual_completion_loss_aware_unclosed_nested_clause() {
    let c = catalog("root = { node = { nested = { value = scalar } sibling = scalar } }");
    assert_eq!(
        c.completion_at(
            "root",
            "node = { nested = {",
            "node = { nested = {".len(),
            ""
        )
        .unwrap(),
        vec!["value"]
    );
}
#[test]
fn contextual_completion_loss_aware_stray_close_is_safe() {
    let c = catalog("root = { field = scalar }");
    assert_eq!(c.completion_at("root", "} ", 2, "").unwrap(), vec!["field"]);
}
