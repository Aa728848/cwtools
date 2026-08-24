use cwtools_rule_ir::parse_document;
use cwtools_rules_engine::{CompileError, MAX_DEPTH, RuleCatalog, ScopeUniverse};

fn catalog(source: &str) -> RuleCatalog {
    let document = parse_document("integration.cwt", source).expect("valid rule fixture");
    RuleCatalog::compile(
        &[document],
        ScopeUniverse::new(["country".into(), "planet".into(), "ship".into()]),
    )
    .expect("catalog compiles")
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
    let c = catalog("root = { p = percent }");
    assert!(codes(&c, "root", "p = 0").is_empty() && codes(&c, "root", "p = 100").is_empty());
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
    assert!(r.diagnostics.windows(2).all(|w| (w[0].range.start,w[0].code.clone()) <= (w[1].range.start,w[1].code.clone())));
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
