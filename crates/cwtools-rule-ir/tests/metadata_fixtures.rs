use cwtools_rule_ir::{RootRule, parse_document};

// Synthetic aggregate fixtures shaped after CwtProjectIndex/CwtLanguage schema
// examples; these are not claimed to be repository files.
fn fixture() -> cwtools_rule_ir::Document {
    parse_document(
        "synthetic-schema.cwt",
        r#"
priorities = { "common/α" = FIOS "common/α" = LIOS }
override_modes_info = { LIOS = { name = "Last In" nested = { label = "深い" } } }
system_scopes = { country = { base_id = scope display = "国家" } }
locales = { l_日本語 = { supports = yes codes = { ja 日本語 } } }
database_object_types = { law = { type = law swap_type = institution } }
on_actions = { on_test = { event_type = country hint = "Country only" } }
ordinary_rule = { value = scalar }
"#,
    )
    .unwrap()
}

#[test]
fn all_six_root_sections_are_metadata() {
    let d = fixture();
    assert_eq!(d.metadata.sections.len(), 6);
    assert_eq!(d.metadata.priorities.len(), 2);
    assert!(d.metadata.override_modes_info.contains_key("LIOS"));
    assert!(d.metadata.system_scopes.contains_key("country"));
    assert!(d.metadata.locales.contains_key("l_日本語"));
    assert!(d.metadata.database_object_types.contains_key("law"));
    assert!(d.metadata.on_actions.contains_key("on_test"));
}

#[test]
fn typed_entries_keep_keys_values_and_nested_fields() {
    let d = fixture();
    let mode = &d.metadata.override_modes_info["LIOS"];
    assert_eq!(mode.key, "LIOS");
    assert_eq!(mode.value, None);
    assert_eq!(mode.fields["name"], "Last In");
    assert_eq!(mode.fields["nested.label"], "深い");
    assert!(mode.range.is_some());
    assert!(!mode.value_ranges.is_empty());
}

#[test]
fn quoted_and_unicode_keys_are_lossless() {
    let d = fixture();
    let locale = &d.metadata.locales["l_日本語"];
    assert_eq!(locale.key, "l_日本語");
    assert_eq!(locale.fields["supports"], "yes");
    assert!(!locale.fields.is_empty());
    assert!(locale.fields.values().any(|value| value.contains("yes")));
    assert!(locale.range.unwrap().start < locale.range.unwrap().end);
}

#[test]
fn duplicate_priorities_are_preserved_deterministically() {
    let d = fixture();
    assert_eq!(d.metadata.priorities[0].key, "common/α");
    assert_eq!(d.metadata.priorities[0].value.as_deref(), Some("FIOS"));
    assert_eq!(d.metadata.priorities[1].value.as_deref(), Some("LIOS"));
    assert!(d.metadata.raw_ranges["priorities"].len() >= 3);
}

#[test]
fn raw_ranges_cover_root_and_children() {
    let d = fixture();
    for name in [
        "priorities",
        "override_modes_info",
        "system_scopes",
        "locales",
        "database_object_types",
        "on_actions",
    ] {
        let ranges = &d.metadata.raw_ranges[name];
        assert!(!ranges.is_empty());
        assert!(ranges.windows(2).all(|w| w[0].start <= w[1].start));
    }
}

#[test]
fn ordinary_rules_do_not_enter_metadata() {
    // This shape mirrors the ordinary entries in CWToolsDocs common/on_actions.cwt,
    // without claiming that file is an aggregate metadata fixture.
    let d = parse_document(
        "common/on_actions.cwt",
        "on_daily = { effect = scalar }
ordinary = scalar",
    )
    .unwrap();
    assert!(d.metadata.sections.is_empty());
    assert_eq!(d.rules.len(), 2);
    assert!(d.rules.iter().all(|r| matches!(r, RootRule::Ordinary(..))));
}
