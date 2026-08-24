use cwtools_rule_ir::{NewField, RootRule, RuleKind, ValueType, parse_document};

fn fixture(path: &str) -> cwtools_rule_ir::Document {
    let source = match path {
        "types" => include_str!(
            "../../../CWToolsTests/testfiles/configtests/rulestests/STL/types/rules.cwt"
        ),
        "enums" => include_str!(
            "../../../CWToolsTests/testfiles/configtests/rulestests/STL/enums/rules.cwt"
        ),
        "aliases" => include_str!(
            "../../../CWToolsTests/testfiles/configtests/rulestests/STL/aliases/rules.cwt"
        ),
        "values" => include_str!(
            "../../../CWToolsTests/testfiles/configtests/rulestests/STL/values/rules.cwt"
        ),
        _ => unreachable!(),
    };
    parse_document(path, source).unwrap_or_else(|errors| panic!("{path}: {errors:?}"))
}

#[test]
fn stl_types_contract() {
    let d = fixture("types");
    assert_eq!(d.types.len(), 13);
    assert_eq!(d.types[0].name, "ship_size");
    assert_eq!(d.types[0].path.as_deref(), Some("game/common/ship_sizes"));
    let per_file = d.types.iter().find(|t| t.name == "type_per_file").unwrap();
    assert!(per_file.type_per_file);
    assert_eq!(per_file.path.as_deref(), Some("game/common/anomalies"));
    assert_eq!(per_file.subtypes[0].name, "subtype_one");
    let one = d.types.iter().find(|t| t.name == "type_one_file").unwrap();
    assert_eq!(one.path_file.as_deref(), Some("one_file.txt"));
    let skip = d
        .types
        .iter()
        .find(|t| t.name == "type_one_file_multiple_skip")
        .unwrap();
    assert_eq!(
        skip.path_file.as_deref(),
        Some("one_file_skip_multiple.txt")
    );
    assert_eq!(skip.skip_root_key, vec!["skip_me_one", "skip_me_two"]);
    assert_eq!(
        d.types
            .iter()
            .find(|t| t.name == "starts_with_c")
            .unwrap()
            .starts_with
            .as_deref(),
        Some("c")
    );
    let event = d.types.iter().find(|t| t.name == "event").unwrap();
    assert_eq!(event.subtypes.len(), 2);
    assert_eq!(event.subtypes[0].name, "ship");
    assert_eq!(event.subtypes[0].push_scope.as_deref(), Some("ship"));
    assert_eq!(event.subtypes[1].name, "country");
    assert_eq!(event.subtypes[1].push_scope.as_deref(), Some("country"));
    assert!(
        d.rules
            .iter()
            .any(|r| matches!(r, RootRule::Alias(name, _) if name == "effect:<ship_size>"))
    );
    assert!(d.rules.iter().any(
        |r| matches!(r, RootRule::Alias(name, _) if name.starts_with("effect:enum[test_enum"))
    ));
}

#[test]
fn stl_complex_enums_contract() {
    let d = fixture("enums");
    assert_eq!(d.complex_enums.len(), 4);
    let single = d
        .complex_enums
        .iter()
        .find(|e| e.name == "singlefile")
        .unwrap();
    assert_eq!(single.path.as_deref(), Some("game/common"));
    assert_eq!(
        single.path_file.as_deref(),
        Some("graphicalculturetype.txt")
    );
    assert!(single.start_from_root);
    assert!(
        single
            .name_tree
            .as_ref()
            .unwrap()
            .iter()
            .any(|r| matches!(r.kind, RuleKind::Leaf { .. }))
    );
    let complex = d
        .complex_enums
        .iter()
        .find(|e| e.name == "complex_path")
        .unwrap();
    assert_eq!(complex.path.as_deref(), Some("game/common"));
    assert!(complex.range.is_some());
    assert_eq!(
        d.complex_enums
            .iter()
            .find(|e| e.name == "top_leaf")
            .unwrap()
            .path
            .as_deref(),
        Some("game/common/anomalies")
    );
    assert!(
        d.rules
            .iter()
            .any(|r| matches!(r, RootRule::Ordinary(name, _) if name == "event"))
    );
}

#[test]
fn stl_single_alias_contract() {
    let d = fixture("aliases");
    let aliases: Vec<_> = d
        .rules
        .iter()
        .filter_map(|r| match r {
            RootRule::Ordinary(_, rule) => Some(rule),
            _ => None,
        })
        .collect();
    assert_eq!(aliases.len(), 1);
    let RuleKind::Node { rules, .. } = &aliases[0].kind else {
        panic!("event must be a node")
    };
    assert_eq!(rules.len(), 3);
    assert!(
        matches!(rules[0].kind, RuleKind::Leaf { right: NewField::SingleAlias(ref n), .. } if n == "single_alias_int")
    );
    assert!(
        matches!(rules[1].kind, RuleKind::Leaf { right: NewField::SingleAlias(ref n), .. } if n == "single_alias_clause")
    );
    assert_eq!((rules[0].options.min, rules[0].options.max), (0, i32::MAX));
    assert_eq!((rules[1].options.min, rules[1].options.max), (0, i32::MAX));
}

#[test]
fn stl_values_contract() {
    let d = fixture("values");
    let names: Vec<_> = d
        .rules
        .iter()
        .filter_map(|r| match r {
            RootRule::Alias(n, _) => Some(n.as_str()),
            _ => None,
        })
        .collect();
    assert!(names.contains(&"effect:int_no_limit"));
    assert!(names.contains(&"effect:date"));
    let find = |name: &str| {
        d.rules
            .iter()
            .find(|r| matches!(r, RootRule::Alias(n, _) if n == name))
            .unwrap()
    };
    let right = |name: &str| match find(name) {
        RootRule::Alias(_, r) => match &r.kind {
            RuleKind::Leaf { right, .. } => right,
            _ => panic!("not leaf"),
        },
        _ => unreachable!(),
    };
    assert!(matches!(
        right("effect:int_inf_upper"),
        NewField::Value(ValueType::Int(-10, i64::MAX))
    ));
    assert!(matches!(
        right("effect:int_inf_lower"),
        NewField::Value(ValueType::Int(i64::MIN, 10))
    ));
    assert!(
        matches!(right("effect:float_fixed_range"), NewField::Value(ValueType::Float(a, b)) if (*a - -5.1).abs() < f64::EPSILON && (*b - 10.1).abs() < f64::EPSILON)
    );
    assert!(matches!(
        right("effect:date"),
        NewField::Value(ValueType::Date)
    ));
    assert!(matches!(
        right("effect:datetime"),
        NewField::Value(ValueType::DateTime)
    ));
    assert!(
        d.directives
            .values()
            .any(|o| o.push_scope.as_deref() == Some("ship"))
    );
}
