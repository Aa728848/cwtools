use cwtools_script_syntax::{parse, print_canonical};

#[test]
fn contract_simple() {
    let source = "key = value\nlabel = {\n\tvaluea\n\tvalueb\n}\n";
    let parsed = parse(source).expect("fixture should parse");
    assert_eq!(
        print_canonical(&parsed),
        "key = value\nlabel = {\n\tvaluea\n\tvalueb\n}\n"
    );
}

#[test]
fn contract_unicode() {
    let source =
        "中文键 = 中文值\ninline_script = { script = districts/精灵服务区划岗位添加（无海军） }";
    let parsed = parse(source).expect("fixture should parse");
    assert!(!parsed.tokens.is_empty());
}

#[test]
fn contract_int64() {
    let source = "@large = 80000000000000";
    let parsed = parse(source).expect("fixture should parse");
    assert!(!parsed.tokens.is_empty());
}

#[test]
fn contract_duplicate_order() {
    let source = "create_starbase = { owner = this owner = this size = large }";
    let parsed = parse(source).expect("fixture should parse");
    assert!(!parsed.tokens.is_empty());
}

#[test]
fn contract_quoted_values() {
    let source = "test_event = { effect = { create_species = { name = \"from\" name = from name = \"Local Name\" traits = { ideal_planet_class = \"from\" } } } }";
    let parsed = parse(source).expect("fixture should parse");
    assert!(!parsed.tokens.is_empty());
}

#[test]
fn contract_empty_blocks() {
    let source = "can_declare_war = {} can_declar_war = {} on_game_start = {} on_gamestart = {}";
    let parsed = parse(source).expect("fixture should parse");
    assert!(!parsed.tokens.is_empty());
}

#[test]
fn contract_unclosed() {
    let source = "x = { y = \"unterminated";
    assert!(parse(source).is_err());
}
