use cwtools_docs::{parse_docs_bytes, parse_modifiers_bytes};
use std::fs;
use std::path::PathBuf;

fn fixture(name: &str) -> Vec<u8> {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("../../fixtures/testfiles/parsertests/stellarisnewdocs");
    path.push(name);
    fs::read(path).unwrap()
}

#[test]
fn parses_modifier_reference_count() {
    let entries = parse_modifiers_bytes(&fixture("modifiers.log")).unwrap();
    assert_eq!(entries.len(), 4_639);
}

#[test]
fn parses_both_documentation_fixtures() {
    for name in ["trigger_docs.log", "trigger_docs_long.log"] {
        let docs = parse_docs_bytes(&fixture(name)).unwrap();
        assert!(!docs.triggers.is_empty(), "{name} trigger section");
        assert!(!docs.effects.is_empty(), "{name} effect section");
    }
}
