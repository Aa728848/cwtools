use cwtools_process::*;
use cwtools_script_syntax::parse;
use std::collections::BTreeSet;

fn doc(source: &str) -> ProcessedDocument {
    ProcessedDocument::from_cst(&parse(source).unwrap())
}

#[test]
fn scalar_assignments_are_leaves() {
    let d = doc("a=1 b=\"x\"");
    assert_eq!(d.leaves().items.len(), 2);
    assert!(d.nodes().items.is_empty());
}
#[test]
fn clause_assignments_are_nodes() {
    let d = doc("a={ b=1 raw }");
    assert_eq!(d.nodes().items.len(), 1);
    assert_eq!(d.leaves().items.len(), 1);
}
#[test]
fn standalone_values_and_clauses() {
    let d = doc("one { two }");
    assert_eq!(d.leaf_values().items.len(), 2);
    assert_eq!(d.value_clauses().items.len(), 1);
}
#[test]
fn comments_duplicates_order() {
    let d = doc("# c\na=1 a=2");
    assert!(matches!(d.children[0], ProcessedItem::Comment(_)));
    assert_eq!(d.leaves().items.len(), 2);
}
#[test]
fn typed_values() {
    let d = doc("a=1 b=-1.5 c=yes d=\"q\" e=rgb{1 2 3}");
    let x = d.leaves().items;
    assert!(matches!(x[0].value, LeafValue::Integer(1)));
    assert!(matches!(x[1].value, LeafValue::Decimal(_)));
    assert!(matches!(x[2].value, LeafValue::Boolean(true)));
    assert!(matches!(x[3].value, LeafValue::Quoted(_)));
    assert!(matches!(x[4].value, LeafValue::Colour(_)));
}
#[test]
fn canonical_reparse() {
    let d = doc("a={b=1}");
    let reparsed = d.reparse().unwrap();
    assert_eq!(reparsed.to_canonical(), d.to_canonical());
    assert_eq!(reparsed.nodes().items.len(), d.nodes().items.len());
    assert_eq!(reparsed.leaves().items.len(), d.leaves().items.len());
}
#[test]
fn clone_is_independent() {
    let d = doc("a=1");
    let mut c = d.deep_clone();
    if let ProcessedItem::Leaf(x) = &mut c.children[0] {
        x.key = "b".into();
    }
    assert_ne!(d, c);
}
#[test]
fn queries() {
    let d = doc("a={x=1} b=2");
    assert_eq!(d.tag("a").len(), 1);
    assert_eq!(d.tag_text("b"), vec!["2"]);
}
#[test]
fn params_replace_and_default() {
    let p = vec![("$NAME$".into(), "value".into())];
    assert_eq!(
        substitute_params("$NAME$/$MISS|d$/$KEEP$", &p),
        "value/d/$KEEP$"
    );
}
#[test]
fn params_case_sensitive() {
    let p = vec![("Name".into(), "x".into())];
    assert_eq!(substitute_params("$name$", &p), "$name$");
}
#[test]
fn event_targets() {
    let d = doc("root={ a=event_target:foo.bar event_target:baz={x=1} }");
    assert_eq!(
        find_used_targets(&d),
        BTreeSet::from(["baz".into(), "foo".into()])
    );
}
#[test]
fn saved_exists() {
    let d = doc("root={save_event_target_as=one exists=event_target:two?}");
    assert_eq!(find_saved_targets(&d), BTreeSet::from(["one".into()]));
    assert_eq!(find_exists_targets(&d), BTreeSet::from(["two".into()]));
}
#[test]
fn globals() {
    let d = doc("root={save_global_event_target_as=all}");
    assert_eq!(
        find_global_event_targets(&d),
        BTreeSet::from(["all".into()])
    );
}
#[test]
fn actions() {
    let d = doc("fire_on_action={on_action=test other=no}");
    assert_eq!(fired_on_actions(&d), BTreeSet::from(["test".into()]));
}
#[test]
fn categories() {
    assert_eq!(static_modifier_category("ship_fire_rate"), Some("ship"));
    assert_eq!(static_modifier_category("planet_jobs"), Some("planet"));
    assert_eq!(static_modifier_category("other"), None);
}
#[test]
fn bounded() {
    let mut children = Vec::new();
    for _ in 0..=MAX_NODES {
        children.push(ProcessedItem::LeafValue(LeafValue::Integer(1)));
    }
    assert!(ProcessedDocument { children }.leaf_values().truncated);
}
