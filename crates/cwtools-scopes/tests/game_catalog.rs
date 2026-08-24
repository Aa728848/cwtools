use cwtools_scopes::game::*;
use cwtools_scopes::{Scope, ScopeContext};
use std::collections::BTreeMap;

const ALL: [GameScopeFamily; 9] = [
    GameScopeFamily::Ck2,
    GameScopeFamily::Ck3,
    GameScopeFamily::Eu4,
    GameScopeFamily::Eu5,
    GameScopeFamily::Hoi4,
    GameScopeFamily::Imperator,
    GameScopeFamily::Vic2,
    GameScopeFamily::Vic3,
    GameScopeFamily::Stellaris,
];
#[test]
fn exact_catalog_counts() {
    let expected = [
        (14, 11),
        (14, 0),
        (11, 1),
        (14, 0),
        (6, 0),
        (14, 0),
        (14, 0),
        (14, 0),
        (10, 0),
    ];
    for (game, (transitions, effects)) in ALL.into_iter().zip(expected) {
        let c = catalog(game);
        assert_eq!(
            (c.transitions.len(), c.effects.len()),
            (transitions, effects),
            "{game:?}"
        );
    }
}
#[test]
fn each_catalog_has_this_and_root() {
    for game in ALL {
        let c = catalog(game);
        assert_eq!(c.transitions[0].0, "THIS");
        assert_eq!(c.transitions[1].0, "ROOT");
    }
}
#[test]
fn jomini_catalogs_have_deep_from() {
    for game in [
        GameScopeFamily::Ck2,
        GameScopeFamily::Ck3,
        GameScopeFamily::Eu5,
        GameScopeFamily::Imperator,
        GameScopeFamily::Vic2,
        GameScopeFamily::Vic3,
    ] {
        assert!(
            catalog(game)
                .transitions
                .iter()
                .any(|x| x.0 == "ROOT_FROMFROMFROMFROM")
        );
        assert!(
            catalog(game)
                .transitions
                .iter()
                .any(|x| x.0 == "PREVPREVPREV")
        );
    }
}
#[test]
fn eu4_exact_special_keys() {
    let names: Vec<_> = catalog(GameScopeFamily::Eu4)
        .transitions
        .iter()
        .map(|x| x.0)
        .collect();
    assert!(names.contains(&"PREV_PREV"));
    assert!(names.contains(&"NOR"));
    assert!(!names.contains(&"FROMFROM"));
}
#[test]
fn hoi4_exact_special_keys() {
    let names: Vec<_> = catalog(GameScopeFamily::Hoi4)
        .transitions
        .iter()
        .map(|x| x.0)
        .collect();
    assert!(names.contains(&"hidden_effect"));
    assert!(!names.contains(&"PREV_PREV"));
}
#[test]
fn stellaris_exact_relative_keys() {
    let c = catalog(GameScopeFamily::Stellaris);
    assert!(c.transitions.iter().any(|x| x.0 == "FROMFROMFROMFROM"));
    assert!(c.transitions.iter().any(|x| x.0 == "PREVPREVPREVPREV"));
    assert!(!c.transitions.iter().any(|x| x.0 == "ROOT_FROM"));
}
#[test]
fn ck2_effects_are_exact() {
    let c = catalog(GameScopeFamily::Ck2);
    assert_eq!(
        c.effects[0],
        ScopedEffect {
            key: "primary_title",
            from: &["Character"],
            to: "Title"
        }
    );
    assert_eq!(
        c.effects[10],
        ScopedEffect {
            key: "owner",
            from: &["Province"],
            to: "Character"
        }
    );
}
#[test]
fn eu4_owner_effect_is_exact() {
    assert_eq!(
        catalog(GameScopeFamily::Eu4).effects,
        [ScopedEffect {
            key: "owner",
            from: &["province"],
            to: "country"
        }]
    );
}
fn context() -> ScopeContext {
    ScopeContext::from_depth_stack([
        Scope::named("Root"),
        Scope::named("From"),
        Scope::named("Current"),
    ])
}
#[test]
fn root_transition_pushes_root() {
    assert_eq!(
        change_scope(GameScopeFamily::Ck3, &context(), "ROOT")
            .unwrap()
            .current(),
        Some(&Scope::named("Root"))
    );
}
#[test]
fn from_transition_uses_previous() {
    assert_eq!(
        change_scope(GameScopeFamily::Ck3, &context(), "FROM")
            .unwrap()
            .current(),
        Some(&Scope::named("From"))
    );
}
#[test]
fn prev_transition_pops_current() {
    assert_eq!(
        change_scope(GameScopeFamily::Ck3, &context(), "PREV")
            .unwrap()
            .current(),
        Some(&Scope::named("From"))
    );
}
#[test]
fn eu4_identity_logic_key() {
    assert_eq!(
        change_scope(GameScopeFamily::Eu4, &context(), "AND")
            .unwrap()
            .current(),
        Some(&Scope::named("Current"))
    );
}
#[test]
fn hoi4_rejects_deep_from() {
    assert!(change_scope(GameScopeFamily::Hoi4, &context(), "FROMFROM").is_none());
}
#[test]
fn stl_source_scope_strips_hidden_and_optional() {
    let effects = BTreeMap::from([("owner".into(), vec![Scope::named("Country")])]);
    assert_eq!(
        source_scope(GameScopeFamily::Stellaris, &effects, "hidden:ROOT.owner?"),
        vec![Scope::named("Country")]
    );
}
#[test]
fn stl_source_scope_case_insensitive() {
    let effects = BTreeMap::from([("owner".into(), vec![Scope::named("Country")])]);
    assert_eq!(
        source_scope(GameScopeFamily::Stellaris, &effects, "OWNER"),
        vec![Scope::named("Country")]
    );
}
#[test]
fn stl_source_scope_unknown_is_wildcard() {
    assert_eq!(
        source_scope(GameScopeFamily::Stellaris, &BTreeMap::new(), "missing"),
        vec![Scope::Wildcard]
    );
}
#[test]
fn non_stl_source_scope_is_empty() {
    assert!(source_scope(GameScopeFamily::Eu4, &BTreeMap::new(), "owner").is_empty());
}
