//! Exact built-in scope-switch catalogs from the supported game adapters.
use crate::{Scope, ScopeContext};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GameScopeFamily {
    Ck2,
    Ck3,
    Eu4,
    Eu5,
    Hoi4,
    Imperator,
    Vic2,
    Vic3,
    Stellaris,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Transition {
    Identity,
    Root,
    From(usize),
    Prev(usize),
    RootFrom(usize),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScopedEffect {
    pub key: &'static str,
    pub from: &'static [&'static str],
    pub to: &'static str,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScopeCatalog {
    pub transitions: &'static [(&'static str, Transition)],
    pub effects: &'static [ScopedEffect],
    pub variable_prefix: &'static str,
}

const JOMINI: &[(&str, Transition)] = &[
    ("THIS", Transition::Identity),
    ("ROOT", Transition::Root),
    ("ROOT_FROM", Transition::RootFrom(1)),
    ("ROOT_FROMFROM", Transition::RootFrom(2)),
    ("ROOT_FROMFROMFROM", Transition::RootFrom(3)),
    ("ROOT_FROMFROMFROMFROM", Transition::RootFrom(4)),
    ("FROM", Transition::From(1)),
    ("FROMFROM", Transition::From(2)),
    ("FROMFROMFROM", Transition::From(3)),
    ("FROMFROMFROMFROM", Transition::From(4)),
    ("PREV", Transition::Prev(1)),
    ("PREVPREV", Transition::Prev(2)),
    ("PREVPREVPREV", Transition::Prev(3)),
    ("PREVPREVPREVPREV", Transition::Prev(4)),
];
const EU4: &[(&str, Transition)] = &[
    ("THIS", Transition::Identity),
    ("ROOT", Transition::Root),
    ("FROM", Transition::From(1)),
    ("PREV", Transition::Prev(1)),
    ("PREV_PREV", Transition::Prev(2)),
    ("AND", Transition::Identity),
    ("OR", Transition::Identity),
    ("NOR", Transition::Identity),
    ("NOT", Transition::Identity),
    ("hidden_effect", Transition::Identity),
    ("hidden_trigger", Transition::Identity),
];
const HOI4: &[(&str, Transition)] = &[
    ("THIS", Transition::Identity),
    ("ROOT", Transition::Root),
    ("FROM", Transition::From(1)),
    ("PREV", Transition::Prev(1)),
    ("hidden_effect", Transition::Identity),
    ("hidden_trigger", Transition::Identity),
];
const STL: &[(&str, Transition)] = &[
    ("THIS", Transition::Identity),
    ("ROOT", Transition::Root),
    ("FROM", Transition::From(1)),
    ("FROMFROM", Transition::From(2)),
    ("FROMFROMFROM", Transition::From(3)),
    ("FROMFROMFROMFROM", Transition::From(4)),
    ("PREV", Transition::Prev(1)),
    ("PREVPREV", Transition::Prev(2)),
    ("PREVPREVPREV", Transition::Prev(3)),
    ("PREVPREVPREVPREV", Transition::Prev(4)),
];
const CK2_EFFECTS: &[ScopedEffect] = &[
    ScopedEffect {
        key: "primary_title",
        from: &["Character"],
        to: "Title",
    },
    ScopedEffect {
        key: "mother",
        from: &["Character"],
        to: "Character",
    },
    ScopedEffect {
        key: "mother_even_if_dead",
        from: &["Character"],
        to: "Character",
    },
    ScopedEffect {
        key: "father",
        from: &["Character"],
        to: "Character",
    },
    ScopedEffect {
        key: "father_even_if_dead",
        from: &["Character"],
        to: "Character",
    },
    ScopedEffect {
        key: "killer",
        from: &["Character"],
        to: "Character",
    },
    ScopedEffect {
        key: "liege",
        from: &["Character"],
        to: "Character",
    },
    ScopedEffect {
        key: "liege_before_war",
        from: &["Character"],
        to: "Character",
    },
    ScopedEffect {
        key: "top_liege",
        from: &["Character"],
        to: "Character",
    },
    ScopedEffect {
        key: "capital_scope",
        from: &["Character", "Title"],
        to: "Province",
    },
    ScopedEffect {
        key: "owner",
        from: &["Province"],
        to: "Character",
    },
];
const EU4_EFFECTS: &[ScopedEffect] = &[ScopedEffect {
    key: "owner",
    from: &["province"],
    to: "country",
}];
const EMPTY: &[ScopedEffect] = &[];

#[must_use]
pub const fn catalog(game: GameScopeFamily) -> ScopeCatalog {
    match game {
        GameScopeFamily::Ck2 => ScopeCatalog {
            transitions: JOMINI,
            effects: CK2_EFFECTS,
            variable_prefix: "variable:",
        },
        GameScopeFamily::Eu4 => ScopeCatalog {
            transitions: EU4,
            effects: EU4_EFFECTS,
            variable_prefix: "variable:",
        },
        GameScopeFamily::Hoi4 => ScopeCatalog {
            transitions: HOI4,
            effects: EMPTY,
            variable_prefix: "var:",
        },
        GameScopeFamily::Stellaris => ScopeCatalog {
            transitions: STL,
            effects: EMPTY,
            variable_prefix: "var:",
        },
        GameScopeFamily::Ck3
        | GameScopeFamily::Eu5
        | GameScopeFamily::Imperator
        | GameScopeFamily::Vic2
        | GameScopeFamily::Vic3 => ScopeCatalog {
            transitions: JOMINI,
            effects: EMPTY,
            variable_prefix: "variable:",
        },
    }
}

#[must_use]
pub fn apply_transition(context: &ScopeContext, transition: Transition) -> ScopeContext {
    let mut next = context.clone();
    match transition {
        Transition::Identity => {}
        Transition::Root => {
            let root = next.scopes().first().cloned().unwrap_or(Scope::Wildcard);
            next.push(root);
        }
        Transition::From(depth) => {
            let index = next.scopes().len().saturating_sub(depth + 1);
            let scope = next.scopes().get(index).cloned().unwrap_or(Scope::Wildcard);
            next.push(scope);
        }
        Transition::Prev(depth) => {
            for _ in 0..depth {
                let _ = next.pop();
            }
        }
        Transition::RootFrom(depth) => {
            let root = next.scopes().first().cloned().unwrap_or(Scope::Wildcard);
            next.push(root);
            let index = next.scopes().len().saturating_sub(depth + 1);
            let scope = next.scopes().get(index).cloned().unwrap_or(Scope::Wildcard);
            next.push(scope);
        }
    }
    next
}

#[must_use]
pub fn change_scope(
    game: GameScopeFamily,
    context: &ScopeContext,
    key: &str,
) -> Option<ScopeContext> {
    catalog(game)
        .transitions
        .iter()
        .find(|(name, _)| *name == key)
        .map(|(_, transition)| apply_transition(context, *transition))
}

#[must_use]
pub fn source_scope(
    game: GameScopeFamily,
    effects: &BTreeMap<String, Vec<Scope>>,
    key: &str,
) -> Vec<Scope> {
    if game != GameScopeFamily::Stellaris {
        return Vec::new();
    }
    let raw = key
        .strip_prefix("hidden:")
        .or_else(|| key.strip_prefix("HIDDEN:"))
        .unwrap_or(key);
    for part in raw.split('.') {
        let part = part.strip_suffix('?').unwrap_or(part);
        if catalog(game)
            .transitions
            .iter()
            .any(|(name, _)| name.eq_ignore_ascii_case(part))
        {
            continue;
        }
        if let Some((_, scopes)) = effects
            .iter()
            .find(|(name, _)| name.eq_ignore_ascii_case(part))
        {
            return scopes.clone();
        }
    }
    vec![Scope::Wildcard]
}
