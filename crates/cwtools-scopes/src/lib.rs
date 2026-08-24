#![forbid(unsafe_code)]
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::match_wildcard_for_single_variants
)]
use std::collections::BTreeMap;
pub mod game;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReferenceHint {
    Type { type_name: String, value: String },
    Enum { enum_name: String, value: String },
    Localisation(String),
    File(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueScopeEntry {
    pub name: String,
    pub scopes: Vec<String>,
    pub target_scope: Option<String>,
    pub reference_hint: Option<ReferenceHint>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueScopeResolution {
    Reference(ReferenceHint),
    Variable(String),
    StaticValue(String),
    ScopeChange(Option<String>),
    WrongScope { name: String, expected: Vec<String> },
    NotFound,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueScopeCatalogError {
    TooManyEntries { limit: usize },
}

#[derive(Clone, Debug, Default)]
pub struct ValueScopeCatalogInput {
    pub links: Vec<ValueScopeEntry>,
    pub value_triggers: Vec<ValueScopeEntry>,
    pub wildcard_links: Vec<ValueScopeEntry>,
    pub variables: Vec<String>,
    pub static_values: Vec<String>,
    pub variable_prefixes: Vec<(String, bool)>,
    pub jomini: bool,
}

#[derive(Clone, Debug, Default)]
pub struct ValueScopeCatalog {
    links: BTreeMap<String, ValueScopeEntry>,
    value_triggers: BTreeMap<String, ValueScopeEntry>,
    wildcard_links: Vec<ValueScopeEntry>,
    variables: std::collections::BTreeSet<String>,
    static_values: std::collections::BTreeSet<String>,
    variable_prefixes: Vec<(String, bool)>,
    jomini: bool,
}

impl ValueScopeCatalog {
    /// Builds a deterministic, bounded resolver catalog.
    ///
    /// # Errors
    /// Returns an error when all caller-provided catalog entries exceed `max_entries`.
    pub fn build(
        input: ValueScopeCatalogInput,
        max_entries: usize,
    ) -> Result<Self, ValueScopeCatalogError> {
        let mut result = Self {
            jomini: input.jomini,
            ..Self::default()
        };
        let mut count = 0usize;
        for entry in input.links {
            bounded_insert(&mut count, max_entries)?;
            result.links.insert(entry.name.to_ascii_lowercase(), entry);
        }
        for entry in input.value_triggers {
            bounded_insert(&mut count, max_entries)?;
            result
                .value_triggers
                .insert(entry.name.to_ascii_lowercase(), entry);
        }
        for entry in input.wildcard_links {
            bounded_insert(&mut count, max_entries)?;
            result.wildcard_links.push(entry);
        }
        for variable in input.variables {
            bounded_insert(&mut count, max_entries)?;
            result.variables.insert(variable.to_ascii_lowercase());
        }
        for value in input.static_values {
            bounded_insert(&mut count, max_entries)?;
            result.static_values.insert(value.to_ascii_lowercase());
        }
        result.variable_prefixes.extend(input.variable_prefixes);
        result.variable_prefixes.sort_by(|left, right| {
            right
                .0
                .len()
                .cmp(&left.0.len())
                .then_with(|| left.0.cmp(&right.0))
        });
        result.wildcard_links.sort_by(|left, right| {
            right
                .name
                .len()
                .cmp(&left.name.len())
                .then_with(|| left.name.cmp(&right.name))
        });
        Ok(result)
    }

    #[must_use]
    pub fn resolve(&self, raw: &str, current_scope: Option<&str>) -> ValueScopeResolution {
        let mut key = raw.trim().trim_matches('"').split('|').next().unwrap_or("");
        if let Some(rest) = strip_prefix_ignore_case(key, "hidden:") {
            key = rest;
        }
        if key.starts_with('@')
            || starts_ignore_case(key, "parameter:")
            || (self.jomini && starts_ignore_case(key, "event_target:"))
        {
            return ValueScopeResolution::ScopeChange(None);
        }
        let mut variable_only = false;
        for (prefix, only) in &self.variable_prefixes {
            if let Some(rest) = strip_prefix_ignore_case(key, prefix) {
                key = rest;
                variable_only = *only;
                break;
            }
        }
        let parts = split_scope_path(key);
        if parts.is_empty() {
            return ValueScopeResolution::NotFound;
        }
        let mut scope = current_scope.map(str::to_owned);
        for (index, part) in parts.iter().enumerate() {
            let last = index + 1 == parts.len();
            let name = part.strip_suffix('?').unwrap_or(part);
            let lower = name.to_ascii_lowercase();
            if last {
                if let Some(trigger) = self.value_triggers.get(&lower) {
                    return resolve_entry(trigger, scope.as_deref(), true);
                }
            }
            let link = self.links.get(&lower).or_else(|| {
                self.wildcard_links
                    .iter()
                    .find(|entry| starts_ignore_case(name, &entry.name))
            });
            if let Some(link) = link {
                let resolved = resolve_entry(link, scope.as_deref(), last);
                match resolved {
                    ValueScopeResolution::ScopeChange(target) => scope = target.or(scope),
                    ValueScopeResolution::Reference(_)
                    | ValueScopeResolution::WrongScope { .. } => return resolved,
                    ValueScopeResolution::NotFound
                    | ValueScopeResolution::Variable(_)
                    | ValueScopeResolution::StaticValue(_) => {}
                }
                continue;
            }
            if last && self.variables.contains(&lower) {
                return ValueScopeResolution::Variable(name.to_owned());
            }
            if variable_only {
                return ValueScopeResolution::NotFound;
            }
            return if self.static_values.contains(&key.to_ascii_lowercase()) {
                ValueScopeResolution::StaticValue(key.to_owned())
            } else {
                ValueScopeResolution::NotFound
            };
        }
        ValueScopeResolution::ScopeChange(scope)
    }
}

fn bounded_insert(count: &mut usize, limit: usize) -> Result<(), ValueScopeCatalogError> {
    *count = count.saturating_add(1);
    if *count > limit {
        return Err(ValueScopeCatalogError::TooManyEntries { limit });
    }
    Ok(())
}

fn resolve_entry(entry: &ValueScopeEntry, scope: Option<&str>, last: bool) -> ValueScopeResolution {
    if !entry.scopes.is_empty()
        && scope.is_some_and(|scope| {
            !entry
                .scopes
                .iter()
                .any(|item| item.eq_ignore_ascii_case(scope))
        })
    {
        return ValueScopeResolution::WrongScope {
            name: entry.name.clone(),
            expected: entry.scopes.clone(),
        };
    }
    if last {
        if let Some(reference) = &entry.reference_hint {
            return ValueScopeResolution::Reference(reference.clone());
        }
    }
    ValueScopeResolution::ScopeChange(entry.target_scope.clone())
}

fn starts_ignore_case(value: &str, prefix: &str) -> bool {
    value
        .get(..prefix.len())
        .is_some_and(|head| head.eq_ignore_ascii_case(prefix))
}

fn strip_prefix_ignore_case<'a>(value: &'a str, prefix: &str) -> Option<&'a str> {
    starts_ignore_case(value, prefix).then(|| &value[prefix.len()..])
}

fn split_scope_path(value: &str) -> Vec<String> {
    let prefix = value.split_once('@').map_or(value, |(prefix, _)| prefix);
    let mut result = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (index, character) in prefix.char_indices() {
        match character {
            '(' | '[' | '{' => depth = depth.saturating_add(1),
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            '.' if depth == 0 => {
                result.push(prefix[start..index].to_owned());
                start = index + 1;
            }
            _ => {}
        }
    }
    result.push(prefix[start..].to_owned());
    result.into_iter().filter(|part| !part.is_empty()).collect()
}
pub const FIXED_SLOTS: i32 = -1;
#[allow(non_upper_case_globals)]
pub const FixedSlots: i32 = FIXED_SLOTS;
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Scope {
    Named(String),
    Wildcard,
    Unknown(String),
}
impl Scope {
    #[must_use]
    pub fn named(name: impl Into<String>) -> Self {
        Self::Named(name.into())
    }
    #[must_use]
    pub fn unknown(name: impl Into<String>) -> Self {
        Self::Unknown(name.into())
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Resolution {
    Resolved(Scope),
    Wildcard,
    Unknown(String),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScopeContext {
    scopes: Vec<Scope>,
}
impl Default for ScopeContext {
    fn default() -> Self {
        Self::root()
    }
}
impl ScopeContext {
    #[must_use]
    pub fn root() -> Self {
        Self {
            scopes: vec![Scope::Named("ROOT".into())],
        }
    }
    #[must_use]
    pub fn from(scope: Scope) -> Self {
        Self {
            scopes: vec![Scope::Named("ROOT".into()), scope],
        }
    }
    #[must_use]
    pub fn from_depth(depth: usize, scope: Scope) -> Self {
        let mut out = Self::root();
        out.scopes.resize(depth.saturating_add(1), Scope::Wildcard);
        if let Some(last) = out.scopes.last_mut() {
            *last = scope;
        }
        out
    }
    #[must_use]
    pub fn from_depth_stack(scopes: impl IntoIterator<Item = Scope>) -> Self {
        let mut out = scopes.into_iter().collect::<Vec<_>>();
        if out.is_empty() {
            out.push(Scope::Named("ROOT".into()));
        }
        Self { scopes: out }
    }
    #[must_use]
    pub fn scopes(&self) -> &[Scope] {
        &self.scopes
    }
    #[must_use]
    pub fn current(&self) -> Option<&Scope> {
        self.scopes.last()
    }
    pub fn pop(&mut self) -> Option<Scope> {
        if self.scopes.len() > 1 {
            self.scopes.pop()
        } else {
            None
        }
    }
    pub fn push(&mut self, scope: Scope) {
        self.scopes.push(scope);
    }
    pub fn push_reset(&mut self, scope: Scope) {
        self.scopes.truncate(1);
        self.scopes.push(scope);
    }
    pub fn replace_current(&mut self, scope: Scope) {
        if let Some(x) = self.scopes.last_mut() {
            *x = scope
        } else {
            self.scopes.push(scope)
        }
    }
    #[must_use]
    pub fn resolve(&self, path: &str, resolver: &BTreeMap<String, Scope>) -> Resolution {
        let parts = parse_path(path);
        if parts.is_empty() {
            return Resolution::Unknown(path.into());
        }
        let head = parts[0].to_ascii_uppercase();
        let base = match head.as_str() {
            "ROOT" => self.scopes.first().cloned(),
            "THIS" => self.current().cloned(),
            "PREV" | "FROM" => self
                .scopes
                .get(self.scopes.len().saturating_sub(2))
                .cloned(),
            "FROMFROM" => self
                .scopes
                .get(self.scopes.len().saturating_sub(3))
                .cloned(),
            _ => resolver.get(&parts[0]).cloned(),
        };
        let Some(mut value) = base else {
            return Resolution::Unknown(parts[0].clone());
        };
        if matches!(value, Scope::Wildcard) {
            return Resolution::Wildcard;
        }
        for part in parts.iter().skip(1) {
            if part == "*" {
                return Resolution::Wildcard;
            }
            value = match value {
                Scope::Named(parent) => Scope::Named(format!("{parent}.{part}")),
                Scope::Unknown(_) => return Resolution::Unknown(part.clone()),
                Scope::Wildcard => return Resolution::Wildcard,
            }
        }
        match value {
            Scope::Wildcard => Resolution::Wildcard,
            Scope::Unknown(x) => Resolution::Unknown(x),
            x => Resolution::Resolved(x),
        }
    }
}
#[must_use]
pub fn parse_path(path: &str) -> Vec<String> {
    let bounded = &path[..path.len().min(256)];
    let mut result = Vec::new();
    let mut start = 0;
    let mut depth = 0;
    for (i, ch) in bounded.char_indices() {
        match ch {
            '@' if bounded[i..].starts_with("@[") => depth += 1,
            ']' if depth > 0 => depth -= 1,
            '.' if depth == 0 => {
                if i > start {
                    result.push(bounded[start..i].to_owned())
                }
                start = i + 1
            }
            _ => {}
        }
    }
    if start < bounded.len() {
        result.push(bounded[start..].to_owned())
    }
    result
}
#[cfg(test)]
mod tests {
    use super::*;
    fn c() -> ScopeContext {
        ScopeContext::from_depth_stack([Scope::named("ROOT"), Scope::named("A"), Scope::named("B")])
    }
    #[test]
    fn root() {
        assert_eq!(ScopeContext::root().current(), Some(&Scope::named("ROOT")))
    }
    #[test]
    fn from_scope() {
        assert_eq!(ScopeContext::from(Scope::named("X")).scopes().len(), 2)
    }
    #[test]
    fn depth() {
        assert_eq!(
            ScopeContext::from_depth(2, Scope::named("X"))
                .scopes()
                .len(),
            3
        )
    }
    fn entry(name: &str, target: Option<&str>, hint: Option<ReferenceHint>) -> ValueScopeEntry {
        ValueScopeEntry {
            name: name.into(),
            scopes: vec!["country".into()],
            target_scope: target.map(str::to_owned),
            reference_hint: hint,
        }
    }

    #[test]
    fn value_scope_catalog_resolves_links_triggers_variables_and_static_values() {
        let catalog = ValueScopeCatalog::build(
            ValueScopeCatalogInput {
                links: vec![entry("owner", Some("country"), None)],
                value_triggers: vec![entry(
                    "scripted_value",
                    None,
                    Some(ReferenceHint::Type {
                        type_name: "script_value".into(),
                        value: "value_a".into(),
                    }),
                )],
                wildcard_links: vec![entry("event_target:", Some("country"), None)],
                variables: vec!["amount".into()],
                static_values: vec!["static_one".into()],
                variable_prefixes: vec![("variable:".into(), true)],
                jomini: false,
            },
            10,
        )
        .unwrap();
        assert_eq!(
            catalog.resolve("owner.scripted_value", Some("country")),
            ValueScopeResolution::Reference(ReferenceHint::Type {
                type_name: "script_value".into(),
                value: "value_a".into(),
            })
        );
        assert_eq!(
            catalog.resolve("variable:amount", Some("country")),
            ValueScopeResolution::Variable("amount".into())
        );
        assert_eq!(
            catalog.resolve("static_one", Some("country")),
            ValueScopeResolution::StaticValue("static_one".into())
        );
        assert_eq!(
            catalog.resolve("owner.scripted_value|fallback", Some("country")),
            ValueScopeResolution::Reference(ReferenceHint::Type {
                type_name: "script_value".into(),
                value: "value_a".into(),
            })
        );
    }

    #[test]
    fn value_scope_catalog_handles_specials_scope_errors_and_bounds() {
        let catalog = ValueScopeCatalog::build(
            ValueScopeCatalogInput {
                links: vec![entry("owner", Some("country"), None)],
                jomini: true,
                ..ValueScopeCatalogInput::default()
            },
            1,
        )
        .unwrap();
        assert_eq!(
            catalog.resolve("hidden:owner", Some("planet")),
            ValueScopeResolution::WrongScope {
                name: "owner".into(),
                expected: vec!["country".into()],
            }
        );
        assert_eq!(
            catalog.resolve("event_target:foo", Some("country")),
            ValueScopeResolution::ScopeChange(None)
        );
        assert_eq!(
            catalog.resolve("@value", Some("country")),
            ValueScopeResolution::ScopeChange(None)
        );
        assert!(matches!(
            ValueScopeCatalog::build(
                ValueScopeCatalogInput {
                    variables: vec!["a".into(), "b".into()],
                    ..ValueScopeCatalogInput::default()
                },
                1,
            ),
            Err(ValueScopeCatalogError::TooManyEntries { limit: 1 })
        ));
    }

    #[test]
    fn value_scope_path_dots_inside_groups_are_not_split() {
        assert_eq!(
            split_scope_path("owner(func.a).scripted_value@x.y"),
            ["owner(func.a)", "scripted_value"]
        );
    }

    #[test]
    fn stack() {
        assert_eq!(c().scopes().len(), 3)
    }
    #[test]
    fn current() {
        assert_eq!(c().current(), Some(&Scope::named("B")))
    }
    #[test]
    fn pop() {
        let mut x = c();
        assert_eq!(x.pop(), Some(Scope::named("B")))
    }
    #[test]
    fn pop_root() {
        let mut x = ScopeContext::root();
        assert_eq!(x.pop(), None)
    }
    #[test]
    fn push() {
        let mut x = c();
        x.push(Scope::named("C"));
        assert_eq!(x.current(), Some(&Scope::named("C")))
    }
    #[test]
    fn reset() {
        let mut x = c();
        x.push_reset(Scope::named("C"));
        assert_eq!(x.scopes().len(), 2)
    }
    #[test]
    fn replace() {
        let mut x = c();
        x.replace_current(Scope::named("C"));
        assert_eq!(x.current(), Some(&Scope::named("C")))
    }
    #[test]
    fn parse_dots() {
        assert_eq!(parse_path("a.b.c"), ["a", "b", "c"])
    }
    #[test]
    fn parse_brackets() {
        assert_eq!(parse_path("a.@[x.y].z"), ["a", "@[x.y]", "z"])
    }
    #[test]
    fn fixed() {
        assert_eq!(FixedSlots, -1)
    }
    #[test]
    fn resolve_root() {
        assert_eq!(
            c().resolve("ROOT", &BTreeMap::new()),
            Resolution::Resolved(Scope::named("ROOT"))
        )
    }
    #[test]
    fn resolve_this() {
        assert_eq!(
            c().resolve("THIS", &BTreeMap::new()),
            Resolution::Resolved(Scope::named("B"))
        )
    }
    #[test]
    fn resolve_from() {
        assert_eq!(
            c().resolve("FROM", &BTreeMap::new()),
            Resolution::Resolved(Scope::named("A"))
        )
    }
    #[test]
    fn resolve_fromfrom() {
        assert_eq!(
            c().resolve("FROMFROM", &BTreeMap::new()),
            Resolution::Resolved(Scope::named("ROOT"))
        )
    }
    #[test]
    fn resolve_variable() {
        let mut r = BTreeMap::new();
        r.insert("x".into(), Scope::named("X"));
        assert_eq!(
            c().resolve("x.y", &r),
            Resolution::Resolved(Scope::named("X.y"))
        )
    }
    #[test]
    fn resolve_unknown() {
        assert!(matches!(
            c().resolve("nope", &BTreeMap::new()),
            Resolution::Unknown(_)
        ))
    }
    #[test]
    fn resolve_wildcard() {
        assert!(matches!(
            c().resolve("*", &BTreeMap::new()),
            Resolution::Unknown(_)
        ))
    }
    #[test]
    fn cap() {
        assert_eq!(
            parse_path(&"a".repeat(300))
                .iter()
                .map(String::len)
                .sum::<usize>(),
            256
        )
    }
}
