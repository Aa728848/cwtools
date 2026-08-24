#![forbid(unsafe_code)]
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::match_wildcard_for_single_variants
)]
use std::collections::BTreeMap;
pub mod game;
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
