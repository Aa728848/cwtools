#![forbid(unsafe_code)]

use cwtools_rule_ir::{self as ir, NewField, NewRule, RootRule, RuleKind, ValueType};
use cwtools_script_syntax::{self as syntax, ByteRange, CstNode};
use std::collections::{BTreeMap, BTreeSet};

pub const MAX_RULES: usize = 100_000;
pub const MAX_DEPTH: usize = 256;

struct CancelCheck<'a> {
    check: &'a mut dyn FnMut() -> bool,
    cancelled: bool,
}
impl CancelCheck<'_> {
    fn poll(&mut self) -> bool {
        if !self.cancelled && (self.check)() {
            self.cancelled = true;
        }
        self.cancelled
    }
}

#[derive(Clone, Debug, Default)]
struct ScopeFrame {
    root: Option<String>,
    current: Option<String>,
    froms: Vec<String>,
    prevs: Vec<String>,
}
impl ScopeFrame {
    fn apply(&self, options: &ir::Options) -> Self {
        if let Some(scope) = &options.push_scope {
            let mut next = self.clone();
            if let Some(current) = &self.current {
                next.prevs.insert(0, current.clone());
            }
            next.current = Some(scope.clone());
            return next;
        }
        let mut next = self.clone();
        if let Some(r) = &options.replace_scopes {
            if r.root.is_some() {
                next.root.clone_from(&r.root);
            }
            if r.this.is_some() {
                next.current.clone_from(&r.this);
            }
            if let Some(froms) = &r.froms {
                next.froms.clone_from(froms);
            }
            if let Some(prevs) = &r.prevs {
                next.prevs.clone_from(prevs);
            }
        }
        next
    }
    fn resolves_keyword_to_allowed(&self, raw: &str, allowed: &[String]) -> bool {
        let scope = if raw.eq_ignore_ascii_case("this") {
            self.current.as_deref()
        } else if raw.eq_ignore_ascii_case("root") {
            self.root.as_deref()
        } else {
            let lower = raw.to_ascii_lowercase();
            if lower.starts_with("from")
                && lower[4..].len() % 4 == 0
                && lower.as_bytes()[4..].chunks(4).all(|part| part == b"from")
            {
                self.froms.get(lower[4..].len() / 4).map(String::as_str)
            } else if lower.starts_with("prev")
                && lower[4..].len() % 4 == 0
                && lower.as_bytes()[4..].chunks(4).all(|part| part == b"prev")
            {
                self.prevs.get(lower[4..].len() / 4).map(String::as_str)
            } else {
                None
            }
        };
        scope.is_some_and(|scope| allowed.iter().any(|item| item.eq_ignore_ascii_case(scope)))
    }

    fn allows(&self, raw: &str, universe: &ScopeUniverse) -> bool {
        [self.root.as_deref(), self.current.as_deref()]
            .into_iter()
            .flatten()
            .any(|x| x.eq_ignore_ascii_case(raw))
            || self
                .froms
                .iter()
                .chain(&self.prevs)
                .any(|x| x.eq_ignore_ascii_case(raw))
            || (self.current.is_none()
                && universe.names.iter().any(|x| x.eq_ignore_ascii_case(raw)))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ScopeUniverse {
    pub names: BTreeSet<String>,
}
impl ScopeUniverse {
    pub fn new(names: impl IntoIterator<Item = String>) -> Self {
        Self {
            names: names.into_iter().collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: String,
    pub message_key: String,
    pub key: String,
    pub args: Vec<String>,
    pub range: ByteRange,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedReference {
    pub type_name: String,
    pub value: String,
    pub range: ByteRange,
    pub is_outgoing: bool,
    pub reference_label: Option<String>,
    pub fuzzy: bool,
    pub associated_type: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DynamicTypeReference {
    pub type_name: String,
    pub value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SubtypeScopeTransition {
    Push(String),
    Replace(ir::ReplaceScopes),
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct TypeSubtypeMatch {
    pub names: Vec<String>,
    pub scope: Option<SubtypeScopeTransition>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleVariableSet {
    pub kind: String,
    pub value: String,
    pub range: ByteRange,
    pub scope: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct RuleComputedData {
    pub variable_sets: Vec<RuleVariableSet>,
    pub effect_blocks: Vec<ByteRange>,
    pub trigger_blocks: Vec<ByteRange>,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ValidationResult {
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValidationOutcome {
    Completed(ValidationResult),
    Cancelled,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QueryError {
    InvalidOffset,
    ParseFailed,
    TooManyResults,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    TooManyRules,
    TooDeep,
    DuplicateRoot(String),
    UnknownScope(String),
}

#[derive(Clone, Debug)]
pub struct RuleCatalog {
    ordinary: BTreeMap<String, NewRule>,
    aliases: BTreeMap<String, NewRule>,
    single: BTreeMap<String, NewRule>,
    types: BTreeMap<String, Vec<NewRule>>,
    enums: BTreeMap<String, BTreeSet<String>>,
    scopes: ScopeUniverse,
}
impl RuleCatalog {
    /// Compiles rule documents into a catalog.
    ///
    /// # Errors
    ///
    /// Returns an error when the catalog exceeds the configured rule or depth
    /// limits, or when duplicate ordinary root rules are encountered.
    pub fn compile(
        documents: &[ir::Document],
        scopes: ScopeUniverse,
    ) -> Result<Self, CompileError> {
        Self::compile_with_limit(documents, scopes, MAX_RULES)
    }

    fn compile_with_limit(
        documents: &[ir::Document],
        scopes: ScopeUniverse,
        limit: usize,
    ) -> Result<Self, CompileError> {
        let mut c = Self {
            ordinary: BTreeMap::new(),
            aliases: BTreeMap::new(),
            single: BTreeMap::new(),
            types: BTreeMap::new(),
            enums: BTreeMap::new(),
            scopes,
        };
        let mut count = 0;
        for d in documents {
            for r in &d.rules {
                count += 1;
                if count > limit {
                    return Err(CompileError::TooManyRules);
                }
                let (map, name, x) = match r {
                    RootRule::Ordinary(n, x) => (0, n, x),
                    RootRule::Alias(n, x) => (1, n, x),
                    RootRule::SingleAlias(n, x) => (2, n, x),
                    RootRule::Type(n, x) => (3, n, x),
                };
                let n = name.to_ascii_lowercase();
                if map == 0 && c.ordinary.insert(n.clone(), x.clone()).is_some() {
                    return Err(CompileError::DuplicateRoot(name.clone()));
                }
                if map == 1 {
                    c.aliases.insert(n.clone(), x.clone());
                }
                if map == 2 {
                    c.single.insert(n.clone(), x.clone());
                }
                if map == 3 {
                    c.types.entry(n).or_default().push(x.clone());
                }
                validate_rule_scope_options(x, &c.scopes)?;
                count_rules(&x.kind, &mut count, limit, 0)?;
            }
            for t in &d.types {
                let entry = c.types.entry(t.name.to_ascii_lowercase()).or_default();
                entry.extend(t.rules.iter().cloned());
                for subtype in &t.subtypes {
                    entry.extend(subtype.rules.iter().cloned());
                }
            }
            for e in &d.enums {
                c.enums
                    .entry(e.key.to_ascii_lowercase())
                    .or_default()
                    .extend(e.values.iter().cloned());
            }
        }
        Ok(c)
    }
    #[must_use]
    pub fn validate_source(&self, root_rule_name: &str, source: &str) -> ValidationResult {
        match self.validate_source_cancellable(root_rule_name, source, None, || false) {
            ValidationOutcome::Completed(result) => result,
            ValidationOutcome::Cancelled => ValidationResult::default(),
        }
    }

    #[must_use]
    pub fn validate_source_cancellable<F>(
        &self,
        root_rule_name: &str,
        source: &str,
        initial_scope: Option<&str>,
        mut should_cancel: F,
    ) -> ValidationOutcome
    where
        F: FnMut() -> bool,
    {
        if should_cancel() {
            return ValidationOutcome::Cancelled;
        }
        let mut cancel = CancelCheck {
            check: &mut should_cancel,
            cancelled: false,
        };
        match self.validate_source_with_scope_inner(
            root_rule_name,
            source,
            initial_scope,
            &mut cancel,
        ) {
            Some(result) => ValidationOutcome::Completed(result),
            None => ValidationOutcome::Cancelled,
        }
    }
    #[must_use]
    pub fn validate_source_with_scope(
        &self,
        root_rule_name: &str,
        source: &str,
        initial_scope: Option<&str>,
    ) -> ValidationResult {
        let mut never = || false;
        let mut cancel = CancelCheck {
            check: &mut never,
            cancelled: false,
        };
        self.validate_source_with_scope_inner(root_rule_name, source, initial_scope, &mut cancel)
            .unwrap_or_default()
    }
    fn validate_source_with_scope_inner(
        &self,
        root_rule_name: &str,
        source: &str,
        initial_scope: Option<&str>,
        cancel: &mut CancelCheck<'_>,
    ) -> Option<ValidationResult> {
        if cancel.poll() {
            return None;
        }
        let mut out = ValidationResult::default();
        let Ok(cst) = syntax::parse(source) else {
            out.diagnostics.push(Diagnostic {
                code: "RULE001".into(),
                message_key: diagnostic_message_key("RULE001").into(),
                key: root_rule_name.into(),
                args: vec![],
                range: ByteRange {
                    start: 0,
                    end: source.len(),
                },
            });
            return Some(out);
        };
        let Some(rule) = self.find(root_rule_name) else {
            out.diagnostics.push(diag(
                "RULE130",
                root_rule_name,
                ByteRange { start: 0, end: 0 },
                vec![],
            ));
            return Some(out);
        };
        let mut ctx = BTreeSet::new();
        let frame = initial_scope
            .map(|scope| ScopeFrame {
                root: Some(scope.into()),
                current: Some(scope.into()),
                ..Default::default()
            })
            .unwrap_or_default();
        for required in &rule.options.required_scopes {
            if cancel.poll() {
                return None;
            }
            let ok = frame
                .current
                .as_deref()
                .is_some_and(|scope| scope.eq_ignore_ascii_case(required))
                || (frame.current.is_none()
                    && self
                        .scopes
                        .names
                        .iter()
                        .any(|scope| scope.eq_ignore_ascii_case(required)));
            if !ok {
                out.diagnostics.push(diag(
                    "RULE140",
                    required,
                    ByteRange {
                        start: 0,
                        end: source.len(),
                    },
                    vec![required.clone()],
                ));
            }
        }
        self.validate_nodes(
            &rule.kind, &cst.roots, &mut out, &mut ctx, 0, &frame, cancel,
        );
        if cancel.cancelled {
            return None;
        }
        out.diagnostics.sort_by(|a, b| {
            (a.range.start, a.range.end, a.code.as_str(), a.key.as_str()).cmp(&(
                b.range.start,
                b.range.end,
                b.code.as_str(),
                b.key.as_str(),
            ))
        });
        Some(out)
    }
    /// Extracts only scalar references selected by the active rule path.
    ///
    /// # Errors
    /// Returns [`QueryError::ParseFailed`] for malformed source or
    /// [`QueryError::TooManyResults`] when the caller-provided bound is exceeded.
    pub fn typed_references(
        &self,
        root: &str,
        source: &str,
        max_results: usize,
    ) -> Result<Vec<TypedReference>, QueryError> {
        self.typed_references_with(root, source, max_results, |_, _| None)
    }

    /// Extracts exact, fuzzy and value-scope dynamic references from active rules.
    ///
    /// # Errors
    /// Returns [`QueryError::ParseFailed`] for malformed source or
    /// [`QueryError::TooManyResults`] when the caller-provided bound is exceeded.
    pub fn typed_references_with<F>(
        &self,
        root: &str,
        source: &str,
        max_results: usize,
        mut resolve_value_scope: F,
    ) -> Result<Vec<TypedReference>, QueryError>
    where
        F: FnMut(&str, Option<&str>) -> Option<DynamicTypeReference>,
    {
        let cst = syntax::parse(source).map_err(|_| QueryError::ParseFailed)?;
        let Some(root_rule) = self.find(root) else {
            return Ok(Vec::new());
        };
        let mut result = Vec::new();
        let mut seen = BTreeSet::new();
        let mut never = || false;
        let mut cancel = CancelCheck {
            check: &mut never,
            cancelled: false,
        };
        self.collect_typed_references(
            &root_rule.kind,
            &cst.roots,
            &mut result,
            max_results,
            &mut seen,
            0,
            &ScopeFrame::default(),
            &mut cancel,
            &mut resolve_value_scope,
        )?;
        result.sort_by(|left, right| {
            (
                left.range.start,
                left.range.end,
                &left.type_name,
                &left.value,
                left.is_outgoing,
                &left.reference_label,
                left.fuzzy,
                &left.associated_type,
            )
                .cmp(&(
                    right.range.start,
                    right.range.end,
                    &right.type_name,
                    &right.value,
                    right.is_outgoing,
                    &right.reference_label,
                    right.fuzzy,
                    &right.associated_type,
                ))
        });
        result.dedup();
        Ok(result)
    }

    /// Extracts variable sets and effect/trigger blocks from active rules.
    ///
    /// # Errors
    /// Returns [`QueryError::ParseFailed`] for malformed source or
    /// [`QueryError::TooManyResults`] when the shared bound is exceeded.
    pub fn computed_data(
        &self,
        root: &str,
        source: &str,
        max_results: usize,
    ) -> Result<RuleComputedData, QueryError> {
        let cst = syntax::parse(source).map_err(|_| QueryError::ParseFailed)?;
        let Some(root_rule) = self.find(root) else {
            return Ok(RuleComputedData::default());
        };
        let mut result = RuleComputedData::default();
        let mut seen = BTreeSet::new();
        let mut never = || false;
        let mut cancel = CancelCheck {
            check: &mut never,
            cancelled: false,
        };
        self.collect_rule_computed_data(
            &root_rule.kind,
            &cst.roots,
            &mut result,
            max_results,
            &mut seen,
            0,
            &ScopeFrame::default(),
            &mut cancel,
        )?;
        result.variable_sets.sort_by(|left, right| {
            (
                left.range.start,
                left.range.end,
                &left.kind,
                &left.value,
                &left.scope,
            )
                .cmp(&(
                    right.range.start,
                    right.range.end,
                    &right.kind,
                    &right.value,
                    &right.scope,
                ))
        });
        result.variable_sets.dedup();
        result
            .effect_blocks
            .sort_by_key(|range| (range.start, range.end));
        result.effect_blocks.dedup();
        result
            .trigger_blocks
            .sort_by_key(|range| (range.start, range.end));
        result.trigger_blocks.dedup();
        Ok(result)
    }

    /// Applies a type definition's subtype selectors and full rule validation.
    ///
    /// This mirrors F# `testSubtype`: selector filters run before the rule probe,
    /// subtypes whose diagnostics are only missing-cardinality remain applicable,
    /// and `only_if_not` is evaluated against the complete pre-filter match set.
    ///
    /// # Errors
    /// Returns [`QueryError::ParseFailed`] for malformed source.
    pub fn apply_type_subtypes(
        &self,
        type_definition: &ir::TypeDefinition,
        key: &str,
        source: &str,
    ) -> Result<TypeSubtypeMatch, QueryError> {
        let cst = syntax::parse(source).map_err(|_| QueryError::ParseFailed)?;
        let mut candidates = Vec::new();
        let mut never = || false;
        let mut cancel = CancelCheck {
            check: &mut never,
            cancelled: false,
        };
        for subtype in &type_definition.subtypes {
            if !subtype_selector_matches(subtype, key) {
                continue;
            }
            let probe_kind = RuleKind::Node {
                left: NewField::Specific("__subtype_probe".into()),
                rules: subtype.rules.clone(),
            };
            let mut probe = ValidationResult::default();
            let mut seen = BTreeSet::new();
            self.validate_nodes(
                &probe_kind,
                &cst.roots,
                &mut probe,
                &mut seen,
                0,
                &ScopeFrame::default(),
                &mut cancel,
            );
            if probe
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code == "RULE101")
            {
                candidates.push(subtype);
            }
        }
        let names = candidates
            .iter()
            .filter(|subtype| {
                !subtype.only_if_not.iter().any(|excluded| {
                    candidates
                        .iter()
                        .any(|matched| matched.name.eq_ignore_ascii_case(excluded))
                })
            })
            .map(|subtype| subtype.name.clone())
            .collect::<Vec<_>>();
        let scope = candidates.iter().find_map(|subtype| {
            subtype
                .push_scope
                .clone()
                .map(SubtypeScopeTransition::Push)
                .or_else(|| {
                    subtype
                        .replace_scopes
                        .clone()
                        .map(SubtypeScopeTransition::Replace)
                })
        });
        Ok(TypeSubtypeMatch { names, scope })
    }

    #[must_use]
    pub fn completion(&self, root: &str, prefix: &str) -> Vec<String> {
        let mut result = BTreeSet::new();
        if let Some(rule) = self.find(root) {
            self.collect_completion(&rule.kind, prefix, &mut result);
        }
        result.into_iter().collect()
    }
    #[must_use]
    pub fn info(&self, root: &str, field: &str) -> Option<String> {
        self.find(root)
            .and_then(|r| Self::find_info(&r.kind, field))
    }
    /// Return direct completions for the deepest rule clause containing `offset`.
    ///
    /// # Errors
    /// Returns [`QueryError::InvalidOffset`] for a non-boundary offset and
    /// [`QueryError::ParseFailed`] when `source` is not a complete script.
    pub fn completion_at(
        &self,
        root: &str,
        source: &str,
        offset: usize,
        prefix: &str,
    ) -> Result<Vec<String>, QueryError> {
        if offset > source.len() || !source.is_char_boundary(offset) {
            return Err(QueryError::InvalidOffset);
        }
        let cst = syntax::parse_loss_aware(source);
        let Some(root_rule) = self.find(root) else {
            return Ok(Vec::new());
        };
        let nodes = Self::query_roots(root, &cst.roots, offset);
        let (kind, nodes) = Self::context_at(&root_rule.kind, nodes, offset, 0);
        let mut result = BTreeSet::new();
        if let Some(rule) = Self::rhs_rule_at(kind, nodes, offset)
            && Self::supports_rhs_completion(&rule.kind)
        {
            self.collect_rhs_completion(&rule.kind, prefix, &mut result, 0);
        } else {
            Self::collect_direct_completion(kind, nodes, prefix, &mut result);
        }
        Ok(result.into_iter().collect())
    }

    /// Return direct field documentation for the deepest rule clause at `offset`.
    ///
    /// # Errors
    /// Returns [`QueryError::InvalidOffset`] for a non-boundary offset and
    /// [`QueryError::ParseFailed`] when `source` is not a complete script.
    pub fn info_at(
        &self,
        root: &str,
        source: &str,
        offset: usize,
        field: &str,
    ) -> Result<Option<String>, QueryError> {
        if offset > source.len() || !source.is_char_boundary(offset) {
            return Err(QueryError::InvalidOffset);
        }
        let cst = syntax::parse(source).map_err(|_| QueryError::ParseFailed)?;
        let Some(root_rule) = self.find(root) else {
            return Ok(None);
        };
        let nodes = Self::query_roots(root, &cst.roots, offset);
        let (kind, _) = Self::context_at(&root_rule.kind, nodes, offset, 0);
        Ok(Self::find_direct_info(kind, field))
    }
    fn query_roots<'a>(root: &str, nodes: &'a [CstNode], offset: usize) -> &'a [CstNode] {
        nodes
            .iter()
            .find_map(|node| {
                let CstNode::Assignment {
                    key, value, range, ..
                } = node
                else {
                    return None;
                };
                if !bare(key).eq_ignore_ascii_case(root)
                    || offset < range.start
                    || offset > range.end
                {
                    return None;
                }
                match value.as_ref() {
                    CstNode::Clause { children, .. } => Some(children.as_slice()),
                    _ => None,
                }
            })
            .unwrap_or(nodes)
    }

    fn context_at<'a>(
        kind: &'a RuleKind,
        nodes: &'a [CstNode],
        offset: usize,
        depth: usize,
    ) -> (&'a RuleKind, &'a [CstNode]) {
        if depth >= MAX_DEPTH {
            return (kind, nodes);
        }
        for node in nodes {
            let CstNode::Assignment {
                key, value, range, ..
            } = node
            else {
                continue;
            };
            let contains = range.start <= offset && offset <= range.end
                || matches!(value.as_ref(), CstNode::Clause { open, close: None, .. } if offset >= open.range.start);
            if !contains {
                continue;
            }
            let key = bare(key);
            let Some(rule) = Self::direct_rules(kind)
                .find(|rule| field_name(&rule.kind).eq_ignore_ascii_case(&key))
            else {
                continue;
            };
            if let CstNode::Clause { children, .. } = value.as_ref() {
                return Self::context_at(&rule.kind, children, offset, depth + 1);
            }
        }
        (kind, nodes)
    }

    fn direct_rules(kind: &RuleKind) -> impl Iterator<Item = &NewRule> {
        let rules = match kind {
            RuleKind::Node { rules, .. }
            | RuleKind::ValueClause { rules }
            | RuleKind::Subtype { rules, .. } => rules.as_slice(),
            _ => &[],
        };
        rules.iter().flat_map(|rule| match &rule.kind {
            RuleKind::Subtype { rules, .. } => rules.as_slice(),
            _ => std::slice::from_ref(rule),
        })
    }

    fn supports_rhs_completion(kind: &RuleKind) -> bool {
        matches!(
            kind,
            RuleKind::Leaf {
                right: NewField::Specific(_)
                    | NewField::Value(ValueType::Enum(_))
                    | NewField::Type(_),
                ..
            } | RuleKind::LeafValue {
                right: NewField::Specific(_)
                    | NewField::Value(ValueType::Enum(_))
                    | NewField::Type(_)
            }
        )
    }

    fn rhs_rule_at<'a>(
        kind: &'a RuleKind,
        nodes: &'a [CstNode],
        offset: usize,
    ) -> Option<&'a NewRule> {
        nodes.iter().find_map(|node| {
            let CstNode::Assignment { key, value, .. } = node else {
                return None;
            };
            let value_range = n_range(value);
            if !(value_range.start <= offset && offset <= value_range.end) {
                return None;
            }
            let key = bare(key);
            Self::direct_rules(kind).find(|rule| field_name(&rule.kind).eq_ignore_ascii_case(&key))
        })
    }

    fn collect_rhs_completion(
        &self,
        kind: &RuleKind,
        prefix: &str,
        out: &mut BTreeSet<String>,
        depth: usize,
    ) {
        if depth >= MAX_DEPTH {
            return;
        }
        let (RuleKind::Leaf { right, .. } | RuleKind::LeafValue { right }) = kind else {
            return;
        };
        match right {
            NewField::Specific(value) => {
                if value.starts_with(prefix) {
                    out.insert(value.clone());
                }
            }
            NewField::Value(ValueType::Enum(name)) => {
                if let Some(values) = self.enums.get(&name.to_ascii_lowercase()) {
                    out.extend(
                        values
                            .iter()
                            .filter(|value| value.starts_with(prefix))
                            .cloned(),
                    );
                }
            }
            NewField::Type(ir::TypeType::Simple(name)) => {
                if let Some(rules) = self.type_rules(name) {
                    for rule in rules {
                        self.collect_rhs_completion(&rule.kind, prefix, out, depth + 1);
                    }
                }
            }
            NewField::Type(ir::TypeType::Complex {
                prefix: left,
                name,
                suffix,
            }) => {
                if let Some(rules) = self.type_rules(name) {
                    let mut inner = BTreeSet::new();
                    for rule in rules {
                        self.collect_rhs_completion(&rule.kind, "", &mut inner, depth + 1);
                    }
                    out.extend(
                        inner
                            .into_iter()
                            .map(|value| format!("{left}{value}{suffix}"))
                            .filter(|value| value.starts_with(prefix)),
                    );
                }
            }
            _ => {}
        }
    }

    fn collect_direct_completion(
        kind: &RuleKind,
        nodes: &[CstNode],
        prefix: &str,
        out: &mut BTreeSet<String>,
    ) {
        for rule in Self::direct_rules(kind) {
            let name = field_name(&rule.kind);
            let count = nodes
                .iter()
                .filter(|node| {
                    assignment_key(node).is_some_and(|key| key.eq_ignore_ascii_case(&name))
                })
                .count();
            if !name.is_empty()
                && name.starts_with(prefix)
                && i32::try_from(count).map_or(true, |count| count < rule.options.max)
            {
                out.insert(name);
            }
        }
    }

    fn find_direct_info(kind: &RuleKind, field: &str) -> Option<String> {
        let rules = match kind {
            RuleKind::Node { rules, .. }
            | RuleKind::ValueClause { rules }
            | RuleKind::Subtype { rules, .. } => rules.as_slice(),
            _ => return None,
        };
        rules
            .iter()
            .flat_map(|rule| match &rule.kind {
                RuleKind::Subtype { rules, .. } => rules.as_slice(),
                _ => std::slice::from_ref(rule),
            })
            .find(|rule| field_name(&rule.kind).eq_ignore_ascii_case(field))
            .and_then(|rule| rule.options.description.clone())
    }

    fn collect_completion(&self, kind: &RuleKind, prefix: &str, out: &mut BTreeSet<String>) {
        let (RuleKind::Node { rules, .. }
        | RuleKind::ValueClause { rules }
        | RuleKind::Subtype { rules, .. }) = kind
        else {
            return;
        };
        for r in rules {
            let name = field_name(&r.kind);
            if !name.is_empty() && name.starts_with(prefix) {
                out.insert(name);
            }
            if let RuleKind::Leaf { right, .. } | RuleKind::LeafValue { right } = &r.kind {
                match right {
                    NewField::Value(ValueType::Enum(key)) => {
                        if let Some(values) = self.enums.get(&key.to_ascii_lowercase()) {
                            out.extend(values.iter().filter(|v| v.starts_with(prefix)).cloned());
                        }
                    }
                    NewField::Specific(value) if value.starts_with(prefix) => {
                        out.insert(value.clone());
                    }
                    _ => {}
                }
            }
            self.collect_completion(&r.kind, prefix, out);
        }
    }
    fn find_info(kind: &RuleKind, field: &str) -> Option<String> {
        let (RuleKind::Node { rules, .. }
        | RuleKind::ValueClause { rules }
        | RuleKind::Subtype { rules, .. }) = kind
        else {
            return None;
        };
        for rule in rules {
            if field_name(&rule.kind).eq_ignore_ascii_case(field)
                && let Some(description) = &rule.options.description
            {
                return Some(description.clone());
            }
            if let Some(description) = Self::find_info(&rule.kind, field) {
                return Some(description);
            }
        }
        None
    }
    fn find(&self, n: &str) -> Option<&NewRule> {
        let k = n.to_ascii_lowercase();
        self.ordinary
            .get(&k)
            .or_else(|| self.aliases.get(&k))
            .or_else(|| self.single.get(&k))
    }
    fn type_rules(&self, n: &str) -> Option<&Vec<NewRule>> {
        self.types.get(&n.to_ascii_lowercase())
    }
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn collect_rule_computed_data(
        &self,
        kind: &RuleKind,
        nodes: &[CstNode],
        out: &mut RuleComputedData,
        limit: usize,
        seen: &mut BTreeSet<String>,
        depth: usize,
        frame: &ScopeFrame,
        cancel: &mut CancelCheck<'_>,
    ) -> Result<(), QueryError> {
        if depth > MAX_DEPTH {
            return Ok(());
        }
        let (RuleKind::Node { rules, .. }
        | RuleKind::ValueClause { rules }
        | RuleKind::Subtype { rules, .. }) = kind
        else {
            return Ok(());
        };
        let effective = self.active_rules(rules, nodes, seen, depth, frame, cancel);
        for node in nodes {
            let CstNode::Assignment {
                key, value, range, ..
            } = node
            else {
                continue;
            };
            let key_text = bare(key);
            let Some(rule) = effective
                .iter()
                .find(|rule| field_matches(&rule.kind, &key_text))
                .or_else(|| {
                    effective
                        .iter()
                        .find(|rule| self.left_alias_rule(&rule.kind, &key_text).is_some())
                })
            else {
                continue;
            };
            let selected = self.left_alias_rule(&rule.kind, &key_text).unwrap_or(rule);
            match &selected.kind {
                RuleKind::Leaf {
                    left: NewField::VariableSet(kind),
                    ..
                } => {
                    ensure_computed_capacity(out, limit)?;
                    out.variable_sets.push(RuleVariableSet {
                        kind: kind.clone(),
                        value: key_text.clone(),
                        range: n_range(key),
                        scope: frame.current.clone(),
                    });
                }
                RuleKind::Node {
                    left: NewField::VariableSet(kind),
                    rules,
                } => {
                    ensure_computed_capacity(out, limit)?;
                    out.variable_sets.push(RuleVariableSet {
                        kind: kind.clone(),
                        value: key_text.clone(),
                        range: n_range(key),
                        scope: frame.current.clone(),
                    });
                    if let CstNode::Clause { children, .. } = value.as_ref() {
                        self.collect_rule_computed_data(
                            &RuleKind::ValueClause {
                                rules: rules.clone(),
                            },
                            children,
                            out,
                            limit,
                            seen,
                            depth + 1,
                            &frame.apply(&selected.options),
                            cancel,
                        )?;
                    }
                }
                RuleKind::Leaf {
                    right: NewField::VariableSet(kind),
                    ..
                }
                | RuleKind::LeafValue {
                    right: NewField::VariableSet(kind),
                } => {
                    ensure_computed_capacity(out, limit)?;
                    out.variable_sets.push(RuleVariableSet {
                        kind: kind.clone(),
                        value: bare(value),
                        range: n_range(value),
                        scope: frame.current.clone(),
                    });
                }
                RuleKind::Node { .. } | RuleKind::ValueClause { .. } | RuleKind::Subtype { .. } => {
                    if let CstNode::Clause { children, .. } = value.as_ref() {
                        if rule_has_alias(&selected.kind, "effect") {
                            ensure_computed_capacity(out, limit)?;
                            out.effect_blocks.push(*range);
                        }
                        if rule_has_alias(&selected.kind, "trigger") {
                            ensure_computed_capacity(out, limit)?;
                            out.trigger_blocks.push(*range);
                        }
                        self.collect_rule_computed_data(
                            &selected.kind,
                            children,
                            out,
                            limit,
                            seen,
                            depth + 1,
                            &frame.apply(&selected.options),
                            cancel,
                        )?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn collect_typed_references(
        &self,
        kind: &RuleKind,
        nodes: &[CstNode],
        out: &mut Vec<TypedReference>,
        limit: usize,
        seen: &mut BTreeSet<String>,
        depth: usize,
        frame: &ScopeFrame,
        cancel: &mut CancelCheck<'_>,
        resolve_value_scope: &mut dyn FnMut(&str, Option<&str>) -> Option<DynamicTypeReference>,
    ) -> Result<(), QueryError> {
        if depth > MAX_DEPTH {
            return Ok(());
        }
        let (RuleKind::Node { rules, .. }
        | RuleKind::ValueClause { rules }
        | RuleKind::Subtype { rules, .. }) = kind
        else {
            return Ok(());
        };
        let effective = self.active_rules(rules, nodes, seen, depth, frame, cancel);
        for node in nodes {
            let CstNode::Assignment { key, value, .. } = node else {
                continue;
            };
            let key_text = bare(key);
            let Some(rule) = effective
                .iter()
                .find(|rule| field_matches(&rule.kind, &key_text))
                .or_else(|| {
                    effective
                        .iter()
                        .find(|rule| self.left_alias_rule(&rule.kind, &key_text).is_some())
                })
            else {
                continue;
            };
            let selected = self.left_alias_rule(&rule.kind, &key_text).unwrap_or(rule);
            match &selected.kind {
                RuleKind::Leaf { left, right } => {
                    if let Some(reference) = typed_reference(
                        right,
                        value,
                        &selected.options,
                        frame.current.as_deref(),
                        resolve_value_scope,
                    )
                    .or_else(|| {
                        typed_reference(
                            left,
                            key,
                            &selected.options,
                            frame.current.as_deref(),
                            resolve_value_scope,
                        )
                    }) {
                        if out.len() >= limit {
                            return Err(QueryError::TooManyResults);
                        }
                        out.push(reference);
                    }
                }
                RuleKind::LeafValue { right } => {
                    if let Some(reference) = typed_reference(
                        right,
                        value,
                        &selected.options,
                        frame.current.as_deref(),
                        resolve_value_scope,
                    ) {
                        if out.len() >= limit {
                            return Err(QueryError::TooManyResults);
                        }
                        out.push(reference);
                    }
                }
                RuleKind::Node { .. } | RuleKind::ValueClause { .. } | RuleKind::Subtype { .. } => {
                    if let CstNode::Clause { children, .. } = value.as_ref() {
                        self.collect_typed_references(
                            &selected.kind,
                            children,
                            out,
                            limit,
                            seen,
                            depth + 1,
                            &frame.apply(&selected.options),
                            cancel,
                            resolve_value_scope,
                        )?;
                    }
                }
                RuleKind::Opaque(_) => {}
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_nodes(
        &self,
        kind: &RuleKind,
        nodes: &[CstNode],
        out: &mut ValidationResult,
        seen: &mut BTreeSet<String>,
        depth: usize,
        frame: &ScopeFrame,
        cancel: &mut CancelCheck<'_>,
    ) {
        if depth > MAX_DEPTH {
            out.diagnostics.push(diag(
                "RULE150",
                "depth",
                ByteRange { start: 0, end: 0 },
                vec![MAX_DEPTH.to_string()],
            ));
            return;
        }
        let (RuleKind::Node { rules, .. }
        | RuleKind::ValueClause { rules }
        | RuleKind::Subtype { rules, .. }) = kind
        else {
            return;
        };
        let effective_rules = self.active_rules(rules, nodes, seen, depth, frame, cancel);
        let rules = effective_rules.as_slice();
        let mut occurrences: BTreeMap<String, Vec<ByteRange>> = BTreeMap::new();
        for n in nodes {
            if cancel.poll() {
                return;
            }
            if let CstNode::Assignment {
                key, value, range, ..
            } = n
            {
                let k = bare(key);
                let Some(r) = rules
                    .iter()
                    .find(|x| field_name(&x.kind).eq_ignore_ascii_case(&k))
                    .or_else(|| {
                        rules
                            .iter()
                            .find(|x| self.left_alias_rule(&x.kind, &k).is_some())
                    })
                else {
                    let has_alias_slot = rules.iter().any(|rule| {
                        matches!(
                            rule.kind,
                            RuleKind::Node {
                                left: NewField::Aliases(_) | NewField::SingleAlias(_),
                                ..
                            } | RuleKind::Leaf {
                                left: NewField::Aliases(_) | NewField::SingleAlias(_),
                                ..
                            }
                        )
                    });
                    let code = if has_alias_slot { "RULE130" } else { "RULE101" };
                    out.diagnostics
                        .push(diag(code, &k, *range, vec![k.clone()]));
                    continue;
                };
                let matched_name = field_name(&r.kind).to_ascii_lowercase();
                occurrences.entry(matched_name).or_default().push(*range);
                if let Some(alias) = self.left_alias_rule(&r.kind, &k) {
                    self.validate_named_rule(alias, n, value, out, seen, depth, frame, cancel);
                } else {
                    self.validate_rule(r, n, value, out, seen, depth, frame, cancel);
                }
            }
        }
        for r in rules {
            let name = field_name(&r.kind);
            let ranges = occurrences.get(&name.to_ascii_lowercase());
            let n = ranges.map_or(0, Vec::len);
            if usize::try_from(r.options.min).is_ok_and(|min| n < min) {
                out.diagnostics.push(diag(
                    "RULE110",
                    &name,
                    ByteRange { start: 0, end: 0 },
                    vec![name.clone(), r.options.min.to_string()],
                ));
            }
            if let Ok(max) = usize::try_from(r.options.max)
                && n > max
            {
                let overflow_range = ranges
                    .and_then(|items| items.get(max))
                    .copied()
                    .unwrap_or(r.range);
                out.diagnostics.push(diag(
                    "RULE111",
                    &name,
                    overflow_range,
                    vec![name.clone(), r.options.max.to_string()],
                ));
            }
        }
    }
    fn active_rules(
        &self,
        rules: &[NewRule],
        nodes: &[CstNode],
        seen: &BTreeSet<String>,
        depth: usize,
        frame: &ScopeFrame,
        cancel: &mut CancelCheck<'_>,
    ) -> Vec<NewRule> {
        if depth > MAX_DEPTH {
            return Vec::new();
        }
        let mut active = BTreeMap::new();
        for rule in rules {
            if cancel.poll() {
                return Vec::new();
            }
            if let RuleKind::Subtype {
                name,
                primary: true,
                rules: children,
            } = &rule.kind
            {
                let probe_kind = RuleKind::Node {
                    left: NewField::Specific("__subtype_probe".into()),
                    rules: children.clone(),
                };
                let mut probe = ValidationResult::default();
                let mut probe_seen = seen.clone();
                self.validate_nodes(
                    &probe_kind,
                    nodes,
                    &mut probe,
                    &mut probe_seen,
                    depth + 1,
                    frame,
                    cancel,
                );
                active.insert(
                    name.to_ascii_lowercase(),
                    probe
                        .diagnostics
                        .iter()
                        .all(|diagnostic| diagnostic.code == "RULE101"),
                );
            }
        }
        let mut result = Vec::new();
        for rule in rules {
            if cancel.poll() {
                return Vec::new();
            }
            match &rule.kind {
                RuleKind::Subtype {
                    name,
                    primary,
                    rules: children,
                } => {
                    let primary_active = active
                        .get(&name.to_ascii_lowercase())
                        .copied()
                        .unwrap_or(false);
                    if (*primary && primary_active) || (!*primary && !primary_active) {
                        result.extend(self.active_rules(
                            children,
                            nodes,
                            seen,
                            depth + 1,
                            frame,
                            cancel,
                        ));
                    }
                }
                _ => result.push(rule.clone()),
            }
        }
        result
    }

    fn left_alias_rule<'a>(&'a self, kind: &RuleKind, key: &str) -> Option<&'a NewRule> {
        let (RuleKind::Node { left: field, .. } | RuleKind::Leaf { left: field, .. }) = kind else {
            return None;
        };
        let (map, group) = match field {
            NewField::Aliases(group) => (&self.aliases, group),
            NewField::SingleAlias(group) => (&self.single, group),
            _ => return None,
        };
        map.get(&format!("{group}:{key}").to_ascii_lowercase())
            .or_else(|| map.get(&key.to_ascii_lowercase()))
    }
    #[allow(clippy::too_many_arguments)]
    fn validate_named_rule(
        &self,
        r: &NewRule,
        n: &CstNode,
        v: &CstNode,
        out: &mut ValidationResult,
        seen: &mut BTreeSet<String>,
        depth: usize,
        frame: &ScopeFrame,
        cancel: &mut CancelCheck<'_>,
    ) {
        let name = field_name(&r.kind).to_ascii_lowercase();
        if !seen.insert(name.clone()) {
            out.diagnostics
                .push(diag("RULE130", &name, n_range(n), vec![name.clone()]));
            return;
        }
        self.validate_rule(r, n, v, out, seen, depth, frame, cancel);
        seen.remove(&field_name(&r.kind).to_ascii_lowercase());
    }
    #[allow(clippy::too_many_arguments)]
    fn validate_rule(
        &self,
        r: &NewRule,
        n: &CstNode,
        v: &CstNode,
        out: &mut ValidationResult,
        seen: &mut BTreeSet<String>,
        depth: usize,
        frame: &ScopeFrame,
        cancel: &mut CancelCheck<'_>,
    ) {
        for required in &r.options.required_scopes {
            if cancel.poll() {
                return;
            }
            let valid = frame
                .current
                .as_deref()
                .is_some_and(|scope| scope.eq_ignore_ascii_case(required))
                || (frame.current.is_none()
                    && self
                        .scopes
                        .names
                        .iter()
                        .any(|scope| scope.eq_ignore_ascii_case(required)));
            if !valid {
                out.diagnostics.push(diag(
                    "RULE140",
                    required,
                    n_range(n),
                    vec![required.clone()],
                ));
            }
        }
        match &r.kind {
            RuleKind::Node { .. } | RuleKind::ValueClause { .. } | RuleKind::Subtype { .. } => {
                if let CstNode::Clause { children, .. } = v {
                    let child_frame = frame.apply(&r.options);
                    self.validate_nodes(
                        &r.kind,
                        children,
                        out,
                        seen,
                        depth + 1,
                        &child_frame,
                        cancel,
                    );
                } else {
                    out.diagnostics
                        .push(diag("RULE102", &field_name(&r.kind), n_range(n), vec![]));
                }
            }
            RuleKind::Leaf { right, .. } | RuleKind::LeafValue { right } => {
                if matches!(v, CstNode::Bare { .. } | CstNode::ColourLiteral { .. }) {
                    self.validate_value(right, v, out, seen, depth, frame, cancel);
                } else {
                    out.diagnostics
                        .push(diag("RULE103", &field_name(&r.kind), n_range(v), vec![]));
                }
            }
            RuleKind::Opaque(a) => {
                if !seen.insert(a.clone()) {
                    out.diagnostics
                        .push(diag("RULE130", a, n_range(n), vec![a.clone()]));
                }
            }
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn validate_type(
        &self,
        name: &str,
        raw: &str,
        v: &CstNode,
        out: &mut ValidationResult,
        seen: &mut BTreeSet<String>,
        depth: usize,
        _prefix: &str,
        frame: &ScopeFrame,
        cancel: &mut CancelCheck<'_>,
    ) {
        let key = name.to_ascii_lowercase();
        if !seen.insert(format!("type:{key}")) {
            return;
        }
        if let Some(rules) = self.type_rules(name) {
            for r in rules {
                if cancel.poll() {
                    break;
                }
                self.validate_rule_value(r, raw, v, out, seen, depth, frame, cancel);
            }
        } else {
            out.diagnostics
                .push(diag("RULE130", name, n_range(v), vec![name.to_owned()]));
        }
        seen.remove(&format!("type:{key}"));
    }
    #[allow(clippy::too_many_arguments)]
    fn validate_rule_value(
        &self,
        r: &NewRule,
        raw: &str,
        v: &CstNode,
        out: &mut ValidationResult,
        _seen: &mut BTreeSet<String>,
        _depth: usize,
        frame: &ScopeFrame,
        cancel: &mut CancelCheck<'_>,
    ) {
        if cancel.poll() {
            return;
        }
        if let RuleKind::Leaf { right, .. } | RuleKind::LeafValue { right } = &r.kind {
            self.validate_value_text(right, raw, n_range(v), out, frame);
        }
    }
    fn validate_value_text(
        &self,
        f: &NewField,
        raw: &str,
        range: ByteRange,
        out: &mut ValidationResult,
        frame: &ScopeFrame,
    ) {
        let (ty, key) = match f {
            NewField::Value(t) => (Some(t), raw),
            NewField::Scalar => (Some(&ValueType::Scalar), raw),
            NewField::Scope(allowed) => {
                if !allowed.iter().any(|x| x.eq_ignore_ascii_case(raw))
                    && !frame.allows(raw, &self.scopes)
                {
                    out.diagnostics
                        .push(diag("RULE120", raw, range, allowed.clone()));
                }
                return;
            }
            _ => return,
        };
        if let Some(t) = ty {
            let bad = match t {
                ValueType::Bool => !matches!(
                    key.to_ascii_lowercase().as_str(),
                    "yes" | "no" | "true" | "false"
                ),
                ValueType::Int(a, b) => key.parse::<i64>().map_or(true, |x| x < *a || x > *b),
                ValueType::Float(a, b) => key.parse::<f64>().map_or(true, |x| x < *a || x > *b),
                ValueType::Percent => !valid_percent(key),
                ValueType::Date => !valid_date(key),
                ValueType::DateTime => !valid_datetime(key),
                ValueType::Enum(name) => self
                    .enums
                    .get(&name.to_ascii_lowercase())
                    .is_none_or(|values| !values.contains(key)),
                _ => false,
            };
            if bad {
                out.diagnostics
                    .push(diag("RULE120", key, range, vec![key.into()]));
            }
        }
    }
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn validate_value(
        &self,
        f: &NewField,
        v: &CstNode,
        out: &mut ValidationResult,
        seen: &mut BTreeSet<String>,
        depth: usize,
        frame: &ScopeFrame,
        cancel: &mut CancelCheck<'_>,
    ) {
        if cancel.poll() {
            return;
        }
        let raw = bare(v);
        let (ty, key) = match f {
            NewField::Value(t) => (Some(t), raw.as_str()),
            NewField::Scalar => (Some(&ValueType::Scalar), raw.as_str()),
            NewField::Aliases(group) => {
                let key = format!("{group}:{raw}").to_ascii_lowercase();
                if let Some(rule) = self.aliases.get(&key) {
                    self.validate_named_rule(rule, v, v, out, seen, depth + 1, frame, cancel);
                } else {
                    out.diagnostics
                        .push(diag("RULE130", &key, n_range(v), vec![key.clone()]));
                }
                return;
            }
            NewField::SingleAlias(name) => {
                let key = name.to_ascii_lowercase();
                if let Some(rule) = self.single.get(&key) {
                    self.validate_named_rule(rule, v, v, out, seen, depth + 1, frame, cancel);
                } else {
                    out.diagnostics
                        .push(diag("RULE130", &key, n_range(v), vec![key.clone()]));
                }
                return;
            }
            NewField::Specific(s) => {
                if raw != *s {
                    out.diagnostics
                        .push(diag("RULE120", &raw, n_range(v), vec![s.clone()]));
                }
                return;
            }
            NewField::Parameter | NewField::LocalisationParameter => {
                if !valid_parameter(&raw) {
                    out.diagnostics
                        .push(diag("RULE120", &raw, n_range(v), vec![raw.clone()]));
                }
                return;
            }
            NewField::Scope(allowed) => {
                if !allowed.iter().any(|x| x.eq_ignore_ascii_case(&raw))
                    && !frame.resolves_keyword_to_allowed(&raw, allowed)
                    && (!allowed.is_empty() || !frame.allows(&raw, &self.scopes))
                {
                    out.diagnostics
                        .push(diag("RULE120", &raw, n_range(v), allowed.clone()));
                }
                return;
            }
            NewField::ParameterValue => {
                if !valid_parameter_value(&raw) {
                    out.diagnostics
                        .push(diag("RULE120", &raw, n_range(v), vec![raw.clone()]));
                }
                return;
            }
            NewField::Type(ir::TypeType::Simple(name)) => {
                self.validate_type(name, &raw, v, out, seen, depth, "", frame, cancel);
                return;
            }
            NewField::Type(ir::TypeType::Complex {
                prefix,
                name,
                suffix,
            }) => {
                if !raw.starts_with(prefix)
                    || !raw.ends_with(suffix)
                    || raw.len() <= prefix.len() + suffix.len()
                {
                    out.diagnostics
                        .push(diag("RULE120", &raw, n_range(v), vec![name.clone()]));
                } else {
                    let inner = &raw[prefix.len()..raw.len() - suffix.len()];
                    self.validate_type(name, inner, v, out, seen, depth, "", frame, cancel);
                }
                return;
            }
            _ => return,
        };
        if let Some(t) = ty {
            let bad = match t {
                ValueType::Bool => !matches!(
                    key.to_ascii_lowercase().as_str(),
                    "yes" | "no" | "true" | "false"
                ),
                ValueType::Int(a, b) => key.parse::<i64>().map_or(true, |x| x < *a || x > *b),
                ValueType::Float(a, b) => key.parse::<f64>().map_or(true, |x| x < *a || x > *b),
                ValueType::Percent => !valid_percent(key),
                ValueType::Date => !valid_date(key),
                ValueType::DateTime => !valid_datetime(key),
                ValueType::Enum(name) => self
                    .enums
                    .get(&name.to_ascii_lowercase())
                    .is_none_or(|values| !values.contains(key)),
                _ => false,
            };
            if bad {
                out.diagnostics
                    .push(diag("RULE120", key, n_range(v), vec![key.into()]));
            }
        }
    }
}
fn subtype_selector_matches(subtype: &ir::SubtypeDefinition, key: &str) -> bool {
    let field_match = subtype
        .type_key_field
        .as_deref()
        .is_none_or(|field| key.eq_ignore_ascii_case(field));
    let starts_match = subtype.starts_with.as_deref().is_none_or(|prefix| {
        key.to_ascii_lowercase()
            .starts_with(&prefix.to_ascii_lowercase())
    });
    let regex_match = subtype.type_key_regex.as_deref().is_none_or(|pattern| {
        regex::RegexBuilder::new(pattern)
            .case_insensitive(true)
            .build()
            .is_ok_and(|regex| regex.is_match(key))
    });
    field_match && starts_match && regex_match
}

fn computed_count(data: &RuleComputedData) -> usize {
    data.variable_sets.len() + data.effect_blocks.len() + data.trigger_blocks.len()
}

fn ensure_computed_capacity(data: &RuleComputedData, limit: usize) -> Result<(), QueryError> {
    if computed_count(data) >= limit {
        return Err(QueryError::TooManyResults);
    }
    Ok(())
}

fn rule_has_alias(kind: &RuleKind, alias: &str) -> bool {
    match kind {
        RuleKind::Node { rules, .. }
        | RuleKind::ValueClause { rules }
        | RuleKind::Subtype { rules, .. } => rules.iter().any(|rule| match &rule.kind {
            RuleKind::Leaf {
                left: NewField::Aliases(group),
                ..
            } => group.eq_ignore_ascii_case(alias),
            nested => rule_has_alias(nested, alias),
        }),
        _ => false,
    }
}

fn typed_reference(
    field: &NewField,
    node: &CstNode,
    options: &ir::Options,
    current_scope: Option<&str>,
    resolve_value_scope: &mut dyn FnMut(&str, Option<&str>) -> Option<DynamicTypeReference>,
) -> Option<TypedReference> {
    let raw = bare(node);
    let (type_name, prefix, suffix, associated_type) = match field {
        NewField::Type(ir::TypeType::Simple(name)) => {
            (name.clone(), String::new(), String::new(), None)
        }
        NewField::Type(ir::TypeType::Complex {
            prefix,
            name,
            suffix,
        }) => (name.clone(), prefix.clone(), suffix.clone(), None),
        NewField::ValueScope { .. } => {
            let dynamic = resolve_value_scope(value_scope_head(&raw), current_scope)?;
            let associated_type = options.type_hint.as_ref().map(|hint| hint.0.clone());
            return Some(TypedReference {
                type_name: dynamic.type_name,
                value: dynamic.value,
                range: n_range(node),
                is_outgoing: options
                    .reference_details
                    .as_ref()
                    .is_none_or(|details| details.0),
                reference_label: options
                    .reference_details
                    .as_ref()
                    .map(|details| details.1.clone()),
                fuzzy: false,
                associated_type,
            });
        }
        _ => return None,
    };
    let value = raw;
    let value = value
        .strip_prefix(&prefix)?
        .strip_suffix(&suffix)?
        .to_owned();
    Some(TypedReference {
        type_name,
        value,
        range: n_range(node),
        is_outgoing: options
            .reference_details
            .as_ref()
            .is_none_or(|details| details.0),
        reference_label: options
            .reference_details
            .as_ref()
            .map(|details| details.1.clone()),
        fuzzy: !prefix.is_empty() || !suffix.is_empty(),
        associated_type,
    })
}

fn value_scope_head(raw: &str) -> &str {
    raw.trim_matches('"').split('|').next().unwrap_or("")
}

fn valid_percent(s: &str) -> bool {
    s.strip_suffix('%')
        .is_some_and(|number| number.parse::<f64>().is_ok())
}

fn valid_parameter(s: &str) -> bool {
    let Some(rest) = s.strip_prefix('$') else {
        return false;
    };
    let Some(end) = rest.find('$') else {
        return false;
    };
    let name = &rest[..end];
    let suffix = &rest[end + 1..];
    let inner = if let Some(default) = suffix.strip_prefix('|') {
        if default.is_empty() {
            return false;
        }
        format!("{name}|{default}")
    } else if suffix.is_empty() {
        name.to_owned()
    } else {
        return false;
    };
    let parts: Vec<&str> = inner.split('|').collect();
    (parts.len() == 1 || parts.len() == 2)
        && {
            let n = parts[0];
            let mut chars = n.chars();
            chars
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        }
        && (parts.len() == 1 || !parts[1].is_empty())
}
fn valid_parameter_value(s: &str) -> bool {
    !s.is_empty()
        && (valid_parameter(s) || s.parse::<f64>().is_ok() || !s.contains(char::is_whitespace))
}
fn validate_rule_scope_options(rule: &NewRule, scopes: &ScopeUniverse) -> Result<(), CompileError> {
    let check = |name: &str| {
        if scopes.names.is_empty() || scopes.names.iter().any(|s| s.eq_ignore_ascii_case(name)) {
            Ok(())
        } else {
            Err(CompileError::UnknownScope(name.to_owned()))
        }
    };
    if let Some(scope) = &rule.options.push_scope {
        check(scope)?;
    }
    if let Some(replacement) = &rule.options.replace_scopes {
        for scope in replacement
            .root
            .iter()
            .chain(replacement.this.iter())
            .chain(replacement.froms.iter().flatten())
            .chain(replacement.prevs.iter().flatten())
        {
            check(scope)?;
        }
    }
    validate_scope_options(&rule.kind, scopes)
}

fn validate_scope_options(kind: &RuleKind, scopes: &ScopeUniverse) -> Result<(), CompileError> {
    let check = |name: &str| {
        if scopes.names.is_empty() || scopes.names.iter().any(|s| s.eq_ignore_ascii_case(name)) {
            Ok(())
        } else {
            Err(CompileError::UnknownScope(name.to_owned()))
        }
    };
    let (RuleKind::Node { rules, .. }
    | RuleKind::ValueClause { rules }
    | RuleKind::Subtype { rules, .. }) = kind
    else {
        return Ok(());
    };
    for rule in rules {
        if let Some(s) = &rule.options.push_scope {
            check(s)?;
        }
        if let Some(rs) = &rule.options.replace_scopes {
            for s in rs
                .root
                .iter()
                .chain(rs.this.iter())
                .chain(rs.froms.iter().flatten())
                .chain(rs.prevs.iter().flatten())
            {
                check(s)?;
            }
        }
        validate_rule_scope_options(rule, scopes)?;
    }
    Ok(())
}

fn count_rules(
    k: &RuleKind,
    n: &mut usize,
    limit: usize,
    depth: usize,
) -> Result<(), CompileError> {
    if depth > MAX_DEPTH {
        return Err(CompileError::TooDeep);
    }
    if *n > limit {
        return Err(CompileError::TooManyRules);
    }
    let (RuleKind::Node { rules: rs, .. }
    | RuleKind::ValueClause { rules: rs }
    | RuleKind::Subtype { rules: rs, .. }) = k
    else {
        return Ok(());
    };
    for r in rs {
        *n += 1;
        count_rules(&r.kind, n, limit, depth + 1)?;
    }
    Ok(())
}
fn field_matches(kind: &RuleKind, key: &str) -> bool {
    match kind {
        RuleKind::Node {
            left: NewField::VariableSet(_) | NewField::Type(_),
            ..
        }
        | RuleKind::Leaf {
            left: NewField::VariableSet(_) | NewField::Type(_),
            ..
        } => true,
        _ => field_name(kind).eq_ignore_ascii_case(key),
    }
}

fn field_name(k: &RuleKind) -> String {
    match k {
        RuleKind::Node { left, .. } | RuleKind::Leaf { left, .. } => new_field_name(left),
        RuleKind::LeafValue { .. } | RuleKind::ValueClause { .. } | RuleKind::Subtype { .. } => {
            String::new()
        }
        RuleKind::Opaque(x) => x.clone(),
    }
}
fn new_field_name(f: &NewField) -> String {
    match f {
        NewField::Specific(x)
        | NewField::Aliases(x)
        | NewField::SingleAlias(x)
        | NewField::Opaque(x)
        | NewField::Type(ir::TypeType::Simple(x)) => x.clone(),
        _ => String::new(),
    }
}
fn bare(n: &CstNode) -> String {
    match n {
        CstNode::Bare { token } => token.value.trim_matches('"').to_owned(),
        CstNode::Assignment { key, .. } => bare(key),
        CstNode::ColourLiteral { raw, .. } => raw.clone(),
        _ => String::new(),
    }
}
fn assignment_key(node: &CstNode) -> Option<String> {
    let CstNode::Assignment { key, .. } = node else {
        return None;
    };
    Some(bare(key))
}

fn n_range(n: &CstNode) -> ByteRange {
    match n {
        CstNode::Assignment { range, .. }
        | CstNode::Clause { range, .. }
        | CstNode::ColourLiteral { range, .. } => *range,
        CstNode::Bare { token } => token.range,
        _ => ByteRange { start: 0, end: 0 },
    }
}
#[must_use]
pub fn diagnostic_message_key(code: &str) -> &'static str {
    match code {
        "RULE001" => "rules.syntax",
        "RULE101" => "rules.unknown_field",
        "RULE102" => "rules.expected_clause",
        "RULE103" => "rules.expected_scalar",
        "RULE110" => "rules.cardinality_minimum",
        "RULE111" => "rules.cardinality_maximum",
        "RULE120" => "rules.invalid_value",
        "RULE130" => "rules.unresolved_reference",
        "RULE140" => "rules.scope_mismatch",
        "RULE150" => "rules.depth_exceeded",
        _ => "rules.unknown",
    }
}

fn diag(code: &str, key: &str, range: ByteRange, args: Vec<String>) -> Diagnostic {
    Diagnostic {
        code: code.into(),
        message_key: diagnostic_message_key(code).into(),
        key: key.into(),
        args,
        range,
    }
}
fn valid_date(s: &str) -> bool {
    let p: Vec<_> = s.split('.').collect();
    if p.len() != 3 {
        return false;
    }
    let Ok(year) = p[0].parse::<u32>() else {
        return false;
    };
    let Ok(month) = p[1].parse::<u32>() else {
        return false;
    };
    let Ok(day) = p[2].parse::<u32>() else {
        return false;
    };
    year > 0 && (1..=12).contains(&month) && day >= 1 && day <= days_in_month(year, month)
}
fn days_in_month(year: u32, month: u32) -> u32 {
    match month {
        2 if year % 400 == 0 || (year % 4 == 0 && year % 100 != 0) => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}
fn valid_datetime(s: &str) -> bool {
    let parts: Vec<_> = s.split('.').collect();
    if !(4..=6).contains(&parts.len()) || !valid_date(&parts[..3].join(".")) {
        return false;
    }
    let time_parts = &parts[3..];
    let Ok(hour) = time_parts[0].parse::<u32>() else {
        return false;
    };
    let minute = time_parts
        .get(1)
        .map_or(Some(0), |value| value.parse::<u32>().ok());
    let second = time_parts
        .get(2)
        .map_or(Some(0), |value| value.parse::<u32>().ok());
    minute.is_some_and(|value| value < 60) && second.is_some_and(|value| value < 60) && hour < 24
}
