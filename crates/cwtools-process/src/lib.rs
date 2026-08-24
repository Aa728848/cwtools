#![forbid(unsafe_code)]
#![allow(clippy::missing_errors_doc, clippy::must_use_candidate)]
//! Bounded semantic processing for Clausewitz scripts.

use cwtools_domain::{Document, Item, Value};
use cwtools_script_syntax::{ByteRange, Cst, CstNode, Operator, TokenKind};
use std::collections::{BTreeMap, BTreeSet};

pub const MAX_DEPTH: usize = 256;
pub const MAX_NODES: usize = 1_000_000;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProcessedDocument {
    pub children: Vec<ProcessedItem>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProcessedItem {
    Node(Node),
    Leaf(Leaf),
    LeafValue(LeafValue),
    ValueClause(ValueClause),
    Comment(Comment),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node {
    pub key: String,
    pub operator: Operator,
    pub children: Vec<ProcessedItem>,
    pub range: ByteRange,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Leaf {
    pub key: String,
    pub operator: Operator,
    pub value: LeafValue,
    pub range: ByteRange,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Comment {
    pub text: String,
    pub range: ByteRange,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueClause {
    pub children: Vec<ProcessedItem>,
    pub range: Option<ByteRange>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeafValue {
    Text(String),
    Quoted(String),
    Integer(i64),
    Decimal(String),
    Boolean(bool),
    Colour(String),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bounded<T> {
    pub items: Vec<T>,
    pub truncated: bool,
}

impl LeafValue {
    fn text(&self) -> String {
        match self {
            Self::Text(v) | Self::Quoted(v) | Self::Decimal(v) | Self::Colour(v) => v.clone(),
            Self::Integer(v) => v.to_string(),
            Self::Boolean(v) => {
                if *v {
                    "yes".into()
                } else {
                    "no".into()
                }
            }
        }
    }
}
impl ProcessedDocument {
    pub fn from_cst(cst: &Cst) -> Self {
        Self {
            children: convert_cst(&cst.roots),
        }
    }
    pub fn from_document(doc: &Document) -> Self {
        Self {
            children: convert_domain(&doc.children),
        }
    }
    #[must_use]
    pub fn deep_clone(&self) -> Self {
        self.clone()
    }
    pub fn to_canonical(&self) -> String {
        render(&self.children, 0)
    }
    pub fn reparse(&self) -> Result<Self, String> {
        cwtools_script_syntax::parse(&self.to_canonical())
            .map(|x| Self::from_cst(&x))
            .map_err(|x| {
                x.into_iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join("; ")
            })
    }
    pub fn nodes(&self) -> Bounded<&Node> {
        collect(&self.children, |x| {
            if let ProcessedItem::Node(v) = x {
                Some(v)
            } else {
                None
            }
        })
    }
    pub fn leaves(&self) -> Bounded<&Leaf> {
        collect(&self.children, |x| {
            if let ProcessedItem::Leaf(v) = x {
                Some(v)
            } else {
                None
            }
        })
    }
    pub fn comments(&self) -> Bounded<&Comment> {
        collect(&self.children, |x| {
            if let ProcessedItem::Comment(v) = x {
                Some(v)
            } else {
                None
            }
        })
    }
    pub fn leaf_values(&self) -> Bounded<&LeafValue> {
        collect(&self.children, |x| match x {
            ProcessedItem::Leaf(v) => Some(&v.value),
            ProcessedItem::LeafValue(v) => Some(v),
            _ => None,
        })
    }
    pub fn value_clauses(&self) -> Bounded<&ValueClause> {
        collect(&self.children, |x| {
            if let ProcessedItem::ValueClause(v) = x {
                Some(v)
            } else {
                None
            }
        })
    }
    pub fn clauses(&self) -> Bounded<&ValueClause> {
        self.value_clauses()
    }
    pub fn tag(&self, key: &str) -> Vec<&Node> {
        self.nodes()
            .items
            .into_iter()
            .filter(|x| x.key == key)
            .collect()
    }
    pub fn tag_text(&self, key: &str) -> Vec<String> {
        self.leaves()
            .items
            .into_iter()
            .filter(|x| x.key == key)
            .map(|x| x.value.text())
            .collect()
    }
    pub fn child(&self, key: &str) -> Vec<&Node> {
        self.tag(key)
    }
}

fn collect<'a, T>(
    xs: &'a [ProcessedItem],
    f: impl Fn(&'a ProcessedItem) -> Option<T>,
) -> Bounded<T> {
    let mut out = Vec::new();
    let mut seen = 0;
    let mut truncated = false;
    let mut stack: Vec<(&[ProcessedItem], usize)> = vec![(xs, 0)];
    while let Some((items, depth)) = stack.pop() {
        if depth > MAX_DEPTH {
            truncated = true;
            continue;
        }
        for item in items.iter().rev() {
            if seen >= MAX_NODES {
                truncated = true;
                break;
            }
            seen += 1;
            if let Some(v) = f(item) {
                out.push(v);
            }
            match item {
                ProcessedItem::Node(v) => stack.push((&v.children, depth + 1)),
                ProcessedItem::ValueClause(v) => stack.push((&v.children, depth + 1)),
                _ => {}
            }
        }
    }
    out.reverse();
    Bounded {
        items: out,
        truncated,
    }
}
fn key(x: &CstNode) -> String {
    if let CstNode::Bare { token } = x {
        token.value.clone()
    } else {
        String::new()
    }
}
fn token(t: &cwtools_script_syntax::Token) -> LeafValue {
    if matches!(t.kind, TokenKind::QuotedString) {
        LeafValue::Quoted(t.value.clone())
    } else if t.value == "yes" || t.value == "no" {
        LeafValue::Boolean(t.value == "yes")
    } else if t.value.len() > 1 && t.value.trim_start_matches('-').starts_with('0') {
        LeafValue::Text(t.value.clone())
    } else if let Ok(v) = t.value.parse() {
        LeafValue::Integer(v)
    } else if t.value.parse::<f64>().is_ok() {
        LeafValue::Decimal(t.value.clone())
    } else {
        LeafValue::Text(t.value.clone())
    }
}
fn scalar(x: &CstNode) -> LeafValue {
    match x {
        CstNode::Bare { token: t } => token(t),
        CstNode::ColourLiteral { raw, .. } => LeafValue::Colour(raw.clone()),
        _ => LeafValue::Text(String::new()),
    }
}
fn convert_cst(xs: &[CstNode]) -> Vec<ProcessedItem> {
    xs.iter()
        .filter_map(|x| match x {
            CstNode::Assignment {
                key: k,
                operator,
                value,
                range,
            } => match value.as_ref() {
                CstNode::Clause { children, .. } => Some(ProcessedItem::Node(Node {
                    key: key(k),
                    operator: *operator,
                    children: convert_cst(children),
                    range: *range,
                })),
                _ => Some(ProcessedItem::Leaf(Leaf {
                    key: key(k),
                    operator: *operator,
                    value: scalar(value),
                    range: *range,
                })),
            },
            CstNode::Bare { token: t } => Some(ProcessedItem::LeafValue(token(t))),
            CstNode::Comment { token: t } => Some(ProcessedItem::Comment(Comment {
                text: t.raw.clone(),
                range: t.range,
            })),
            CstNode::Clause {
                children, range, ..
            } => Some(ProcessedItem::ValueClause(ValueClause {
                children: convert_cst(children),
                range: Some(*range),
            })),
            CstNode::ColourLiteral { raw, .. } => {
                Some(ProcessedItem::LeafValue(LeafValue::Colour(raw.clone())))
            }
            _ => None,
        })
        .collect()
}
fn convert_domain(xs: &[Item]) -> Vec<ProcessedItem> {
    xs.iter()
        .map(|x| match x {
            Item::Assignment {
                key,
                operator,
                value,
                range,
            } => match value {
                Value::Clause(v) => ProcessedItem::Node(Node {
                    key: key.clone(),
                    operator: *operator,
                    children: convert_domain(v),
                    range: *range,
                }),
                Value::Scalar { raw, quoted, typed } => ProcessedItem::Leaf(Leaf {
                    key: key.clone(),
                    operator: *operator,
                    value: if *quoted {
                        LeafValue::Quoted(raw.clone())
                    } else {
                        match typed {
                            cwtools_script_syntax::TypedValue::Integer(v) => LeafValue::Integer(*v),
                            cwtools_script_syntax::TypedValue::Decimal(v) => {
                                LeafValue::Decimal(v.clone())
                            }
                            cwtools_script_syntax::TypedValue::Boolean(v) => LeafValue::Boolean(*v),
                            _ => LeafValue::Text(raw.clone()),
                        }
                    },
                    range: *range,
                }),
                Value::Colour { raw, .. } => ProcessedItem::Leaf(Leaf {
                    key: key.clone(),
                    operator: *operator,
                    value: LeafValue::Colour(raw.clone()),
                    range: *range,
                }),
            },
            Item::Bare { raw, .. } => ProcessedItem::LeafValue(LeafValue::Text(raw.clone())),
            Item::Comment { raw, range } => ProcessedItem::Comment(Comment {
                text: raw.clone(),
                range: *range,
            }),
        })
        .collect()
}
fn render_value(v: &LeafValue) -> String {
    match v {
        LeafValue::Quoted(x) => format!("\"{x}\""),
        LeafValue::Text(x) | LeafValue::Decimal(x) | LeafValue::Colour(x) => x.clone(),
        LeafValue::Integer(x) => x.to_string(),
        LeafValue::Boolean(x) => {
            if *x {
                "yes".into()
            } else {
                "no".into()
            }
        }
    }
}
fn render(xs: &[ProcessedItem], d: usize) -> String {
    let mut s = String::new();
    for x in xs {
        s.push_str(&"\t".repeat(d));
        match x {
            ProcessedItem::Comment(v) => {
                s.push_str(&v.text);
                s.push('\n');
            }
            ProcessedItem::LeafValue(v) => {
                s.push_str(&render_value(v));
                s.push('\n');
            }
            ProcessedItem::ValueClause(v) => {
                s.push_str("{\n");
                s.push_str(&render(&v.children, d + 1));
                s.push_str(&"\t".repeat(d));
                s.push_str("}\n");
            }
            ProcessedItem::Leaf(v) => {
                s.push_str(&v.key);
                s.push(' ');
                s.push_str(v.operator.text());
                s.push(' ');
                s.push_str(&render_value(&v.value));
                s.push('\n');
            }
            ProcessedItem::Node(v) => {
                s.push_str(&v.key);
                s.push(' ');
                s.push_str(v.operator.text());
                s.push_str(" {\n");
                s.push_str(&render(&v.children, d + 1));
                s.push_str(&"\t".repeat(d));
                s.push_str("}\n");
            }
        }
    }
    s
}

pub fn normalize_parameter_key(key: &str) -> String {
    key.trim()
        .trim_matches('$')
        .split('|')
        .next()
        .unwrap_or_default()
        .to_owned()
}
pub fn substitute_params(input: &str, params: &[(String, String)]) -> String {
    let map: BTreeMap<_, _> = params
        .iter()
        .filter_map(|(k, v)| {
            let n = normalize_parameter_key(k);
            (!n.is_empty()).then_some((n, v))
        })
        .collect();
    let mut out = String::new();
    let mut rest = input;
    while let Some(a) = rest.find('$') {
        out.push_str(&rest[..a]);
        let Some(b) = rest[a + 1..].find('$') else {
            out.push_str(&rest[a..]);
            return out;
        };
        let expression = &rest[a + 1..a + 1 + b];
        let mut parts = expression.splitn(2, '|');
        let name = parts.next().unwrap_or_default();
        if let Some(v) = map.get(name) {
            out.push_str(v);
        } else if let Some(default) = parts.next() {
            out.push_str(default);
        } else {
            out.push('$');
            out.push_str(expression);
            out.push('$');
        }
        rest = &rest[a + b + 2..];
    }
    out.push_str(rest);
    out
}
fn target_name(value: &str) -> String {
    let mut raw = value.trim();
    while raw.len() >= 13 && raw[..13].eq_ignore_ascii_case("event_target:") {
        raw = &raw[13..];
    }
    let at = raw.find('@');
    let dot = raw.find('.');
    let end = if at.is_some() && (dot.is_none() || dot > at) {
        raw.len()
    } else {
        dot.unwrap_or(raw.len())
    };
    raw[..end].trim_end_matches('?').to_owned()
}
fn all_leaves(doc: &ProcessedDocument) -> Bounded<&Leaf> {
    doc.leaves()
}
pub fn find_used_targets(doc: &ProcessedDocument) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for node in doc.nodes().items {
        if node.key.to_ascii_lowercase().starts_with("event_target:") {
            out.insert(target_name(&node.key));
        }
    }
    for leaf in all_leaves(doc).items {
        let value = leaf.value.text();
        if value.to_ascii_lowercase().starts_with("event_target:") {
            out.insert(target_name(&value));
        }
    }
    out
}
pub fn find_saved_targets(doc: &ProcessedDocument) -> BTreeSet<String> {
    all_leaves(doc)
        .items
        .into_iter()
        .filter(|x| x.key == "save_event_target_as")
        .map(|x| x.value.text())
        .collect()
}
pub fn find_exists_targets(doc: &ProcessedDocument) -> BTreeSet<String> {
    all_leaves(doc)
        .items
        .into_iter()
        .filter(|x| {
            x.key == "exists"
                && x.value
                    .text()
                    .to_ascii_lowercase()
                    .starts_with("event_target:")
        })
        .map(|x| target_name(&x.value.text()))
        .collect()
}
pub fn find_global_event_targets(doc: &ProcessedDocument) -> BTreeSet<String> {
    all_leaves(doc)
        .items
        .into_iter()
        .filter(|x| x.key == "save_global_event_target_as")
        .map(|x| x.value.text())
        .collect()
}
pub fn fired_on_actions(doc: &ProcessedDocument) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for node in doc.nodes().items {
        if node.key == "fire_on_action" {
            for child in &node.children {
                if let ProcessedItem::Leaf(x) = child {
                    if x.key == "on_action" {
                        out.insert(x.value.text());
                    }
                }
            }
        }
    }
    out
}
pub fn static_modifier_category(name: &str) -> Option<&'static str> {
    let x = name.to_ascii_lowercase();
    if x.contains("ship") || x.contains("fleet") {
        Some("ship")
    } else if x.contains("planet") || x.contains("colony") {
        Some("planet")
    } else if x.contains("pop") || x.contains("species") {
        Some("pop")
    } else if x.contains("country") || x.contains("empire") {
        Some("country")
    } else {
        None
    }
}
