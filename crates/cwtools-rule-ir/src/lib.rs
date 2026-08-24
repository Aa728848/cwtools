#![forbid(unsafe_code)]
#![allow(
    clippy::struct_excessive_bools,
    clippy::semicolon_if_nothing_returned,
    clippy::too_many_lines
)]

use cwtools_cwt_syntax::{ByteRange, CstNode, parse_cwt};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Severity {
    Hint,
    Info,
    Warning,
    Error,
    Opaque(String),
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ReplaceScopes {
    pub root: Option<String>,
    pub this: Option<String>,
    pub froms: Option<Vec<String>>,
    pub prevs: Option<Vec<String>>,
}
#[derive(Clone, Debug, PartialEq)]
pub struct Options {
    pub min: i32,
    pub max: i32,
    pub strict_min: bool,
    pub leafvalue: bool,
    pub description: Option<String>,
    pub push_scope: Option<String>,
    pub replace_scopes: Option<ReplaceScopes>,
    pub severity: Option<Severity>,
    pub required_scopes: Vec<String>,
    pub comparison: bool,
    pub reference_details: Option<(bool, String)>,
    pub key_required_quotes: bool,
    pub value_required_quotes: bool,
    pub forbidden_quoted_values: Vec<String>,
    pub type_hint: Option<(String, bool)>,
    pub completion_type: Option<String>,
    pub error_if_only_match: Option<String>,
    pub type_prefix_from: Option<String>,
    pub type_suffix_patterns: Vec<String>,
    pub file_extensions: Vec<String>,
    pub color_type: Option<String>,
    pub inject: Option<String>,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            min: 0,
            max: 1000,
            strict_min: true,
            leafvalue: false,
            description: None,
            push_scope: None,
            replace_scopes: None,
            severity: None,
            required_scopes: vec![],
            comparison: false,
            reference_details: None,
            key_required_quotes: false,
            value_required_quotes: false,
            forbidden_quoted_values: vec![],
            type_hint: None,
            completion_type: None,
            error_if_only_match: None,
            type_prefix_from: None,
            type_suffix_patterns: vec![],
            file_extensions: vec![],
            color_type: None,
            inject: None,
        }
    }
}
#[derive(Clone, Debug, PartialEq)]
pub enum ValueType {
    Scalar,
    Enum(String),
    Float(f64, f64),
    Bool,
    Int(i64, i64),
    Percent,
    Date,
    DateTime,
    CK2DNA,
    CK2DNAProperty,
    IRFamilyName,
    STLNameFormat(String),
    Opaque(String),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeType {
    Simple(String),
    Complex {
        prefix: String,
        name: String,
        suffix: String,
    },
}
#[derive(Clone, Debug, PartialEq)]
pub enum NewField {
    Value(ValueType),
    Specific(String),
    Scalar,
    Type(TypeType),
    Scope(Vec<String>),
    Localisation {
        synced: bool,
        inline: bool,
    },
    Filepath {
        prefix: Option<String>,
        extension: Option<String>,
    },
    Aliases(String),
    SingleAlias(String),
    Opaque(String),
}
#[derive(Clone, Debug, PartialEq)]
pub enum RuleKind {
    Node {
        left: NewField,
        rules: Vec<NewRule>,
    },
    Leaf {
        left: NewField,
        right: NewField,
    },
    LeafValue {
        right: NewField,
    },
    ValueClause {
        rules: Vec<NewRule>,
    },
    Subtype {
        name: String,
        primary: bool,
        rules: Vec<NewRule>,
    },
    Opaque(String),
}
#[derive(Clone, Debug, PartialEq)]
pub struct NewRule {
    pub kind: RuleKind,
    pub options: Options,
    pub range: ByteRange,
    pub comments: Vec<String>,
}
#[derive(Clone, Debug, PartialEq)]
pub enum RootRule {
    Alias(String, NewRule),
    SingleAlias(String, NewRule),
    Type(String, NewRule),
    Ordinary(String, NewRule),
}
#[derive(Clone, Debug, PartialEq, Default)]
pub struct SubtypeDefinition {
    pub name: String,
    pub display_name: Option<String>,
    pub abbreviation: Option<String>,
    pub rules: Vec<NewRule>,
    pub type_key_field: Option<String>,
    pub type_key_regex: Option<String>,
    pub starts_with: Option<String>,
    pub push_scope: Option<String>,
    pub replace_scopes: Option<ReplaceScopes>,
    pub localisation: Vec<String>,
    pub only_if_not: Vec<String>,
    pub modifiers: Vec<String>,
}
#[derive(Clone, Debug, PartialEq, Default)]
pub struct TypeDefinition {
    pub name: String,
    pub name_field: Option<String>,
    pub path: Option<String>,
    pub path_file: Option<String>,
    pub conditions: Option<String>,

    pub subtypes: Vec<SubtypeDefinition>,
    pub type_key_filter: Option<(Vec<String>, bool)>,
    pub type_key_regex: Option<String>,
    pub root_completion_from_subtypes: bool,
    pub skip_root_key: Vec<String>,
    pub starts_with: Option<String>,
    pub type_per_file: bool,
    pub key_prefix: Option<String>,
    pub warning_only: bool,
    pub unique: bool,
    pub should_be_referenced: Option<String>,
    pub unknown_key_handling: Option<String>,
    pub obsolete_keys: BTreeMap<String, String>,
    pub localisation: Vec<String>,
    pub graph_related_types: Vec<String>,
    pub modifiers: Vec<String>,
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct EnumDefinition {
    pub key: String,
    pub description: String,
    pub values: Vec<String>,
    pub values_with_range: Vec<(String, Option<ByteRange>)>,
}
#[derive(Clone, Debug, PartialEq, Default)]
pub struct ComplexEnumDef {
    pub name: String,
    pub description: String,
    pub path: Option<String>,
    pub path_file: Option<String>,
    pub start_from_root: bool,
    pub opaque: String,
    /// The optional name tree, retained as parsed rules rather than flattened text.
    pub name_tree: Option<Vec<NewRule>>,
    /// Range of the complete `complex_enum` assignment in the source.
    pub range: Option<ByteRange>,
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct MetadataEntry {
    pub values: Vec<String>,
    pub value_ranges: Vec<ByteRange>,
    pub range: Option<ByteRange>,
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ExtendedMetadata {
    pub sections: BTreeMap<String, BTreeMap<String, String>>,
    pub priorities: Vec<MetadataEntry>,
    pub override_modes_info: BTreeMap<String, MetadataEntry>,
    pub system_scopes: BTreeMap<String, MetadataEntry>,
    pub locales: BTreeMap<String, MetadataEntry>,
    pub database_object_types: BTreeMap<String, MetadataEntry>,
    pub on_actions: BTreeMap<String, MetadataEntry>,
    pub raw_ranges: BTreeMap<String, Vec<ByteRange>>,
}
#[derive(Clone, Debug, PartialEq)]
pub struct Document {
    pub file: String,
    pub rules: Vec<RootRule>,
    pub types: Vec<TypeDefinition>,
    pub enums: Vec<EnumDefinition>,
    pub complex_enums: Vec<ComplexEnumDef>,
    pub metadata: ExtendedMetadata,
    pub values: Vec<NewField>,
    pub directives: BTreeMap<usize, Options>,
    pub comments: Vec<String>,
    pub order: Vec<String>,
    pub source: String,
}

fn text(n: &CstNode) -> String {
    match n {
        CstNode::Bare { token } => token.value.clone(),
        CstNode::Assignment { key, value, .. } => format!("{} = {}", text(key), text(value)),
        CstNode::Clause { children, .. } => format!(
            "{{{}}}",
            children.iter().map(text).collect::<Vec<_>>().join(" ")
        ),
        CstNode::ColourLiteral { raw, .. } => raw.clone(),
        CstNode::Comment { token } | CstNode::Trivia { token } | CstNode::Error { token } => {
            token.value.clone()
        }
    }
}
fn key(n: &CstNode) -> String {
    match n {
        CstNode::Bare { token } => token.value.clone(),
        _ => text(n),
    }
}
fn number<T: std::str::FromStr>(s: &str, inf: T) -> T {
    s.trim().parse().unwrap_or(inf)
}
fn typed(s: &str) -> NewField {
    let s = s.trim();
    if s == "scalar" {
        return NewField::Scalar;
    }
    if s == "bool" {
        return NewField::Value(ValueType::Bool);
    }
    if s == "percent" {
        return NewField::Value(ValueType::Percent);
    }
    if s == "localisation" {
        return NewField::Localisation {
            synced: false,
            inline: false,
        };
    }
    if let Some(x) = s.strip_prefix("enum[").and_then(|x| x.strip_suffix(']')) {
        return NewField::Value(ValueType::Enum(x.to_owned()));
    }
    for (prefix, is_float) in [("float[", true), ("int[", false)] {
        if let Some(x) = s.strip_prefix(prefix).and_then(|x| x.strip_suffix(']')) {
            let mut p = x.split("..");
            let a = p.next().unwrap_or("");
            let b = p.next().unwrap_or("");
            return if is_float {
                NewField::Value(ValueType::Float(
                    if a.eq_ignore_ascii_case("-inf") {
                        -f64::MAX
                    } else {
                        number(a, f64::MIN)
                    },
                    if b.eq_ignore_ascii_case("inf") {
                        f64::MAX
                    } else {
                        number(b, f64::MAX)
                    },
                ))
            } else {
                NewField::Value(ValueType::Int(number(a, i64::MIN), number(b, i64::MAX)))
            };
        }
    }
    if let Some(x) = s.strip_prefix("scope[").and_then(|x| x.strip_suffix(']')) {
        return NewField::Scope(
            x.split(',')
                .map(|v| v.trim().to_owned())
                .filter(|v| !v.is_empty())
                .collect(),
        );
    }
    if let Some(x) = s
        .strip_prefix("filepath[")
        .and_then(|x| x.strip_suffix(']'))
    {
        let mut p = x.split('|');
        return NewField::Filepath {
            prefix: Some(p.next().unwrap_or("").to_owned()).filter(|v| !v.is_empty()),
            extension: p.next().map(str::to_owned),
        };
    }
    if s == "filepath" {
        return NewField::Filepath {
            prefix: None,
            extension: None,
        };
    }
    if let Some(x) = s
        .strip_prefix("localisation[")
        .and_then(|x| x.strip_suffix(']'))
    {
        return NewField::Localisation {
            synced: x.contains("synced"),
            inline: x.contains("inline"),
        };
    }
    if let Some(x) = s.strip_prefix("<").and_then(|x| x.strip_suffix('>')) {
        return NewField::Type(TypeType::Simple(x.to_owned()));
    }
    if let Some(start) = s.find('<') {
        if let Some(end) = s[start..].find('>') {
            let end = start + end;
            return NewField::Type(TypeType::Complex {
                prefix: s[..start].to_owned(),
                name: s[start + 1..end].to_owned(),
                suffix: s[end + 1..].to_owned(),
            });
        }
    }
    if let Some(x) = s.strip_prefix("alias[").and_then(|x| x.strip_suffix(']')) {
        return NewField::Aliases(x.to_owned());
    }
    if let Some(x) = s
        .strip_prefix("single_alias_right[")
        .or_else(|| s.strip_prefix("single_alias["))
        .and_then(|x| x.strip_suffix(']'))
    {
        return NewField::SingleAlias(x.to_owned());
    }
    match s {
        "date" | "date_field" => NewField::Value(ValueType::Date),
        "datetime" | "datetime_field" => NewField::Value(ValueType::DateTime),
        "CK2DNA" => NewField::Value(ValueType::CK2DNA),
        _ => NewField::Specific(s.to_owned()),
    }
}
fn field(n: &CstNode) -> NewField {
    match n {
        CstNode::Bare { token } => typed(&token.value),
        _ => NewField::Opaque(text(n)),
    }
}
fn yes(value: Option<String>) -> bool {
    value.is_some_and(|x| matches!(x.as_str(), "yes" | "true" | "1"))
}
fn filter_value(value: &str) -> (Vec<String>, bool) {
    let negated = value.contains("<>");
    let values = value
        .trim_matches('{')
        .trim_matches('}')
        .split_whitespace()
        .map(str::to_owned)
        .collect();
    (values, !negated)
}
fn directive(line: &str, o: &mut Options) {
    let x = line
        .trim()
        .trim_start_matches('#')
        .trim_start_matches('#')
        .trim();
    let mut p = x.splitn(2, '=');
    let name = p.next().unwrap_or("").trim();
    let value = p.next().unwrap_or("").trim();
    match name {
        "cardinality" => {
            let mut q = value.split("..");
            o.min = number(q.next().unwrap_or(""), 0);
            let upper = q.next().unwrap_or("");
            o.max = if upper.eq_ignore_ascii_case("inf") {
                i32::MAX
            } else {
                number(upper, 1000)
            }
        }
        "required" => o.required_scopes.extend(
            value
                .split(',')
                .map(|s| s.trim().to_owned())
                .filter(|s| !s.is_empty()),
        ),
        "severity" => {
            o.severity = Some(match value {
                "hint" => Severity::Hint,
                "info" => Severity::Info,
                "warning" => Severity::Warning,
                "error" => Severity::Error,
                x => Severity::Opaque(x.to_owned()),
            })
        }
        "scope" => o.push_scope = Some(value.to_owned()),
        "comparison" => o.comparison = !matches!(value, "false" | "0"),
        "description" => o.description = Some(value.to_owned()),
        "inject" => o.inject = Some(value.to_owned()),
        _ => {}
    }
}
fn options(comments: &[String]) -> Options {
    let mut o = Options {
        min: 1,
        max: 1,
        ..Options::default()
    };
    for c in comments {
        directive(c, &mut o)
    }
    o
}
fn comments_children<'a>(
    nodes: &'a [CstNode],
    pending: &mut Vec<String>,
) -> Vec<(Vec<String>, &'a CstNode)> {
    let mut out = Vec::new();
    for n in nodes {
        match n {
            CstNode::Comment { token } => pending.push(token.value.clone()),
            CstNode::Trivia { .. } => {}
            _ => {
                out.push((std::mem::take(pending), n));
            }
        }
    }
    out
}
fn make_rule(n: &CstNode, pending: Vec<String>) -> Option<(String, NewRule)> {
    if let CstNode::Assignment {
        key: k,
        value,
        range,
        ..
    } = n
    {
        let name = key(k);
        let o = options(&pending);
        let kind = match value.as_ref() {
            CstNode::Clause { children, .. } => {
                let mut p = Vec::new();
                let rs = comments_children(children, &mut p)
                    .into_iter()
                    .filter_map(|(c, x)| make_rule(x, c).map(|(_, r)| r))
                    .collect();
                RuleKind::Node {
                    left: field(k),
                    rules: rs,
                }
            }
            _ => RuleKind::Leaf {
                left: field(k),
                right: field(value),
            },
        };
        Some((
            name,
            NewRule {
                kind,
                options: o,
                range: *range,
                comments: pending,
            },
        ))
    } else {
        None
    }
}
fn props(clause: &CstNode, name: &str) -> Vec<String> {
    match clause {
        CstNode::Clause { children, .. } => children
            .iter()
            .filter_map(|n| match n {
                CstNode::Assignment {
                    key: field_key,
                    value,
                    ..
                } if key(field_key) == name => Some(text(value).trim_matches('"').to_owned()),
                _ => None,
            })
            .collect(),
        _ => vec![],
    }
}
fn prop(clause: &CstNode, name: &str) -> Option<String> {
    if let CstNode::Clause { children, .. } = clause {
        for n in children {
            if let CstNode::Assignment {
                key: field_key,
                value,
                ..
            } = n
            {
                if key(field_key) == name {
                    return Some(text(value).trim_matches('"').to_owned());
                }
            }
        }
    }
    None
}
fn bare_values(clause: &CstNode) -> Vec<(String, Option<ByteRange>)> {
    match clause {
        CstNode::Clause { children, .. } => children
            .iter()
            .filter_map(|n| match n {
                CstNode::Bare { token } => Some((token.value.clone(), Some(token.range))),
                CstNode::Assignment { key: k, range, .. } => Some((key(k), Some(*range))),
                _ => None,
            })
            .collect(),
        _ => vec![],
    }
}

fn complex_enum(name: &str, clause: &CstNode, range: Option<ByteRange>) -> ComplexEnumDef {
    let name_tree = if let CstNode::Clause { children, .. } = clause {
        children.iter().find_map(|n| match n {
            CstNode::Assignment { key: k, value, .. } if key(k) == "name" => {
                if let CstNode::Clause { children, .. } = value.as_ref() {
                    let mut pending = Vec::new();
                    Some(
                        comments_children(children, &mut pending)
                            .into_iter()
                            .filter_map(|(c, n)| make_rule(n, c).map(|(_, r)| r))
                            .collect(),
                    )
                } else {
                    None
                }
            }
            _ => None,
        })
    } else {
        None
    };
    ComplexEnumDef {
        name: name.to_owned(),
        description: prop(clause, "description").unwrap_or_default(),
        path: prop(clause, "path"),
        path_file: prop(clause, "path_file"),
        start_from_root: prop(clause, "start_from_root").is_some_and(|x| x == "yes" || x == "true"),
        opaque: text(clause),
        name_tree,
        range,
    }
}

fn type_def(name: &str, clause: &CstNode) -> TypeDefinition {
    let mut t = TypeDefinition {
        name: name.to_owned(),
        ..Default::default()
    };
    t.path = prop(clause, "path");
    t.path_file = prop(clause, "path_file");
    t.name_field = prop(clause, "name_field");
    t.starts_with = prop(clause, "starts_with");
    t.skip_root_key = props(clause, "skip_root_key");
    t.type_key_filter = prop(clause, "type_key_filter").map(|v| filter_value(&v));
    t.type_per_file = yes(prop(clause, "type_per_file"));
    t.unique = yes(prop(clause, "unique"));
    t.warning_only = yes(prop(clause, "warning_only"));
    if let CstNode::Clause { children, .. } = clause {
        // Only explicit subtype[...] assignments define subtypes. Ordinary
        // properties belong to the type itself and must never be reclassified.
        let mut declaration_comments = Vec::new();
        for (comments, n) in comments_children(children, &mut declaration_comments) {
            if let CstNode::Assignment { key: k, value, .. } = n {
                let k = key(k);
                if let Some(subtype) = k.strip_prefix("subtype[").and_then(|x| x.strip_suffix(']'))
                {
                    if let CstNode::Clause { .. } = value.as_ref() {
                        let mut s = SubtypeDefinition {
                            name: subtype.to_owned(),
                            ..Default::default()
                        };
                        for comment in &comments {
                            let body = comment
                                .trim()
                                .trim_start_matches('#')
                                .trim_start_matches('#')
                                .trim();
                            if let Some(value) = body
                                .strip_prefix("push_scope")
                                .and_then(|rest| rest.trim().strip_prefix('='))
                            {
                                s.push_scope = Some(value.trim().to_owned());
                            }
                            if let Some(value) = body
                                .strip_prefix("starts_with")
                                .and_then(|rest| rest.trim().strip_prefix('='))
                            {
                                s.starts_with = Some(value.trim().to_owned());
                            }
                        }
                        if let CstNode::Clause {
                            children: subchildren,
                            ..
                        } = value.as_ref()
                        {
                            let mut pending = Vec::new();
                            s.rules = comments_children(subchildren, &mut pending)
                                .into_iter()
                                .filter_map(|(c, x)| make_rule(x, c).map(|(_, r)| r))
                                .collect();
                        }
                        t.subtypes.push(s);
                    }
                }
            }
        }
    }
    t
}
/// Parse one CWT document into immutable rule IR.
///
/// # Errors
/// Returns syntax diagnostics when the document cannot be parsed.
pub fn parse_document(file: &str, source: &str) -> Result<Document, Vec<String>> {
    let c = parse_cwt(source).map_err(|e| e.into_iter().map(|x| x.message).collect::<Vec<_>>())?;
    let mut d = Document {
        file: file.to_owned(),
        rules: vec![],
        types: vec![],
        enums: vec![],
        complex_enums: vec![],
        metadata: ExtendedMetadata::default(),
        values: vec![],
        directives: BTreeMap::new(),
        comments: vec![],
        order: vec![],
        source: source.to_owned(),
    };
    let mut pending = Vec::new();
    for n in &c.roots {
        match n {
            CstNode::Comment { token } => {
                d.comments.push(token.value.clone());
                pending.push(token.value.clone())
            }
            CstNode::Assignment { key: k, value, .. } => {
                let name = key(k);
                if name == "enums" {
                    if let CstNode::Clause { children, .. } = value.as_ref() {
                        for x in children {
                            if let CstNode::Assignment {
                                key: ek,
                                value: ev,
                                range,
                                ..
                            } = x
                            {
                                let n = key(ek);
                                if let Some(en) =
                                    n.strip_prefix("enum[").and_then(|x| x.strip_suffix(']'))
                                {
                                    let pairs = bare_values(ev);
                                    d.enums.push(EnumDefinition {
                                        key: en.to_owned(),
                                        description: String::new(),
                                        values: pairs.iter().map(|x| x.0.clone()).collect(),
                                        values_with_range: pairs,
                                    });
                                } else if let Some(en) = n
                                    .strip_prefix("complex_enum[")
                                    .and_then(|x| x.strip_suffix(']'))
                                {
                                    d.complex_enums.push(complex_enum(en, ev, Some(*range)));
                                }
                            }
                        }
                    }
                } else if name == "values" {
                    if let CstNode::Clause { children, .. } = value.as_ref() {
                        for x in children {
                            if let CstNode::Assignment { value: ev, .. } = x {
                                d.values.push(field(ev));
                            }
                        }
                    }
                } else if name == "types" {
                    if let CstNode::Clause { children, .. } = value.as_ref() {
                        for x in children {
                            if let CstNode::Assignment {
                                key: k2, value: v2, ..
                            } = x
                            {
                                let n = key(k2);
                                if let Some(t) =
                                    n.strip_prefix("type[").and_then(|x| x.strip_suffix(']'))
                                {
                                    if let CstNode::Clause { .. } = v2.as_ref() {
                                        d.types.push(type_def(t, v2));
                                    }
                                }
                            }
                        }
                    }
                } else if let Some((k, r)) = make_rule(n, std::mem::take(&mut pending)) {
                    d.order.push(k.clone());
                    let (kind, nm) = if let Some(x) = k.strip_prefix("alias[") {
                        ("a", x.trim_end_matches(']'))
                    } else if let Some(x) = k.strip_prefix("single_alias[") {
                        ("s", x.trim_end_matches(']'))
                    } else if let Some(x) = k.strip_prefix("type[") {
                        ("t", x.trim_end_matches(']'))
                    } else {
                        ("o", k.as_str())
                    };
                    d.rules.push(match kind {
                        "a" => RootRule::Alias(nm.to_owned(), r),
                        "s" => RootRule::SingleAlias(nm.to_owned(), r),
                        "t" => RootRule::Type(nm.to_owned(), r),
                        _ => RootRule::Ordinary(nm.to_owned(), r),
                    });
                }
            }
            _ => {}
        }
    }
    for (i, l) in source.lines().enumerate() {
        if l.trim_start().starts_with("##") {
            let mut o = Options {
                min: 1,
                max: 1,
                ..Options::default()
            };
            directive(l, &mut o);
            if o != Options::default() {
                d.directives.insert(i + 1, o);
            }
        }
    }
    Ok(d)
}

#[cfg(test)]
fn rule_options(r: &RootRule) -> &Options {
    match r {
        RootRule::Alias(_, x)
        | RootRule::SingleAlias(_, x)
        | RootRule::Type(_, x)
        | RootRule::Ordinary(_, x) => &x.options,
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn defaults() {
        assert_eq!(Options::default().max, 1000);
        assert_eq!(Options::default().min, 0)
    }
    #[test]
    fn rule_default_cardinality_is_one() {
        let d = parse_document("x", "a = scalar").unwrap();
        assert_eq!(
            (rule_options(&d.rules[0]).min, rule_options(&d.rules[0]).max),
            (1, 1)
        );
    }
    #[test]
    fn cardinality_inf() {
        let d = parse_document("x", "a = scalar\n## cardinality = 2..inf\nb = bool").unwrap();
        assert_eq!(rule_options(&d.rules[1]).min, 2);
        assert_eq!(rule_options(&d.rules[1]).max, i32::MAX)
    }
    #[test]
    fn directives_attach() {
        let d =
            parse_document("x", "## description = one\n## severity = error\na = scalar").unwrap();
        assert_eq!(rule_options(&d.rules[0]).description, Some("one".into()));
    }
    #[test]
    fn all_fields() {
        for s in [
            "scalar",
            "bool",
            "percent",
            "date",
            "datetime",
            "CK2DNA",
            "int[-1..inf]",
            "float[0..1]",
            "enum[x]",
            "scope[a,b]",
            "<x>",
            "pre<x>suf",
            "filepath",
            "alias[x]",
            "single_alias[x]",
            "unknown",
        ] {
            let _ = typed(s);
        }
    }
    #[test]
    fn unknown_specific() {
        assert_eq!(typed("newthing"), NewField::Specific("newthing".into()))
    }
    #[test]
    fn rules() {
        let d = parse_document("x", "a = scalar\nb = bool").unwrap();
        assert_eq!(d.rules.len(), 2)
    }
    #[test]
    fn types() {
        let d = parse_document(
            "x",
            "types = { type[event] = { path = game/events unique = yes } }",
        )
        .unwrap();
        assert_eq!(d.types[0].name, "event");
        assert_eq!(d.types[0].path.as_deref(), Some("game/events"))
    }
    #[test]
    fn aliases() {
        let d = parse_document("x", "alias[x] = scalar\nsingle_alias[y] = bool").unwrap();
        assert!(matches!(d.rules[0], RootRule::Alias(..)));
        assert!(matches!(d.rules[1], RootRule::SingleAlias(..)))
    }
    #[test]
    fn comparison() {
        let d = parse_document("x", "## comparison = true\na = scalar").unwrap();
        assert!(rule_options(&d.rules[0]).comparison)
    }
    #[test]
    fn required() {
        let d = parse_document("x", "## required = root,this\na = scalar").unwrap();
        assert_eq!(rule_options(&d.rules[0]).required_scopes.len(), 2)
    }
    #[test]
    fn comments() {
        let d = parse_document("x", "## hi\na = scalar").unwrap();
        assert_eq!(d.comments.len(), 1)
    }
    #[test]
    fn source() {
        let s = "a = scalar";
        assert_eq!(parse_document("x", s).unwrap().source, s)
    }
    #[test]
    fn order() {
        let d = parse_document("x", "b = scalar\na = scalar").unwrap();
        assert_eq!(d.order, ["b", "a"])
    }
    #[test]
    fn nested() {
        let d = parse_document("x", "a = { b = scalar }").unwrap();
        assert!(matches!(d.rules[0], RootRule::Ordinary(..)))
    }
    #[test]
    fn severity() {
        let d = parse_document("x", "## severity = warning\na = scalar").unwrap();
        assert_eq!(rule_options(&d.rules[0]).severity, Some(Severity::Warning))
    }
    #[test]
    fn inject() {
        let d = parse_document("x", "## inject = x\na = scalar").unwrap();
        assert_eq!(rule_options(&d.rules[0]).inject.as_deref(), Some("x"))
    }
    #[test]
    fn description() {
        let d = parse_document("x", "## description = x\na = scalar").unwrap();
        assert_eq!(rule_options(&d.rules[0]).description.as_deref(), Some("x"))
    }
    #[test]
    fn range() {
        assert!(matches!(
            typed("int[-2..3]"),
            NewField::Value(ValueType::Int(-2, 3))
        ))
    }
    #[test]
    fn complex() {
        assert!(matches!(
            typed("pre<x>suf"),
            NewField::Type(TypeType::Complex { .. })
        ))
    }
    #[test]
    fn filepath() {
        assert!(matches!(typed("filepath"), NewField::Filepath { .. }))
    }
    #[test]
    fn scopes() {
        assert!(matches!(typed("scope[a,b]"), NewField::Scope(_)))
    }
    #[test]
    fn values() {
        assert!(matches!(
            typed("enum[x]"),
            NewField::Value(ValueType::Enum(_))
        ))
    }
}
