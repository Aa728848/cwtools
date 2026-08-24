#![forbid(unsafe_code)]
#![allow(
    clippy::cast_possible_truncation,
    clippy::semicolon_if_nothing_returned
)]
//! Deterministic, single-document CWT language service primitives.
use cwtools_cwt_syntax::{ByteRange, CstNode, parse_cwt_loss_aware};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum DiagnosticSeverity {
    Hint,
    Info,
    Warning,
    Error,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub phase: String,
    pub severity: DiagnosticSeverity,
    pub range: Range,
    pub code: String,
    pub message_key: String,
    pub args: Vec<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum SymbolKind {
    Type,
    Subtype,
    Enum,
    Complex,
    Value,
    Alias,
    SingleAlias,
    Scope,
    ScopeGroup,
    Link,
    ModifierCategory,
    Directive,
    RootDeclaration,
    Field,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    pub range: Range,
    pub detail: Option<String>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reference {
    pub name: String,
    pub kind: SymbolKind,
    pub range: Range,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompletionArgument {
    pub label: String,
    pub detail: Option<String>,
    pub kind: SymbolKind,
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct DocumentModel {
    pub symbols: Vec<Symbol>,
    pub references: Vec<Reference>,
    pub injects: Vec<String>,
    pub root_names: Vec<String>,
    pub completion_arguments: Vec<CompletionArgument>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnalysisResult {
    pub diagnostics: Vec<Diagnostic>,
    pub model: DocumentModel,
}

impl Position {
    fn at(source: &str, byte: usize) -> Self {
        let beyond_eof = byte.saturating_sub(source.len()) as u32;
        let p = &source[..byte.min(source.len())];
        Self {
            line: p.bytes().filter(|b| *b == b'\n').count() as u32,
            character: p
                .rsplit_once('\n')
                .map_or(p, |(_, x)| x)
                .encode_utf16()
                .count() as u32
                + beyond_eof,
        }
    }
}
fn range(source: &str, r: ByteRange) -> Range {
    Range {
        start: Position::at(source, r.start),
        end: Position::at(source, r.end),
    }
}
fn diagnostic(
    source: &str,
    code: &str,
    key: &str,
    r: ByteRange,
    args: Vec<String>,
    severity: DiagnosticSeverity,
    phase: &str,
) -> Diagnostic {
    Diagnostic {
        phase: phase.into(),
        severity,
        range: range(source, r),
        code: code.into(),
        message_key: key.into(),
        args,
    }
}
fn bare(node: &CstNode) -> Option<(&str, ByteRange)> {
    match node {
        CstNode::Bare { token } => Some((&token.value, token.range)),
        _ => None,
    }
}

fn declaration(name: &str) -> Option<(&str, &str, SymbolKind)> {
    let (family, argument) = name.split_once('[')?;
    let argument = argument.strip_suffix(']')?;
    let kind = match family {
        "type" => SymbolKind::Type,
        "subtype" => SymbolKind::Subtype,
        "enum" => SymbolKind::Enum,
        "complex_enum" => SymbolKind::Complex,
        "value" => SymbolKind::Value,
        "alias" => SymbolKind::Alias,
        "single_alias" => SymbolKind::SingleAlias,
        "scope" => SymbolKind::Scope,
        "scope_group" => SymbolKind::ScopeGroup,
        _ => return None,
    };
    Some((family, argument, kind))
}

fn add_completion(model: &mut DocumentModel, family: &str, name: &str, kind: SymbolKind) {
    model.completion_arguments.push(CompletionArgument {
        label: name.to_owned(),
        detail: Some(family.to_owned()),
        kind,
    });
}

fn add_node(node: &CstNode, source: &str, model: &mut DocumentModel, top_block: Option<&str>) {
    match node {
        CstNode::Assignment {
            key,
            value,
            range: assignment_range,
            ..
        } => {
            if let Some((name, _key_range)) = bare(key) {
                if let Some((family, argument, kind)) = declaration(name) {
                    if kind != SymbolKind::Scope {
                        model.symbols.push(Symbol {
                            name: argument.to_owned(),
                            kind,
                            range: range(source, *assignment_range),
                            detail: Some(family.to_owned()),
                        });
                    }
                    if matches!(
                        family,
                        "enum" | "complex_enum" | "value" | "scope" | "scope_group"
                    ) {
                        add_completion(model, family, argument, kind);
                    }
                } else if top_block == Some("links") {
                    if let Some((child, _child_range)) = bare(key) {
                        model.symbols.push(Symbol {
                            name: child.to_owned(),
                            kind: SymbolKind::Link,
                            range: range(source, *assignment_range),
                            detail: Some("links".into()),
                        });
                    }
                } else if top_block == Some("modifier_categories") {
                    model.symbols.push(Symbol {
                        name: name.trim_matches('"').to_owned(),
                        kind: SymbolKind::ModifierCategory,
                        range: range(source, *assignment_range),
                        detail: Some("modifier_categories".into()),
                    });
                }
                scan_value_refs(value, source, model, Some(*assignment_range));
            }
            let nested_top = match bare(key).map(|(x, _)| x) {
                Some(name @ ("links" | "modifier_categories")) => Some(name),
                _ => None,
            };
            if let CstNode::Clause { children, .. } = value.as_ref() {
                for child in children {
                    add_node(child, source, model, nested_top);
                }
            } else {
                add_node(value, source, model, nested_top);
            }
        }
        CstNode::Clause { children, .. } => {
            for child in children {
                add_node(child, source, model, top_block);
            }
        }
        _ => {}
    }
}

fn scan_value_refs(
    node: &CstNode,
    source: &str,
    model: &mut DocumentModel,
    enclosing_range: Option<ByteRange>,
) {
    match node {
        CstNode::Bare { token } => {
            let text = token.value.trim_matches('"');
            let (kind, name) = if let Some((family, value)) = text
                .split_once('[')
                .and_then(|(f, rest)| rest.strip_suffix(']').map(|v| (f, v)))
            {
                match family {
                    "enum" | "complex_enum" => (Some(SymbolKind::Enum), Some(value)),
                    "scope" | "scope_group" => (Some(SymbolKind::Scope), Some(value)),
                    "value_set" | "value" => (Some(SymbolKind::Value), Some(value)),
                    "alias_name" | "alias_match_left" => (Some(SymbolKind::Alias), Some(value)),
                    "single_alias_right" => (Some(SymbolKind::SingleAlias), Some(value)),
                    _ => (None, None),
                }
            } else if text.starts_with('<') && text.ends_with('>') && text.len() > 2 {
                (Some(SymbolKind::Type), Some(&text[1..text.len() - 1]))
            } else if let Some(start) = text.find('<') {
                if let Some(end) = text[start + 1..].find('>') {
                    (
                        Some(SymbolKind::Type),
                        Some(&text[start + 1..start + 1 + end]),
                    )
                } else {
                    (None, None)
                }
            } else {
                (None, None)
            };
            if let (Some(kind), Some(name)) = (kind, name) {
                if let Some((family, _)) = text.split_once('[') {
                    add_completion(model, family, name, kind);
                }
                model.references.push(Reference {
                    name: name.to_owned(),
                    kind,
                    range: range(source, enclosing_range.unwrap_or(token.range)),
                });
            }
        }
        CstNode::Clause { children, .. } => {
            for child in children {
                scan_value_refs(child, source, model, enclosing_range);
            }
        }
        CstNode::Assignment { value, range, .. } => {
            scan_value_refs(value, source, model, Some(*range))
        }
        _ => {}
    }
}

/// Analyze one CWT document without workspace state.
#[must_use]
pub fn analyze_document(source: &str) -> AnalysisResult {
    let parsed = parse_cwt_loss_aware(source);
    let mut result = AnalysisResult {
        diagnostics: Vec::new(),
        model: DocumentModel::default(),
    };
    for e in parsed.diagnostics {
        let offset = if e.message.contains("unclosed clause") {
            source.len().saturating_add(1)
        } else {
            e.offset
        };
        let r = ByteRange {
            start: offset,
            end: offset,
        };
        result.diagnostics.push(diagnostic(
            source,
            "CWT001",
            "cwt.syntaxError",
            r,
            vec![e.message],
            DiagnosticSeverity::Error,
            "syntax",
        ));
    }
    for root in &parsed.cst.roots {
        if let CstNode::Assignment { key, .. } = root {
            if let Some((name, declaration_range)) = bare(key) {
                if declaration(name).is_none() {
                    let trimmed = name.trim_matches('"');
                    if !matches!(
                        trimmed,
                        "types"
                            | "enums"
                            | "values"
                            | "links"
                            | "modifier_categories"
                            | "scopes"
                            | "scope_groups"
                    ) && !trimmed.starts_with("alias[")
                        && !trimmed.starts_with("single_alias[")
                    {
                        result.model.root_names.push(trimmed.to_owned());
                        result.model.symbols.push(Symbol {
                            name: trimmed.to_owned(),
                            kind: SymbolKind::RootDeclaration,
                            range: range(source, declaration_range),
                            detail: None,
                        });
                    }
                }
            }
        }
        add_node(root, source, &mut result.model, None);
        scan_semantic_nodes(root, source, &mut result);
    }
    scan_directives(source, &mut result);
    scan_injects(source, &mut result);
    result.model.root_names.sort();
    result.model.root_names.dedup();
    result.model.symbols.sort_by(|a, b| {
        a.range
            .start
            .line
            .cmp(&b.range.start.line)
            .then(a.name.cmp(&b.name))
    });
    result.diagnostics.sort_by(|a, b| {
        a.code
            .cmp(&b.code)
            .then(a.range.start.line.cmp(&b.range.start.line))
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
    result
        .diagnostics
        .dedup_by(|a, b| a.code == b.code && a.message_key == b.message_key && a.range == b.range);
    result
        .model
        .references
        .sort_by(|a, b| a.kind.cmp(&b.kind).then(a.name.cmp(&b.name)));
    result
        .model
        .references
        .dedup_by(|a, b| a.kind == b.kind && a.name == b.name);
    result
        .model
        .symbols
        .retain(|symbol| symbol.kind != SymbolKind::RootDeclaration);
    result.model.completion_arguments.sort_by(|a, b| {
        a.label
            .cmp(&b.label)
            .then(a.detail.cmp(&b.detail))
            .then(a.kind.cmp(&b.kind))
    });
    result
        .model
        .completion_arguments
        .dedup_by(|a, b| a.label == b.label && a.detail == b.detail && a.kind == b.kind);
    result
}
#[allow(clippy::too_many_lines)]
fn scan_semantic_nodes(node: &CstNode, source: &str, result: &mut AnalysisResult) {
    match node {
        CstNode::Assignment {
            key,
            value,
            range: assignment_range,
            ..
        } => {
            if let Some((name, key_range)) = bare(key) {
                if let Some((family, argument, _)) = declaration(name) {
                    if argument.is_empty() {
                        result.diagnostics.push(diagnostic(
                            source,
                            "CWT113",
                            "cwt.emptyDeclaration",
                            *assignment_range,
                            vec![family.into()],
                            DiagnosticSeverity::Error,
                            "expression",
                        ));
                    }
                }
                if let CstNode::Bare { token } = value.as_ref() {
                    let text = token.value.as_str();
                    if let Some(open) = text.find('[') {
                        let family = &text[..open];
                        if declaration(name).is_none() {
                            let known = [
                                "int",
                                "float",
                                "value_field",
                                "int_value_field",
                                "variable_field",
                                "int_variable_field",
                                "variable_field_32",
                                "int_variable_field_32",
                                "enum",
                                "complex_enum",
                                "value",
                                "value_set",
                                "dynamic_value",
                                "prefix_field",
                                "alias_name",
                                "alias_match_left",
                                "alias_keys_field",
                                "alias_params_field",
                                "single_alias_right",
                                "scope",
                                "scope_group",
                                "event_target",
                                "colour",
                                "color",
                                "filepath",
                                "filename",
                                "icon",
                                "name_format",
                                "stellaris_name_format",
                            ];
                            let valid = text.ends_with(']')
                                && text.len() > open + 2
                                && (!matches!(
                                    family,
                                    "int"
                                        | "float"
                                        | "value_field"
                                        | "int_value_field"
                                        | "variable_field"
                                        | "int_variable_field"
                                        | "variable_field_32"
                                        | "int_variable_field_32"
                                ) || text[open + 1..text.len() - 1].contains(".."));
                            if known.contains(&family) && !valid {
                                result.diagnostics.push(diagnostic(
                                    source,
                                    "CWT201",
                                    "cwt.illegalFieldExpression",
                                    *assignment_range,
                                    vec![family.into(), text.into()],
                                    DiagnosticSeverity::Error,
                                    "expression",
                                ));
                            } else if !known.contains(&family) {
                                result.diagnostics.push(diagnostic(
                                    source,
                                    "CWT200",
                                    "cwt.unknownFieldExpression",
                                    *assignment_range,
                                    vec![text.into()],
                                    DiagnosticSeverity::Warning,
                                    "expression",
                                ));
                            }
                        }
                    }
                }
                if let CstNode::Clause { children, .. } = value.as_ref() {
                    if matches!(name, "types" | "enums" | "values") {
                        for child in children {
                            if let CstNode::Assignment {
                                key: child_key,
                                range: child_range,
                                ..
                            } = child
                            {
                                let child_name = bare(child_key).map_or("", |(x, _)| x);
                                let expected = match name {
                                    "types" => ["type"].as_slice(),
                                    "enums" => ["enum", "complex_enum"].as_slice(),
                                    _ => ["value"].as_slice(),
                                };
                                if let Some((cf, arg, _)) = declaration(child_name) {
                                    if arg.is_empty() {
                                        result.diagnostics.push(diagnostic(
                                            source,
                                            "CWT113",
                                            "cwt.emptyDeclaration",
                                            *child_range,
                                            vec![cf.into()],
                                            DiagnosticSeverity::Error,
                                            "expression",
                                        ));
                                    }
                                    if !expected.contains(&cf) {
                                        result.diagnostics.push(diagnostic(
                                            source,
                                            match name {
                                                "types" => "CWT110",
                                                "enums" => "CWT111",
                                                _ => "CWT112",
                                            },
                                            match name {
                                                "types" => "cwt.invalidTypesDeclaration",
                                                "enums" => "cwt.invalidEnumsDeclaration",
                                                _ => "cwt.invalidValuesDeclaration",
                                            },
                                            *child_range,
                                            vec![],
                                            DiagnosticSeverity::Warning,
                                            "expression",
                                        ));
                                    }
                                } else if !child_name.is_empty() {
                                    result.diagnostics.push(diagnostic(
                                        source,
                                        match name {
                                            "types" => "CWT110",
                                            "enums" => "CWT111",
                                            _ => "CWT112",
                                        },
                                        match name {
                                            "types" => "cwt.invalidTypesDeclaration",
                                            "enums" => "cwt.invalidEnumsDeclaration",
                                            _ => "cwt.invalidValuesDeclaration",
                                        },
                                        *child_range,
                                        vec![],
                                        DiagnosticSeverity::Warning,
                                        "expression",
                                    ));
                                }
                            }
                        }
                    }
                    for child in children {
                        scan_semantic_nodes(child, source, result);
                    }
                } else {
                    scan_semantic_nodes(value, source, result);
                }
                let _ = key_range;
            }
        }
        CstNode::Clause { children, .. } => {
            for child in children {
                scan_semantic_nodes(child, source, result);
            }
        }
        _ => {}
    }
}

#[allow(clippy::too_many_lines, clippy::if_not_else)]
fn scan_directives(source: &str, result: &mut AnalysisResult) {
    let mut offset = 0usize;
    for line in source.split_inclusive('\n') {
        let content = line
            .strip_suffix('\n')
            .unwrap_or(line)
            .strip_suffix('\r')
            .unwrap_or(line.strip_suffix('\n').unwrap_or(line));
        let t = content.trim();
        if t.starts_with("##") {
            let hash = content.find("##").unwrap_or(0);
            let body = content[hash + 2..].trim();
            let comment_range = ByteRange {
                start: offset + hash,
                end: offset + line.len(),
            };
            let (name, value, eq_pos) = if let Some(eq) = body.find('=') {
                (body[..eq].trim(), Some(body[eq + 1..].trim()), Some(eq))
            } else {
                (body.trim(), None, None)
            };
            let known = [
                "cardinality",
                "severity",
                "description",
                "scope",
                "comparison",
                "inject",
                "required",
                "push_scope",
                "replace_scope",
                "file_extensions",
                "forbid_quoted_values",
            ];
            if !known.contains(&name) {
                result.diagnostics.push(diagnostic(
                    source,
                    "CWT101",
                    "cwt.unknownDirective",
                    comment_range,
                    vec![name.into()],
                    DiagnosticSeverity::Warning,
                    "structure",
                ));
            } else {
                let value = value.filter(|v| !v.is_empty());
                if value.is_none()
                    && matches!(
                        name,
                        "cardinality"
                            | "severity"
                            | "scope"
                            | "comparison"
                            | "inject"
                            | "push_scope"
                            | "replace_scope"
                            | "file_extensions"
                    )
                {
                    result.diagnostics.push(diagnostic(
                        source,
                        "CWT104",
                        "cwt.directiveMissingValue",
                        comment_range,
                        vec![name.into()],
                        DiagnosticSeverity::Warning,
                        "structure",
                    ));
                } else if let Some(v) = value {
                    let val_start = offset
                        + hash
                        + 2
                        + eq_pos.unwrap_or(0)
                        + 1
                        + body[eq_pos.unwrap_or(0) + 1..].len()
                        - body[eq_pos.unwrap_or(0) + 1..].trim_start().len();
                    let vr = ByteRange {
                        start: val_start,
                        end: val_start + v.len(),
                    };
                    if name == "required" {
                        result.diagnostics.push(diagnostic(
                            source,
                            "CWT104",
                            "cwt.directiveValueNotAllowed",
                            vr,
                            vec![name.into()],
                            DiagnosticSeverity::Warning,
                            "structure",
                        ));
                    } else if name == "cardinality"
                        && !(v.split_once("..").is_some_and(|(a, b)| {
                            !a.is_empty()
                                && !b.is_empty()
                                && [a, b]
                                    .iter()
                                    .all(|x| *x == "inf" || x.chars().all(|c| c.is_ascii_digit()))
                        }))
                    {
                        result.diagnostics.push(diagnostic(
                            source,
                            "CWT102",
                            "cwt.illegalDirectiveValue",
                            vr,
                            vec![name.into(), v.into()],
                            DiagnosticSeverity::Error,
                            "structure",
                        ));
                    }
                }
            }
        } else if t.starts_with('@') {
            let name = t.split_whitespace().next().unwrap_or(t);
            let start = offset + content.find('@').unwrap_or(0);
            let allowed = ["@include", "@replace", "@hide", "@clear", "@trigger"];
            if !allowed.contains(&name) {
                result.diagnostics.push(diagnostic(
                    source,
                    "CWT101",
                    "directive.unknown",
                    ByteRange {
                        start,
                        end: start + name.len(),
                    },
                    vec![name.into()],
                    DiagnosticSeverity::Warning,
                    "directive",
                ));
            }
            result.model.symbols.push(Symbol {
                name: name.into(),
                kind: SymbolKind::Directive,
                range: range(
                    source,
                    ByteRange {
                        start,
                        end: start + name.len(),
                    },
                ),
                detail: None,
            });
            if t.split_whitespace().count() < 2 {
                result.diagnostics.push(diagnostic(
                    source,
                    "CWT102",
                    "directive.missing_argument",
                    ByteRange {
                        start,
                        end: start + name.len(),
                    },
                    vec![],
                    DiagnosticSeverity::Error,
                    "directive",
                ));
            }
        }
        offset += line.len();
    }
}
fn scan_injects(source: &str, result: &mut AnalysisResult) {
    for line in source.lines() {
        let t = line.trim();
        let value = if t.starts_with("##") {
            t.trim_start_matches('#')
                .trim()
                .strip_prefix("inject")
                .and_then(|rest| rest.trim().strip_prefix('='))
        } else {
            t.strip_prefix("inject")
                .and_then(|rest| rest.trim().strip_prefix('='))
        };
        if let Some(value) = value {
            let path = value
                .trim()
                .trim_matches('"')
                .split_once('@')
                .map_or(value.trim().trim_matches('"'), |(path, _)| path.trim());
            if !path.is_empty() {
                result.model.injects.push(path.into());
            }
        }
    }
}
/// Return deterministic completions for the current prefix/context.
#[must_use]
pub fn completions(source: &str, offset: usize) -> Vec<CompletionArgument> {
    let prefix = &source[..offset.min(source.len())];
    let mut values = if prefix.trim_end().ends_with('@') {
        vec!["@clear", "@hide", "@include", "@replace", "@trigger"]
            .into_iter()
            .map(|x| CompletionArgument {
                label: x.into(),
                detail: Some("directive".into()),
                kind: SymbolKind::Directive,
            })
            .collect()
    } else if prefix.trim_end().ends_with('=') {
        [
            "type",
            "subtype",
            "enum",
            "complex",
            "value",
            "alias",
            "single_alias",
            "scope",
            "scope_group",
            "link",
            "modifier_category",
        ]
        .into_iter()
        .map(|x| CompletionArgument {
            label: x.into(),
            detail: Some("declaration".into()),
            kind: SymbolKind::Field,
        })
        .collect()
    } else {
        Vec::new()
    };
    values.sort_by(|a, b| a.label.cmp(&b.label));
    values
}

#[cfg(test)]
mod tests {
    use super::*;
    const LINKS: &str =
        include_str!("../../../CWToolsTests/testfiles/stellarisconfig/config/links.cwt");
    const SCOPES: &str =
        include_str!("../../../CWToolsTests/testfiles/stellarisconfig/config/scopes.cwt");
    const MODIFIERS: &str = include_str!(
        "../../../CWToolsTests/testfiles/stellarisconfig/config/modifier_categories.cwt"
    );

    #[test]
    fn real_declaration_keys_are_arguments() {
        let r = analyze_document(
            "type[technology] = {
 enum[category] = {
 value[cost] = 1
 }",
        );
        assert!(
            r.model
                .symbols
                .iter()
                .any(|s| s.name == "technology" && s.kind == SymbolKind::Type)
        );
        assert!(
            r.model
                .symbols
                .iter()
                .any(|s| s.name == "category" && s.kind == SymbolKind::Enum)
        );
        assert!(
            r.model
                .symbols
                .iter()
                .any(|s| s.name == "cost" && s.kind == SymbolKind::Value)
        );
    }

    #[test]
    fn declaration_range_is_key_token() {
        let r = analyze_document("type[Country] = { }");
        let s = r
            .model
            .symbols
            .iter()
            .find(|s| s.name == "Country")
            .unwrap();
        assert_eq!(s.range.start.character, 0);
        assert!(s.range.end.character > s.range.start.character);
    }

    #[test]
    fn all_declaration_families_are_supported() {
        let r = analyze_document(
            "subtype[x] = y
complex_enum[x] = y
alias[g:x] = y
single_alias[x] = y
scope_group[x] = y",
        );
        for name in ["x", "g:x"] {
            assert!(r.model.symbols.iter().any(|s| s.name == name));
        }
        assert!(
            r.model
                .symbols
                .iter()
                .any(|s| s.kind == SymbolKind::Complex)
        );
        assert!(r.model.symbols.iter().any(|s| s.kind == SymbolKind::Alias));
        assert!(
            r.model
                .symbols
                .iter()
                .any(|s| s.kind == SymbolKind::SingleAlias)
        );
        assert!(
            r.model
                .symbols
                .iter()
                .any(|s| s.kind == SymbolKind::ScopeGroup)
        );
    }

    #[test]
    fn declarations_are_not_references() {
        let r = analyze_document("enum[x] = { red blue }");
        assert!(r.model.references.is_empty());
    }

    #[test]
    fn nested_value_expressions_are_references() {
        let r = analyze_document(
            "field = { enum[x] complex_enum[y] scope[z] scope_group[g] value_set[v] value[w] alias_name[a] alias_match_left[b] single_alias_right[c] <thing> pre<other>post }",
        );
        for (name, kind) in [
            ("x", SymbolKind::Enum),
            ("y", SymbolKind::Enum),
            ("z", SymbolKind::Scope),
            ("g", SymbolKind::Scope),
            ("v", SymbolKind::Value),
            ("w", SymbolKind::Value),
            ("a", SymbolKind::Alias),
            ("b", SymbolKind::Alias),
            ("c", SymbolKind::SingleAlias),
            ("thing", SymbolKind::Type),
            ("other", SymbolKind::Type),
        ] {
            assert!(
                r.model
                    .references
                    .iter()
                    .any(|x| x.name == name && x.kind == kind),
                "missing {name}"
            );
        }
    }

    #[test]
    fn link_children_use_real_top_block() {
        let r = analyze_document(LINKS);
        assert!(
            r.model
                .symbols
                .iter()
                .any(|s| s.kind == SymbolKind::Link && s.name == "space_owner")
        );
        assert!(
            !r.model
                .symbols
                .iter()
                .any(|s| s.kind == SymbolKind::Link && s.name == "input_scopes")
        );
    }

    #[test]
    fn modifier_children_use_real_top_block() {
        let r = analyze_document(MODIFIERS);
        assert!(
            r.model
                .symbols
                .iter()
                .any(|s| s.kind == SymbolKind::ModifierCategory && s.name == "Pops")
        );
        assert!(
            !r.model
                .symbols
                .iter()
                .any(|s| s.kind == SymbolKind::ModifierCategory && s.name == "supported_scopes")
        );
    }

    #[test]
    fn root_names_keep_blocks_only() {
        let r = analyze_document(SCOPES);
        assert!(!r.model.root_names.contains(&"scopes".to_owned()));
        assert!(
            !r.model
                .root_names
                .iter()
                .any(|x| x == "alias[country]" || x == "single_alias[country]")
        );
    }

    #[test]
    fn completion_arguments_are_sorted_and_deduplicated() {
        let r = analyze_document(
            "enum[z] = { a }
enum[a] = { b }
enum[z] = { c }",
        );
        let labels: Vec<_> = r
            .model
            .completion_arguments
            .iter()
            .map(|x| x.label.as_str())
            .collect();
        assert_eq!(labels, vec!["a", "z"]);
    }

    #[test]
    fn diagnostics_are_preserved() {
        let r = analyze_document("broken = {");
        assert!(r.diagnostics.iter().any(|d| d.code == "CWT001"));
    }

    #[test]
    fn real_fixture_files_parse() {
        for fixture in [LINKS, SCOPES, MODIFIERS] {
            let diagnostics = analyze_document(fixture).diagnostics;
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        }
    }

    #[test]
    fn completion_directives_remain_stable() {
        let labels: Vec<_> = completions("@", 1).into_iter().map(|x| x.label).collect();
        assert_eq!(
            labels,
            vec!["@clear", "@hide", "@include", "@replace", "@trigger"]
        );
    }
}
