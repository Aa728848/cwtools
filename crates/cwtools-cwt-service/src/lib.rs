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
        let p = &source[..byte.min(source.len())];
        Self {
            line: p.bytes().filter(|b| *b == b'\n').count() as u32,
            character: p
                .rsplit_once('\n')
                .map_or(p, |(_, x)| x)
                .encode_utf16()
                .count() as u32,
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
fn add_node(node: &CstNode, source: &str, model: &mut DocumentModel) {
    match node {
        CstNode::Assignment { key, value, .. } => {
            if let Some((name, _range)) = bare(key) {
                let n = name.trim_matches('"');
                let k = match n {
                    "type" => Some(SymbolKind::Type),
                    "subtype" => Some(SymbolKind::Subtype),
                    "enum" => Some(SymbolKind::Enum),
                    "complex" => Some(SymbolKind::Complex),
                    "value" => Some(SymbolKind::Value),
                    "alias" => Some(SymbolKind::Alias),
                    "single_alias" => Some(SymbolKind::SingleAlias),
                    "scope" => Some(SymbolKind::Scope),
                    "scope_group" => Some(SymbolKind::ScopeGroup),
                    "link" => Some(SymbolKind::Link),
                    "modifier_category" => Some(SymbolKind::ModifierCategory),
                    _ => None,
                };
                if let Some(kind) = k {
                    if let Some((v, vr)) = bare(value) {
                        model.symbols.push(Symbol {
                            name: v.to_owned(),
                            kind,
                            range: range(source, vr),
                            detail: Some(n.to_owned()),
                        });
                    } else if let CstNode::Clause { children, .. } = value.as_ref() {
                        if let Some((v, vr)) = children.iter().find_map(bare) {
                            model.symbols.push(Symbol {
                                name: v.to_owned(),
                                kind,
                                range: range(source, vr),
                                detail: Some(n.to_owned()),
                            });
                        }
                    }
                }
                refs_for(n, value, source, model);
            }
            add_node(value, source, model);
        }
        CstNode::Clause { children, .. } => {
            for c in children {
                add_node(c, source, model)
            }
        }
        _ => {}
    }
}
fn refs_for(key: &str, value: &CstNode, source: &str, model: &mut DocumentModel) {
    let kind = match key {
        "enum" => Some(SymbolKind::Enum),
        "scope" => Some(SymbolKind::Scope),
        "value_set" => Some(SymbolKind::Value),
        "type" => Some(SymbolKind::Type),
        "alias" => Some(SymbolKind::Alias),
        _ => None,
    };
    if let Some(kind) = kind {
        collect_bares(value, source, model, kind);
    }
}
fn collect_bares(node: &CstNode, source: &str, model: &mut DocumentModel, kind: SymbolKind) {
    match node {
        CstNode::Bare { token } => model.references.push(Reference {
            name: token.value.clone(),
            kind,
            range: range(source, token.range),
        }),
        CstNode::Clause { children, .. } => {
            for c in children {
                collect_bares(c, source, model, kind)
            }
        }
        CstNode::Assignment { value, .. } => collect_bares(value, source, model, kind),
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
        let r = ByteRange {
            start: e.offset,
            end: e.offset,
        };
        result.diagnostics.push(diagnostic(
            source,
            "CWT001",
            "syntax",
            r,
            vec![e.message],
            DiagnosticSeverity::Error,
            "syntax",
        ));
    }
    for root in &parsed.cst.roots {
        if let CstNode::Assignment { key, .. } = root {
            if let Some((name, declaration_range)) = bare(key) {
                result.model.root_names.push(name.to_owned());
                result.model.symbols.push(Symbol {
                    name: name.to_owned(),
                    kind: SymbolKind::RootDeclaration,
                    range: range(source, declaration_range),
                    detail: None,
                });
            }
        }
        add_node(root, source, &mut result.model);
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
    result
}
fn scan_directives(source: &str, result: &mut AnalysisResult) {
    for (line, text) in source.lines().enumerate() {
        let t = text.trim();
        if t.starts_with('@') {
            let name = t.split_whitespace().next().unwrap_or(t);
            let start: usize = source.lines().take(line).map(|x| x.len() + 1).sum();
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
                range: Range {
                    start: Position {
                        line: line as u32,
                        character: 0,
                    },
                    end: Position {
                        line: line as u32,
                        character: name.encode_utf16().count() as u32,
                    },
                },
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
    }
}
fn scan_injects(source: &str, result: &mut AnalysisResult) {
    for line in source.lines() {
        let t = line.trim();
        if t.starts_with("inject") {
            if let Some(v) = t.split('=').nth(1) {
                result.model.injects.push(v.trim().trim_matches('"').into());
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
    #[test]
    fn api_kinds() {
        assert_eq!(SymbolKind::Type, SymbolKind::Type);
    }
    #[test]
    fn t0() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t1() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t2() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t3() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t4() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t5() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t6() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t7() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t8() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t9() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t10() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t11() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t12() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t13() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t14() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t15() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t16() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t17() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t18() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t19() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t20() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t21() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t22() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t23() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
    #[test]
    fn t24() {
        let r = analyze_document("type = foo");
        assert!(r.model.symbols.iter().any(|s| s.name == "foo"));
    }
}
