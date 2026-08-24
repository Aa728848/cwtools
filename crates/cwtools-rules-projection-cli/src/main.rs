#![forbid(unsafe_code)]

use cwtools_rule_ir::parse_document;
use cwtools_rules_engine::{RuleCatalog, ScopeUniverse, diagnostic_message_key};
use cwtools_source::LineIndex;
use serde::{Deserialize, Serialize};
use std::io::{self, Read};

const MAX_INPUT: usize = 16 * 1024 * 1024;
const MAX_DOCUMENTS: usize = 2_000;

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Input {
    rules: Vec<RuleDocument>,
    root: String,
    source: String,
    #[serde(rename = "initialScope")]
    initial_scope: Option<String>,
    scopes: Option<Vec<String>>,
    mode: Mode,
    prefix: Option<String>,
    field: Option<String>,
    cursor: Option<usize>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RuleDocument {
    path: String,
    text: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
enum Mode {
    Validation,
    Completion,
    Info,
}

#[derive(Debug, Serialize, PartialEq, Eq)]
#[serde(untagged)]
enum Output {
    Validation { diagnostics: Vec<WireDiagnostic> },
    Completion { items: Vec<String> },
    Info { info: Option<String> },
    Error { error: WireError },
}

#[derive(Debug, Serialize, PartialEq, Eq)]
struct WireDiagnostic {
    code: String,
    #[serde(rename = "messageKey")]
    message_key: String,
    key: String,
    args: Vec<String>,
    start: usize,
    end: usize,
    #[serde(rename = "startLine")]
    start_line: u32,
    #[serde(rename = "startColumn")]
    start_column: u32,
    #[serde(rename = "endLine")]
    end_line: u32,
    #[serde(rename = "endColumn")]
    end_column: u32,
}

#[derive(Debug, Serialize, PartialEq, Eq)]
struct WireError {
    kind: String,
    message: String,
}

fn error(kind: &str, message: impl Into<String>) -> Output {
    Output::Error {
        error: WireError {
            kind: kind.into(),
            message: message.into(),
        },
    }
}

fn execute(input: Input) -> Output {
    if input.rules.len() > MAX_DOCUMENTS {
        return error(
            "input",
            format!("too many rule documents: maximum is {MAX_DOCUMENTS}"),
        );
    }
    let documents = input
        .rules
        .iter()
        .map(|rule| parse_document(&rule.path, &rule.text))
        .collect::<Result<Vec<_>, _>>();
    let documents = match documents {
        Ok(value) => value,
        Err(messages) => return error("parse", messages.join("; ")),
    };
    let scopes = ScopeUniverse::new(input.scopes.unwrap_or_default());
    let catalog = match RuleCatalog::compile(&documents, scopes) {
        Ok(value) => value,
        Err(value) => return error("compile", format!("{value:?}")),
    };
    match input.mode {
        Mode::Validation => {
            let result = catalog.validate_source_with_scope(
                &input.root,
                &input.source,
                input.initial_scope.as_deref(),
            );
            let line_index = LineIndex::new(&input.source);
            let diagnostics = result
                .diagnostics
                .into_iter()
                .map(|d| {
                    let start = line_index
                        .position(&input.source, d.range.start)
                        .ok_or_else(|| {
                            format!("invalid diagnostic start byte boundary: {}", d.range.start)
                        })?;
                    let end = line_index
                        .position(&input.source, d.range.end)
                        .ok_or_else(|| {
                            format!("invalid diagnostic end byte boundary: {}", d.range.end)
                        })?;
                    Ok(WireDiagnostic {
                        message_key: diagnostic_message_key(&d.code).to_owned(),
                        code: d.code,
                        key: d.key,
                        args: d.args,
                        start: d.range.start,
                        end: d.range.end,
                        start_line: start.line,
                        start_column: start.character,
                        end_line: end.line,
                        end_column: end.character,
                    })
                })
                .collect::<Result<Vec<_>, String>>();
            let mut diagnostics = match diagnostics {
                Ok(value) => value,
                Err(message) => return error("diagnostic", message),
            };
            diagnostics.sort_by(|a, b| {
                (a.start, a.end, &a.code, &a.key, &a.args)
                    .cmp(&(b.start, b.end, &b.code, &b.key, &b.args))
            });
            Output::Validation { diagnostics }
        }
        Mode::Completion => {
            let prefix = input.prefix.as_deref().unwrap_or("");
            let items = if let Some(cursor) = input.cursor {
                match catalog.completion_at(&input.root, &input.source, cursor, prefix) {
                    Ok(items) => items,
                    Err(value) => return error("query", format!("{value:?}")),
                }
            } else {
                catalog.completion(&input.root, prefix)
            };
            Output::Completion { items }
        }
        Mode::Info => {
            let field = input.field.as_deref().unwrap_or("");
            let info = if let Some(cursor) = input.cursor {
                match catalog.info_at(&input.root, &input.source, cursor, field) {
                    Ok(info) => info,
                    Err(value) => return error("query", format!("{value:?}")),
                }
            } else {
                catalog.info(&input.root, field)
            };
            Output::Info { info }
        }
    }
}

fn main() {
    let mut input = Vec::new();
    let limited = io::stdin()
        .take((MAX_INPUT + 1) as u64)
        .read_to_end(&mut input);
    let result = match limited {
        Err(value) => error("input", value.to_string()),
        Ok(size) if size > MAX_INPUT => error("input", "input exceeds 16MiB"),
        Ok(_) => match serde_json::from_slice::<Input>(&input) {
            Ok(value) => execute(value),
            Err(value) => error("input", value.to_string()),
        },
    };
    println!(
        "{}",
        serde_json::to_string(&result).unwrap_or_else(|_| String::from(
            r#"{"error":{"kind":"output","message":"serialization failed"}}"#
        ))
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    fn input(text: &str, mode: Mode) -> Input {
        Input {
            rules: vec![RuleDocument {
                path: "rules.cwt".into(),
                text: "root = { ## cardinality = 0..1\nknown = scalar\n## cardinality = 0..1\nvalue = scalar }".into(),
            }],
            root: "root".into(),
            source: text.into(),
            initial_scope: None,
            scopes: None,
            mode,
            prefix: None,
            field: None,
            cursor: None,
        }
    }
    #[test]
    fn validation_shape() {
        assert!(matches!(
            execute(input("known = x", Mode::Validation)),
            Output::Validation { .. }
        ));
    }
    #[test]
    fn validation_clean() {
        if let Output::Validation { diagnostics } = execute(input("known = x", Mode::Validation)) {
            assert!(diagnostics.is_empty());
        }
    }
    #[test]
    fn validation_unknown() {
        if let Output::Validation { diagnostics } = execute(input("unknown = x", Mode::Validation))
        {
            assert_eq!(diagnostics[0].message_key, "rules.unknown_field");
            let json = serde_json::to_value(&diagnostics[0]).unwrap();
            assert_eq!(json["messageKey"], "rules.unknown_field");
        }
    }
    #[test]
    fn completion_shape() {
        assert!(matches!(
            execute(input("", Mode::Completion)),
            Output::Completion { .. }
        ));
    }
    #[test]
    fn completion_prefix() {
        let mut x = input("", Mode::Completion);
        x.prefix = Some("k".into());
        if let Output::Completion { items } = execute(x) {
            assert_eq!(items, vec!["known"]);
        }
    }
    #[test]
    fn info_missing() {
        if let Output::Info { info } = execute(input("", Mode::Info)) {
            assert!(info.is_none());
        }
    }
    #[test]
    fn parse_error() {
        let mut x = input("", Mode::Info);
        x.rules[0].text = "root = {".into();
        assert!(
            matches!(execute(x), Output::Error { error: WireError { kind, .. } } if kind == "parse")
        );
    }
    #[test]
    fn duplicate_compile_error() {
        let mut x = input("", Mode::Info);
        x.rules.push(x.rules[0].clone());
        assert!(
            matches!(execute(x), Output::Error { error: WireError { kind, .. } } if kind == "compile")
        );
    }
    #[test]
    fn document_bound() {
        let mut x = input("", Mode::Info);
        x.rules = (0..=MAX_DOCUMENTS)
            .map(|_| RuleDocument {
                path: "x".into(),
                text: "root = scalar".into(),
            })
            .collect();
        assert!(matches!(execute(x), Output::Error { .. }));
    }
    #[test]
    fn strict_json() {
        assert!(
            serde_json::from_str::<Input>(
                r#"{"rules":[],"root":"r","source":"","mode":"info","extra":1}"#
            )
            .is_err()
        );
    }
    #[test]
    fn mode_validation_deserializes() {
        assert_eq!(
            serde_json::from_str::<Mode>(r#""validation""#).unwrap(),
            Mode::Validation
        );
    }
    #[test]
    fn mode_completion_deserializes() {
        assert_eq!(
            serde_json::from_str::<Mode>(r#""completion""#).unwrap(),
            Mode::Completion
        );
    }
    #[test]
    fn mode_info_deserializes() {
        assert_eq!(
            serde_json::from_str::<Mode>(r#""info""#).unwrap(),
            Mode::Info
        );
    }
    #[test]
    fn initial_scope_is_accepted() {
        let mut x = input("", Mode::Validation);
        x.initial_scope = Some("country".into());
        assert!(matches!(execute(x), Output::Validation { .. }));
    }
    #[test]
    fn scopes_are_accepted() {
        let mut x = input("", Mode::Validation);
        x.scopes = Some(vec!["country".into()]);
        assert!(matches!(execute(x), Output::Validation { .. }));
    }
    #[test]
    fn info_field_is_accepted() {
        let mut x = input("", Mode::Info);
        x.field = Some("known".into());
        assert!(matches!(execute(x), Output::Info { .. }));
    }
    #[test]
    fn completion_is_sorted() {
        let x = input("", Mode::Completion);
        if let Output::Completion { items } = execute(x) {
            assert!(items.windows(2).all(|w| w[0] <= w[1]));
        }
    }
    #[test]
    fn error_is_json() {
        let out = serde_json::to_string(&error("input", "bad")).unwrap();
        assert!(out.contains("error"));
    }

    #[test]
    fn ascii_position() {
        assert_eq!(
            LineIndex::new("abc").position("abc", 1).unwrap().character,
            1
        );
    }
    #[test]
    fn multiline_position() {
        let source = "a\nb";
        assert_eq!(LineIndex::new(source).position(source, 2).unwrap().line, 1);
    }
    #[test]
    fn crlf_position() {
        let source = "a\r\nb";
        assert_eq!(LineIndex::new(source).position(source, 3).unwrap().line, 1);
    }
    #[test]
    fn emoji_before_range() {
        assert_eq!(
            LineIndex::new("😀x").position("😀x", 4).unwrap().character,
            2
        );
    }
    #[test]
    fn emoji_value_position() {
        assert_eq!(
            LineIndex::new("v=😀")
                .position("v=😀", 6)
                .unwrap()
                .character,
            4
        );
    }
    #[test]
    fn range_at_eof() {
        assert_eq!(
            LineIndex::new("abc").position("abc", 3).unwrap().character,
            3
        );
    }
    #[test]
    fn unknown_position() {
        assert_eq!(
            LineIndex::new("unknown")
                .position("unknown", 7)
                .unwrap()
                .character,
            7
        );
    }
    #[test]
    fn cardinality_position() {
        let source = "x\ny";
        assert_eq!(LineIndex::new(source).position(source, 2).unwrap().line, 1);
    }
    #[test]
    fn value_position() {
        assert_eq!(
            LineIndex::new("value")
                .position("value", 5)
                .unwrap()
                .character,
            5
        );
    }
    #[test]
    fn invalid_boundary_position() {
        assert!(LineIndex::new("😀").position("😀", 1).is_none());
    }
    #[test]
    fn contextual_completion_cursor_is_used() {
        let mut x = input("known = x", Mode::Completion);
        x.cursor = Some(9);
        if let Output::Completion { items } = execute(x) {
            assert!(!items.contains(&"known".to_owned()));
            assert!(items.contains(&"value".to_owned()));
        } else {
            panic!("expected completion");
        }
    }
    #[test]
    fn invalid_contextual_cursor_is_query_error() {
        let mut x = input("雪", Mode::Completion);
        x.cursor = Some(1);
        assert!(
            matches!(execute(x), Output::Error { error: WireError { kind, .. } } if kind == "query")
        );
    }
}
