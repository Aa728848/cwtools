use cwtools_script_syntax::{
    CstNode, TokenKind, TypedValue, classify_scalar, parse, print_canonical,
};
use serde_json::{Value, json};
use std::io::{self, Read};
use std::process::ExitCode;

fn scalar(token: &cwtools_script_syntax::Token) -> Value {
    let quoted = matches!(token.kind, TokenKind::QuotedString);
    let (kind, raw) = match classify_scalar(&token.value, quoted) {
        TypedValue::QuotedString(value) => ("quotedString", value),
        TypedValue::Integer(value) => ("int", value.to_string()),
        TypedValue::Decimal(value) => ("float", value),
        TypedValue::Boolean(value) => (
            "bool",
            if value {
                "yes".to_owned()
            } else {
                "no".to_owned()
            },
        ),
        TypedValue::String(value) => ("identifier", value),
        TypedValue::Rgb(_) | TypedValue::Hsv { .. } => ("identifier", token.value.clone()),
    };
    json!({ "kind": kind, "raw": raw, "children": [] })
}

fn node(value: &CstNode) -> Value {
    match value {
        CstNode::Assignment {
            key,
            operator,
            value,
            ..
        } => {
            json!({ "kind": "assignment", "key": key_value(key), "operator": operator.text(), "value": value_projection(value) })
        }
        CstNode::Bare { token } => json!({ "kind": "bare", "value": scalar(token) }),
        CstNode::Comment { token } => {
            json!({ "kind": "comment", "raw": token.raw.trim_start_matches('#') })
        }
        CstNode::Clause { children, .. } => {
            json!({ "kind": "bare", "value": { "kind": "clause", "raw": "", "children": children.iter().map(node).collect::<Vec<_>>() } })
        }
        CstNode::Trivia { token } | CstNode::Error { token } => {
            json!({ "kind": "unknown", "raw": token.raw })
        }
        CstNode::ColourLiteral { typed, .. } => {
            json!({ "kind": "bare", "value": typed_projection(typed.as_ref()) })
        }
    }
}

fn key_value(value: &CstNode) -> String {
    match value {
        CstNode::Bare { token } => token.value.clone(),
        _ => String::new(),
    }
}
fn typed_projection(value: &TypedValue) -> Value {
    match value {
        TypedValue::Rgb(values) => {
            json!({ "kind": "clause", "raw": "", "children": values.iter().map(|value| json!({ "kind": "bare", "value": { "kind": "int", "raw": value.to_string(), "children": [] } })).collect::<Vec<_>>() })
        }
        TypedValue::Hsv { components, .. } => {
            json!({ "kind": "clause", "raw": "", "children": components.iter().map(|value| json!({ "kind": "bare", "value": { "kind": "float", "raw": value, "children": [] } })).collect::<Vec<_>>() })
        }
        _ => json!({ "kind": "unknown", "raw": "", "children": [] }),
    }
}

fn value_projection(value: &CstNode) -> Value {
    match value {
        CstNode::Bare { token } => scalar(token),
        CstNode::Clause { children, .. } => {
            json!({ "kind": "clause", "raw": "", "children": children.iter().map(node).collect::<Vec<_>>() })
        }
        CstNode::ColourLiteral { typed, .. } => typed_projection(typed.as_ref()),
        other => node(other),
    }
}

fn main() -> ExitCode {
    let mut source = String::new();
    if let Err(error) = io::stdin().read_to_string(&mut source) {
        eprintln!("{error}");
        return ExitCode::FAILURE;
    }
    let output = match parse(&source) {
        Ok(cst) => {
            json!({ "schemaVersion": "cwtools.structural-projection/v1", "parser": "rust", "sourceName": "stdin", "ok": true, "errors": [], "nodes": cst.roots.iter().map(node).collect::<Vec<_>>(), "canonical": print_canonical(&cst) })
        }
        Err(errors) => {
            json!({ "schemaVersion": "cwtools.structural-projection/v1", "parser": "rust", "sourceName": "stdin", "ok": false, "errors": errors.iter().map(|error| json!({ "code": error.code, "message": error.message, "line": error.line, "utf16Column": error.utf16_column })).collect::<Vec<_>>(), "nodes": [], "canonical": Value::Null })
        }
    };
    println!("{output}");
    ExitCode::SUCCESS
}
