#![forbid(unsafe_code)]

use cwtools_script_syntax::{
    ByteRange, Cst, CstNode, Operator, TokenKind, TypedValue, classify_scalar,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Document {
    pub children: Vec<Item>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    Assignment {
        key: String,
        operator: Operator,
        value: Value,
        range: ByteRange,
    },
    Bare {
        raw: String,
        range: ByteRange,
    },
    Comment {
        raw: String,
        range: ByteRange,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Scalar {
        raw: String,
        quoted: bool,
        typed: TypedValue,
    },
    Clause(Vec<Item>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextEdit {
    pub range: ByteRange,
    pub replacement: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EditError {
    InvalidRange,
    NotOnBoundary,
    Overlap,
}

impl Document {
    #[must_use]
    pub fn from_cst(cst: &Cst) -> Self {
        Self {
            children: convert_items(&cst.roots),
        }
    }

    #[must_use]
    pub fn query_assignments<'a>(&'a self, key: &str) -> Vec<&'a Item> {
        let mut result = Vec::new();
        collect_assignments(&self.children, key, &mut result);
        result
    }
}

fn collect_assignments<'a>(items: &'a [Item], key: &str, result: &mut Vec<&'a Item>) {
    for item in items {
        if let Item::Assignment {
            key: item_key,
            value,
            ..
        } = item
        {
            if item_key == key {
                result.push(item);
            }
            if let Value::Clause(children) = value {
                collect_assignments(children, key, result);
            }
        }
    }
}

fn convert_items(nodes: &[CstNode]) -> Vec<Item> {
    nodes.iter().filter_map(convert_item).collect()
}

fn convert_item(node: &CstNode) -> Option<Item> {
    match node {
        CstNode::Assignment {
            key,
            operator,
            value,
            range,
        } => Some(Item::Assignment {
            key: key_text(key),
            operator: *operator,
            value: convert_value(value),
            range: *range,
        }),
        CstNode::Bare { token } => Some(Item::Bare {
            raw: token.raw.clone(),
            range: token.range,
        }),
        CstNode::Comment { token } => Some(Item::Comment {
            raw: token.raw.clone(),
            range: token.range,
        }),
        CstNode::Clause { .. } | CstNode::Trivia { .. } | CstNode::Error { .. } => None,
    }
}

fn key_text(node: &CstNode) -> String {
    match node {
        CstNode::Bare { token } => token.value.clone(),
        _ => String::new(),
    }
}

fn convert_value(node: &CstNode) -> Value {
    match node {
        CstNode::Clause { children, .. } => Value::Clause(convert_items(children)),
        CstNode::Bare { token } => {
            let quoted = matches!(token.kind, TokenKind::QuotedString);
            Value::Scalar {
                raw: token.raw.clone(),
                quoted,
                typed: classify_scalar(&token.value, quoted),
            }
        }
        _ => Value::Scalar {
            raw: String::new(),
            quoted: false,
            typed: classify_scalar("", false),
        },
    }
}

/// Applies non-overlapping byte-range edits from right to left.
///
/// # Errors
///
/// Returns an error when an edit range is invalid, is not on a UTF-8 boundary,
/// or overlaps another edit.
pub fn apply_edits(source: &str, edits: &[TextEdit]) -> Result<String, EditError> {
    let mut sorted = edits.to_vec();
    for edit in &sorted {
        if edit.range.start > edit.range.end || edit.range.end > source.len() {
            return Err(EditError::InvalidRange);
        }
        if !source.is_char_boundary(edit.range.start) || !source.is_char_boundary(edit.range.end) {
            return Err(EditError::NotOnBoundary);
        }
    }
    sorted.sort_by_key(|edit| edit.range.start);
    for pair in sorted.windows(2) {
        if pair[0].range.end > pair[1].range.start {
            return Err(EditError::Overlap);
        }
    }
    let mut result = source.to_owned();
    for edit in sorted.into_iter().rev() {
        result.replace_range(edit.range.start..edit.range.end, &edit.replacement);
    }
    Ok(result)
}

/// Replaces the value portion of an assignment with a text edit.
///
/// # Errors
///
/// Returns an error when the item is not an assignment, its range is invalid,
/// or its value cannot be located.
pub fn replace_assignment_value(
    source: &str,
    assignment: &Item,
    replacement: String,
) -> Result<TextEdit, EditError> {
    let Item::Assignment {
        operator, range, ..
    } = assignment
    else {
        return Err(EditError::InvalidRange);
    };
    if range.start > range.end
        || range.end > source.len()
        || !source.is_char_boundary(range.start)
        || !source.is_char_boundary(range.end)
    {
        return Err(EditError::InvalidRange);
    }
    let text = &source[range.start..range.end];
    let op = operator.text();
    let op_start = text.find(op).ok_or(EditError::InvalidRange)? + op.len();
    let value_start = op_start + text[op_start..].len() - text[op_start..].trim_start().len();
    let value = text[value_start..].trim_end();
    if value.is_empty() {
        return Err(EditError::InvalidRange);
    }
    let start = range.start + value_start;
    Ok(TextEdit {
        range: ByteRange {
            start,
            end: start + value.len(),
        },
        replacement,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use cwtools_script_syntax::parse;

    #[test]
    fn preserves_shape_order_comments_and_duplicates() {
        let cst = parse("# one\na=1\na=2\nb={\n # inner\nc=\"3\"\n}").unwrap();
        let doc = Document::from_cst(&cst);
        assert_eq!(doc.query_assignments("a").len(), 2);
        assert!(matches!(doc.children[0], Item::Comment { .. }));
        assert!(matches!(
            doc.children[3],
            Item::Assignment {
                value: Value::Clause(_),
                ..
            }
        ));
    }

    #[test]
    fn typed_quoted_distinction_and_edits() {
        let src = "a=1\nb=\"1\"\n";
        let doc = Document::from_cst(&parse(src).unwrap());
        let a = doc.query_assignments("a")[0];
        let b = doc.query_assignments("b")[0];
        assert!(matches!(
            a,
            Item::Assignment {
                value: Value::Scalar { quoted: false, .. },
                ..
            }
        ));
        assert!(matches!(
            b,
            Item::Assignment {
                value: Value::Scalar { quoted: true, .. },
                ..
            }
        ));
        let edit = replace_assignment_value(src, a, "2".into()).unwrap();
        let updated = apply_edits(src, &[edit]).unwrap();
        assert!(parse(&updated).is_ok());
    }

    #[test]
    fn rejects_bad_edits_and_applies_reverse_order() {
        let source = "abcd";
        assert_eq!(
            apply_edits(
                source,
                &[
                    TextEdit {
                        range: ByteRange { start: 1, end: 3 },
                        replacement: "x".into()
                    },
                    TextEdit {
                        range: ByteRange { start: 2, end: 4 },
                        replacement: "y".into()
                    }
                ]
            ),
            Err(EditError::Overlap)
        );
        assert_eq!(
            apply_edits(
                "éx",
                &[TextEdit {
                    range: ByteRange { start: 1, end: 1 },
                    replacement: "z".into()
                }]
            ),
            Err(EditError::NotOnBoundary)
        );
        assert_eq!(
            apply_edits(
                source,
                &[
                    TextEdit {
                        range: ByteRange { start: 0, end: 1 },
                        replacement: "A".into()
                    },
                    TextEdit {
                        range: ByteRange { start: 3, end: 4 },
                        replacement: "D".into()
                    }
                ]
            ),
            Ok("AbcD".into())
        );
    }
}
