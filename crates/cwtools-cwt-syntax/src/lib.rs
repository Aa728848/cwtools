#![forbid(unsafe_code)]

//! Loss-aware CWT syntax parsing built on the shared script grammar.
//!
//! CWT deliberately exposes a separate API so callers can depend on stable
//! CWT diagnostics while sharing tokens, nodes, ranges, comments, and
//! operators with the script parser.

pub use cwtools_script_syntax::{
    ByteRange, Cst, CstNode, MAX_DEPTH, MAX_INPUT_BYTES, Operator, Position, Token, TokenKind,
};
use cwtools_script_syntax::{ScriptEncoding, decode_script_bytes, parse_cwt_compatible};

fn byte_position(bytes: &[u8], offset: usize) -> (usize, usize) {
    let prefix = &bytes[..offset.min(bytes.len())];
    let text = String::from_utf8_lossy(prefix);
    let line = text.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let column = text
        .rsplit_once('\n')
        .map_or(text.as_ref(), |(_, current)| current)
        .encode_utf16()
        .count()
        + 1;
    (line, column)
}

/// The stable diagnostic code emitted for every CWT syntax parse failure.
pub const CWT001: &str = "CWT001";

/// A syntax diagnostic with a UTF-16 LSP column (both line and column are 1-based).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CwtDiagnostic {
    pub code: &'static str,
    pub message: String,
    pub offset: usize,
    pub line: usize,
    pub utf16_column: usize,
}

/// A loss-aware parse result. The underlying CST retains original token text,
/// trivia, comments, operators, and byte ranges even when diagnostics exist.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CwtParse {
    pub cst: Cst,
    pub diagnostics: Vec<CwtDiagnostic>,
}

fn diagnostics(errors: Vec<cwtools_script_syntax::ParseError>) -> Vec<CwtDiagnostic> {
    errors
        .into_iter()
        .map(|error| CwtDiagnostic {
            code: CWT001,
            message: error.message,
            offset: error.offset,
            line: error.line,
            utf16_column: error.utf16_column,
        })
        .collect()
}

/// Parse UTF-8 CWT source, returning one or more stable CWT001 diagnostics.
///
/// # Errors
/// Returns bounded syntax diagnostics when decoding or parsing fails.
pub fn parse_cwt(source: &str) -> Result<Cst, Vec<CwtDiagnostic>> {
    let source = source.strip_prefix('\u{feff}').unwrap_or(source);
    parse_cwt_compatible(source).map_err(diagnostics)
}

/// Parse CWT source while retaining all loss-aware nodes and diagnostics.
#[must_use]
pub fn parse_cwt_loss_aware(source: &str) -> CwtParse {
    match parse_cwt_compatible(source) {
        Ok(cst) => CwtParse {
            cst,
            diagnostics: Vec::new(),
        },
        Err(errors) => CwtParse {
            cst: cwtools_script_syntax::parse_loss_aware(source),
            diagnostics: diagnostics(errors),
        },
    }
}

/// Decode and parse UTF-8 CWT bytes.
///
/// # Errors
/// Returns bounded diagnostics for invalid UTF-8, oversized input, or syntax errors.
pub fn parse_cwt_bytes(bytes: &[u8]) -> Result<Cst, Vec<CwtDiagnostic>> {
    if bytes.len() > MAX_INPUT_BYTES {
        let (line, utf16_column) = byte_position(bytes, MAX_INPUT_BYTES);
        return Err(vec![CwtDiagnostic {
            code: CWT001,
            message: "input exceeds 16 MiB limit".to_owned(),
            offset: MAX_INPUT_BYTES,
            line,
            utf16_column,
        }]);
    }
    let source = decode_script_bytes(bytes, ScriptEncoding::Utf8).map_err(|error| {
        let (line, utf16_column) = byte_position(bytes, error.offset);
        vec![CwtDiagnostic {
            code: CWT001,
            message: error.message.to_owned(),
            offset: error.offset,
            line,
            utf16_column,
        }]
    })?;
    parse_cwt(&source)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnostics_are_stable_and_utf16_aware() {
        let errors = parse_cwt("😀 = {").expect_err("fixture must fail");
        assert_eq!(errors[0].code, CWT001);
        assert_eq!(errors[0].line, 1);
        assert_eq!(errors[0].utf16_column, 6);
    }

    #[test]
    fn loss_aware_parse_retains_original_tokens() {
        let source = "# note\r\na = { b = \"x\\\"y\" }";
        let parsed = parse_cwt_loss_aware(source);
        let reconstructed: String = parsed
            .cst
            .tokens
            .iter()
            .filter(|token| !matches!(token.kind, TokenKind::Eof))
            .map(|token| token.raw.as_str())
            .collect();
        assert_eq!(reconstructed, source);
        assert!(
            parsed
                .cst
                .tokens
                .iter()
                .any(|token| matches!(token.kind, TokenKind::Comment))
        );
        assert!(
            parsed
                .cst
                .tokens
                .iter()
                .any(|token| matches!(token.kind, TokenKind::Operator(Operator::Eq)))
        );
    }
}
