#![forbid(unsafe_code)]
#![allow(
    clippy::elidable_lifetime_names,
    clippy::items_after_statements,
    clippy::manual_let_else,
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::must_use_candidate,
    clippy::only_used_in_recursion,
    clippy::semicolon_if_nothing_returned,
    clippy::too_many_lines,
    clippy::unnecessary_semicolon
)]

use std::fmt;

pub const MAX_INPUT_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_DEPTH: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteRange {
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Position {
    pub offset: usize,
    pub line: usize,
    pub utf16_column: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub offset: usize,
    pub line: usize,
    pub utf16_column: usize,
}
impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} at {}:{}:{}",
            self.message, self.line, self.utf16_column, self.offset
        )
    }
}
impl std::error::Error for ParseError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operator {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    EqEq,
    QuestionEq,
    QuestionSpaceEq,
}
impl Operator {
    pub fn text(self) -> &'static str {
        match self {
            Self::Eq => "=",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Le => "<=",
            Self::Ge => ">=",
            Self::EqEq => "==",
            Self::QuestionEq => "?=",
            Self::QuestionSpaceEq => "? =",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Whitespace,
    Comment,
    Identifier,
    QuotedString,
    LBrace,
    RBrace,
    Operator(Operator),
    Unknown,
    Eof,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub range: ByteRange,
    pub raw: String,
    pub value: String,
    pub position: Position,
}
impl Token {
    pub fn is_trivia(&self) -> bool {
        matches!(self.kind, TokenKind::Whitespace)
    }
}

fn position(src: &str, offset: usize) -> Position {
    let mut line = 1;
    let mut start = 0;
    for (i, b) in src.bytes().enumerate() {
        if i >= offset {
            break;
        }
        if b == b'\n' {
            line += 1;
            start = i + 1;
        }
    }
    let col = src.get(start..offset).unwrap_or("").encode_utf16().count() + 1;
    Position {
        offset,
        line,
        utf16_column: col,
    }
}
fn error(src: &str, msg: &str, at: usize) -> ParseError {
    let p = position(src, at);
    ParseError {
        message: msg.into(),
        offset: at,
        line: p.line,
        utf16_column: p.utf16_column,
    }
}

pub fn lex(src: &str) -> Result<Vec<Token>, ParseError> {
    if src.len() > MAX_INPUT_BYTES {
        return Err(error(src, "input exceeds 16 MiB limit", MAX_INPUT_BYTES));
    }
    let bytes = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    const OPS: [(&str, Operator); 9] = [
        ("!=", Operator::Ne),
        ("<=", Operator::Le),
        (">=", Operator::Ge),
        ("==", Operator::EqEq),
        ("? =", Operator::QuestionSpaceEq),
        ("?=", Operator::QuestionEq),
        ("=", Operator::Eq),
        ("<", Operator::Lt),
        (">", Operator::Gt),
    ];
    while i < bytes.len() {
        let s = i;
        if bytes[i].is_ascii_whitespace() {
            i += 1;
            while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                i += 1
            }
            out.push(tok(src, TokenKind::Whitespace, s, i, src[s..i].to_string()));
            continue;
        }
        if bytes[i] == b'#' {
            i += 1;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1
            }
            out.push(tok(src, TokenKind::Comment, s, i, src[s..i].to_string()));
            continue;
        }
        if bytes[i] == b'"' {
            i += 1;
            let mut val = String::new();
            let mut closed = false;
            while i < bytes.len() {
                if bytes[i] == b'\\' {
                    i += 1;
                    if i >= bytes.len() {
                        break;
                    };
                    let c = bytes[i];
                    val.push(match c {
                        b'"' => '"',
                        b'\\' => '\\',
                        _ => return Err(error(src, "unsupported quoted escape", i - 1)),
                    });
                    i += 1;
                } else if bytes[i] == b'"' {
                    i += 1;
                    closed = true;
                    break;
                } else {
                    let ch = src[i..].chars().next().unwrap();
                    val.push(ch);
                    i += ch.len_utf8();
                }
            }
            if !closed {
                return Err(error(src, "unclosed quote", s));
            };
            out.push(tok(src, TokenKind::QuotedString, s, i, val));
            continue;
        }
        if bytes[i] == b'{' {
            i += 1;
            out.push(tok(src, TokenKind::LBrace, s, i, "{".into()));
            continue;
        }
        if bytes[i] == b'}' {
            i += 1;
            out.push(tok(src, TokenKind::RBrace, s, i, "}".into()));
            continue;
        }
        let mut found = None;
        for (op, k) in OPS {
            if src[i..].starts_with(op) {
                found = Some((op, k));
                break;
            }
        }
        if let Some((op, k)) = found {
            i += op.len();
            out.push(tok(src, TokenKind::Operator(k), s, i, op.into()));
            continue;
        }
        while i < bytes.len()
            && !bytes[i].is_ascii_whitespace()
            && !b"{}#\"<>!=+-".contains(&bytes[i])
        {
            i += 1;
        }
        if i == s {
            i += 1;
            out.push(tok(src, TokenKind::Unknown, s, i, src[s..i].into()));
        } else {
            let raw = src[s..i].to_string();
            out.push(tok(src, TokenKind::Identifier, s, i, raw));
        }
    }
    out.push(tok(
        src,
        TokenKind::Eof,
        src.len(),
        src.len(),
        String::new(),
    ));
    Ok(out)
}
fn tok(src: &str, kind: TokenKind, s: usize, e: usize, value: String) -> Token {
    Token {
        kind,
        range: ByteRange { start: s, end: e },
        raw: src[s..e].into(),
        value,
        position: position(src, s),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CstNode {
    Assignment {
        key: Box<CstNode>,
        operator: Operator,
        value: Box<CstNode>,
        range: ByteRange,
    },
    Bare {
        token: Token,
    },
    Clause {
        open: Token,
        children: Vec<CstNode>,
        close: Option<Token>,
        range: ByteRange,
    },
    Comment {
        token: Token,
    },
    Trivia {
        token: Token,
    },
    Error {
        token: Token,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cst {
    pub roots: Vec<CstNode>,
    pub tokens: Vec<Token>,
    pub errors: Vec<ParseError>,
    source: String,
}
impl Cst {
    pub fn normalized(&self) -> String {
        let mut s = String::new();
        print_nodes(&self.roots, 0, &mut s);
        s
    }
    pub fn print_normalized(&self) -> String {
        self.normalized()
    }
}

pub fn parse(src: &str) -> Result<Cst, Vec<ParseError>> {
    let tokens = match lex(src) {
        Ok(t) => t,
        Err(e) => return Err(vec![e]),
    };
    let mut p = Parser {
        src,
        tokens: tokens.clone(),
        at: 0,
        errors: Vec::new(),
        depth: 0,
    };
    let roots = p.nodes(false);
    let c = Cst {
        roots,
        tokens,
        errors: p.errors,
        source: src.into(),
    };
    if c.errors.is_empty() {
        Ok(c)
    } else {
        Err(c.errors)
    }
}
pub fn parse_loss_aware(src: &str) -> Cst {
    let tokens = match lex(src) {
        Ok(t) => t,
        Err(e) => {
            return Cst {
                roots: vec![],
                tokens: vec![],
                errors: vec![e],
                source: src.into(),
            };
        }
    };
    let mut p = Parser {
        src,
        tokens: tokens.clone(),
        at: 0,
        errors: Vec::new(),
        depth: 0,
    };
    let roots = p.nodes(false);
    Cst {
        roots,
        tokens,
        errors: p.errors,
        source: src.into(),
    }
}
struct Parser<'a> {
    src: &'a str,
    tokens: Vec<Token>,
    at: usize,
    errors: Vec<ParseError>,
    depth: usize,
}
impl<'a> Parser<'a> {
    fn skip(&mut self) {
        while self.at + 1 < self.tokens.len() && self.tokens[self.at].is_trivia() {
            self.at += 1
        }
    }
    fn peek(&mut self) -> &Token {
        self.skip();
        &self.tokens[self.at]
    }
    fn take(&mut self) -> Token {
        self.skip();
        let t = self.tokens[self.at].clone();
        if self.at + 1 < self.tokens.len() {
            self.at += 1;
        }
        t
    }
    fn nodes(&mut self, in_clause: bool) -> Vec<CstNode> {
        let mut v = Vec::new();
        loop {
            self.skip();
            let k = self.tokens[self.at].kind.clone();
            if matches!(k, TokenKind::Eof) {
                if in_clause {
                    self.errors
                        .push(error(self.src, "unclosed clause", self.src.len()));
                }
                break;
            }
            if matches!(k, TokenKind::RBrace) {
                if in_clause {
                    break;
                }
                let t = self.take();
                self.errors
                    .push(error(self.src, "unexpected token '}'", t.range.start));
                v.push(CstNode::Error { token: t });
                continue;
            }
            if matches!(k, TokenKind::Comment) {
                v.push(CstNode::Comment { token: self.take() });
                continue;
            }
            if matches!(k, TokenKind::Unknown) {
                let t = self.take();
                self.errors
                    .push(error(self.src, "unexpected token", t.range.start));
                v.push(CstNode::Error { token: t });
                continue;
            }
            let key = self.take();
            let key_start = key.range.start;
            if matches!(self.peek().kind, TokenKind::Operator(_)) {
                let op = match self.take().kind {
                    TokenKind::Operator(x) => x,
                    _ => unreachable!(),
                };
                if matches!(self.peek().kind, TokenKind::LBrace) {
                    let open = self.take();
                    if self.depth >= MAX_DEPTH {
                        self.errors.push(error(
                            self.src,
                            "maximum nesting depth exceeded",
                            open.range.start,
                        ));
                    }
                    self.depth += 1;
                    let children = self.nodes(true);
                    self.depth -= 1;
                    let close = if matches!(self.peek().kind, TokenKind::RBrace) {
                        Some(self.take())
                    } else {
                        None
                    };
                    let end = close.as_ref().map_or(open.range.end, |x| x.range.end);
                    if close.is_none() {
                        self.errors
                            .push(error(self.src, "unclosed clause", open.range.start));
                    }
                    v.push(CstNode::Assignment {
                        key: Box::new(CstNode::Bare { token: key }),
                        operator: op,
                        value: Box::new(CstNode::Clause {
                            open,
                            children,
                            close,
                            range: ByteRange {
                                start: key_start,
                                end,
                            },
                        }),
                        range: ByteRange {
                            start: key_start,
                            end,
                        },
                    });
                } else {
                    let val = self.take();
                    let end = val.range.end;
                    v.push(CstNode::Assignment {
                        key: Box::new(CstNode::Bare { token: key }),
                        operator: op,
                        value: Box::new(CstNode::Bare { token: val }),
                        range: ByteRange {
                            start: key_start,
                            end,
                        },
                    })
                }
            } else {
                v.push(CstNode::Bare { token: key });
            }
        }
        v
    }
}
fn print_nodes(ns: &[CstNode], depth: usize, out: &mut String) {
    for n in ns {
        match n {
            CstNode::Comment { token } | CstNode::Trivia { token } => {
                out.push_str(token.raw.trim_end());
                out.push('\n')
            }
            CstNode::Bare { token } => {
                if matches!(token.kind, TokenKind::QuotedString) {
                    out.push('\"');
                    for value in token.value.chars() {
                        if matches!(value as u32, 34 | 92) {
                            out.push(char::from(92));
                        }
                        out.push(value);
                    }
                    out.push('\"');
                } else {
                    out.push_str(&token.value);
                }
                out.push(' ');
            }
            CstNode::Error { token } => {
                out.push_str(&token.raw);
                out.push(' ')
            }
            CstNode::Assignment {
                key,
                operator,
                value,
                ..
            } => {
                print_nodes(std::slice::from_ref(key), depth, out);
                out.push_str(operator.text());
                out.push(' ');
                print_nodes(std::slice::from_ref(value), depth, out);
                out.push('\n')
            }
            CstNode::Clause { children, .. } => {
                out.push_str("{\n");
                print_nodes(children, depth + 1, out);
                out.push_str("} ")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn operators() {
        let t = lex("a=b c!=d e<=f g>=h i==j k?=l m? =n o<p q>r").unwrap();
        assert_eq!(
            t.iter()
                .filter(|x| matches!(x.kind, TokenKind::Operator(_)))
                .count(),
            9
        )
    }
    #[test]
    fn unicode() {
        let t = lex("😀 = \"é\"").unwrap();
        assert_eq!(t[0].position.utf16_column, 1);
        assert_eq!(t[1].position.utf16_column, 3)
    }
    #[test]
    fn nested() {
        let c = parse("a={ b=1 c={d=2}} x=3").unwrap();
        assert!(c.normalized().contains("x ="))
    }
    #[test]
    fn escaped() {
        assert_eq!(lex("a=\"x\\\"y\"").unwrap()[2].value, "x\"y")
    }
    #[test]
    fn errors() {
        assert!(parse("a=\"x").is_err());
        assert!(parse("a={b=1").is_err())
    }
    #[test]
    fn comments_are_ordered_cst_nodes() {
        let parsed = parse("# first\na = 1\n# second\nb = 2").unwrap();
        assert!(matches!(parsed.roots[0], CstNode::Comment { .. }));
        assert!(matches!(parsed.roots[2], CstNode::Comment { .. }));
    }

    #[test]
    fn multi_root_bare_values_and_int64_are_preserved() {
        let parsed = parse("valuea valueb @large = 80000000000000").unwrap();
        assert_eq!(parsed.roots.len(), 3);
        assert_eq!(
            parsed
                .tokens
                .iter()
                .find(|token| token.value == "80000000000000")
                .unwrap()
                .value,
            "80000000000000"
        );
    }

    #[test]
    fn loss_aware_tokens_cover_original_input() {
        let source = "a = { # x\r\n b = \"c\\\"d\" }";
        let parsed = parse(source).unwrap();
        let reconstructed: String = parsed
            .tokens
            .iter()
            .filter(|token| !matches!(token.kind, TokenKind::Eof))
            .map(|token| token.raw.as_str())
            .collect();
        assert_eq!(reconstructed, source);
    }

    #[test]
    fn deterministic_fuzz_never_panics_or_exceeds_input_bound() {
        let alphabet = ["a", "=", "{", "}", "#x\n", "\"q\"", "😀", "?="];
        let mut seed = 0x005E_ED12_u64;
        for _ in 0..10_000 {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let mut source = String::new();
            for shift in 0..8 {
                let index =
                    usize::try_from((seed >> shift) % u64::try_from(alphabet.len()).unwrap())
                        .unwrap();
                source.push_str(alphabet[index]);
            }
            let parsed = parse_loss_aware(&source);
            assert!(parsed.tokens.len() <= source.len() + 1);
            for token in &parsed.tokens {
                assert!(token.range.start <= token.range.end && token.range.end <= source.len());
            }
        }
    }

    #[test]
    fn stable() {
        let s = "a={b=1} c=\"x\"";
        let a = parse(s).unwrap().normalized();
        assert_eq!(parse(&a).unwrap().normalized(), a)
    }
}
