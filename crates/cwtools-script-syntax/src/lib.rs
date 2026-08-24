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
    pub code: &'static str,
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
    let code = match msg {
        "unclosed quote" => "SYNTAX_UNCLOSED_QUOTE",
        "unclosed clause" => "SYNTAX_UNCLOSED_CLAUSE",
        "unexpected token '}'" => "SYNTAX_UNEXPECTED_RBRACE",
        "MissingValue" => "SYNTAX_MISSING_VALUE",
        "invalid colour literal" => "SYNTAX_INVALID_COLOUR_LITERAL",
        "invalid colour components" => "SYNTAX_INVALID_COLOUR_COMPONENTS",
        "maximum nesting depth exceeded" => "SYNTAX_DEPTH_LIMIT",
        "input exceeds 16 MiB limit" => "SYNTAX_INPUT_LIMIT",
        _ => "SYNTAX_UNEXPECTED_TOKEN",
    };
    ParseError {
        code,
        message: msg.into(),
        offset: at,
        line: p.line,
        utf16_column: p.utf16_column,
    }
}

pub fn lex(src: &str) -> Result<Vec<Token>, ParseError> {
    lex_with_mode(src, false)
}

/// Lex CWT syntax, where an unbroken `<...>` segment is part of an identifier.
pub fn lex_cwt(src: &str) -> Result<Vec<Token>, ParseError> {
    lex_with_mode(src, true)
}

fn lex_with_mode(src: &str, cwt_mode: bool) -> Result<Vec<Token>, ParseError> {
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
            let end = if i > s && bytes[i.saturating_sub(1)] == b'\r' {
                i - 1
            } else {
                i
            };
            out.push(tok(
                src,
                TokenKind::Comment,
                s,
                end,
                src[s..end].to_string(),
            ));
            i = end;
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
        // A sign belongs to a numeric literal when it is immediately followed by a digit
        // (or a decimal point and a digit).  It must not become an Unknown token.
        if matches!(bytes[i], b'+' | b'-')
            && i + 1 < bytes.len()
            && (bytes[i + 1].is_ascii_digit()
                || (bytes[i + 1] == b'.' && i + 2 < bytes.len() && bytes[i + 2].is_ascii_digit()))
        {
            i += 1;
            while i < bytes.len()
                && (bytes[i].is_ascii_digit()
                    || matches!(bytes[i], b'.' | b'e' | b'E' | b'+' | b'-'))
            {
                i += 1;
            }
            let raw = src[s..i].to_string();
            out.push(tok(src, TokenKind::Identifier, s, i, raw));
            continue;
        }
        if cwt_mode {
            if let Some(end) = cwt_identifier_end(src, s) {
                i = end;
                out.push(tok(src, TokenKind::Identifier, s, i, src[s..i].to_owned()));
                continue;
            }
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
        if cwt_mode {
            if let Some(end) = cwt_identifier_end(src, s) {
                i = end;
            } else {
                while i < bytes.len()
                    && !bytes[i].is_ascii_whitespace()
                    && !b"{}#\"<>!=+-".contains(&bytes[i])
                {
                    i += 1;
                }
            }
        } else {
            while i < bytes.len()
                && !bytes[i].is_ascii_whitespace()
                && !b"{}#\"<>!=+-".contains(&bytes[i])
            {
                i += 1;
            }
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
fn cwt_identifier_end(src: &str, start: usize) -> Option<usize> {
    let mut end = start;
    for (relative, character) in src[start..].char_indices() {
        if character.is_whitespace() || matches!(character, '{' | '}' | '#' | '"' | '=') {
            break;
        }
        end = start + relative + character.len_utf8();
    }
    if end == start {
        return None;
    }
    let token = &src[start..end];
    let operator_only = matches!(token, "<" | ">" | "!" | "<=" | ">=" | "!=" | "==" | "?=");
    (!operator_only).then_some(end)
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
        key_prefix: Option<Box<Token>>,
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
    ColourLiteral {
        raw: String,
        typed: Box<TypedValue>,
        range: ByteRange,
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
    parse_with_lexer(src, lex)
}

/// Parse CWT-compatible syntax using the dedicated angle-expression lexer.
pub fn parse_cwt_compatible(src: &str) -> Result<Cst, Vec<ParseError>> {
    parse_with_lexer(src, lex_cwt)
}

fn parse_with_lexer(
    src: &str,
    lexer: fn(&str) -> Result<Vec<Token>, ParseError>,
) -> Result<Cst, Vec<ParseError>> {
    let tokens = match lexer(src) {
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
    fn consume_clause(&mut self) -> Option<Token> {
        let mut depth = 1usize;
        loop {
            let kind = self.tokens[self.at].kind.clone();
            match kind {
                TokenKind::Eof => return None,
                TokenKind::LBrace => {
                    self.take();
                    depth += 1;
                }
                TokenKind::RBrace => {
                    let close = self.take();
                    depth -= 1;
                    if depth == 0 {
                        return Some(close);
                    }
                }
                _ => {
                    self.take();
                }
            }
        }
    }
    fn key_prefix(&mut self, key: &mut Token) -> Option<Box<Token>> {
        if !matches!(
            self.peek().kind,
            TokenKind::Identifier | TokenKind::QuotedString
        ) || self.peek().value.starts_with('@')
        {
            return None;
        }
        let checkpoint = self.at;
        let candidate = self.take();
        if matches!(self.peek().kind, TokenKind::Operator(_)) {
            Some(Box::new(std::mem::replace(key, candidate)))
        } else {
            self.at = checkpoint;
            None
        }
    }

    fn colour_literal(&mut self) -> Option<Box<CstNode>> {
        let head = self.peek().clone();
        let lower = head.value.to_ascii_lowercase();
        if lower != "rgb" && lower != "hsv" {
            return None;
        }
        self.take();
        let mut qualifier = None;
        if lower == "hsv" && self.peek().value == "360" {
            qualifier = Some(self.take());
        }
        if !matches!(self.peek().kind, TokenKind::LBrace) {
            self.errors
                .push(error(self.src, "invalid colour literal", head.range.start));
            return None;
        }
        let open = self.take();
        let mut components = Vec::new();
        while !matches!(self.peek().kind, TokenKind::RBrace | TokenKind::Eof) {
            components.push(self.take());
        }
        let close = if matches!(self.peek().kind, TokenKind::RBrace) {
            Some(self.take())
        } else {
            None
        };
        let valid_count = (3..=4).contains(&components.len());
        let valid_types = if lower == "rgb" {
            components.iter().all(|t| t.value.parse::<i64>().is_ok())
        } else {
            components
                .iter()
                .all(|token| token.value.parse::<f64>().is_ok())
        };
        if close.is_none() || !valid_count || !valid_types {
            self.errors.push(error(
                self.src,
                "invalid colour components",
                head.range.start,
            ));
        }
        let typed = if lower == "rgb" {
            TypedValue::Rgb(
                components
                    .iter()
                    .filter_map(|t| t.value.parse().ok())
                    .collect(),
            )
        } else {
            TypedValue::Hsv {
                components: components.iter().map(|t| t.value.clone()).collect(),
                degrees: qualifier.is_some(),
            }
        };
        let end = close
            .as_ref()
            .map_or(open.range.end, |token| token.range.end);
        Some(Box::new(CstNode::ColourLiteral {
            raw: self.src[head.range.start..end].to_owned(),
            typed: Box::new(typed),
            range: ByteRange {
                start: head.range.start,
                end,
            },
        }))
    }

    fn nodes(&mut self, in_clause: bool) -> Vec<CstNode> {
        let mut v = Vec::new();
        loop {
            self.skip();
            let k = self.tokens[self.at].kind.clone();
            if matches!(k, TokenKind::Eof) {
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
            if matches!(self.peek().kind, TokenKind::LBrace) {
                let open = self.take();
                let clause_start = open.range.start;
                self.depth += 1;
                let children = self.nodes(true);
                self.depth -= 1;
                let close = if matches!(self.peek().kind, TokenKind::RBrace) {
                    Some(self.take())
                } else {
                    None
                };
                let end = close
                    .as_ref()
                    .map_or(open.range.end, |token| token.range.end);
                v.push(CstNode::Clause {
                    open,
                    children,
                    close,
                    range: ByteRange {
                        start: clause_start,
                        end,
                    },
                });
                continue;
            }
            let mut key = self.take();
            let key_start = key.range.start;
            let key_prefix = self.key_prefix(&mut key);
            if matches!(self.peek().kind, TokenKind::Operator(_)) {
                let op = match self.take().kind {
                    TokenKind::Operator(x) => x,
                    _ => unreachable!(),
                };
                if matches!(
                    self.peek().kind,
                    TokenKind::Eof | TokenKind::RBrace | TokenKind::Operator(_)
                ) {
                    let at = self.peek().range.start;
                    self.errors.push(error(self.src, "MissingValue", at));
                    v.push(CstNode::Assignment {
                        key_prefix: key_prefix.clone(),
                        key: Box::new(CstNode::Bare { token: key.clone() }),
                        operator: op,
                        value: Box::new(CstNode::Error { token: key }),
                        range: ByteRange {
                            start: key_start,
                            end: at,
                        },
                    });
                    continue;
                }
                if let Some(colour) = self.colour_literal() {
                    let end = match colour.as_ref() {
                        CstNode::ColourLiteral { range, .. } => range.end,
                        _ => unreachable!(),
                    };
                    v.push(CstNode::Assignment {
                        key_prefix: key_prefix.clone(),
                        key: Box::new(CstNode::Bare { token: key }),
                        operator: op,
                        value: colour,
                        range: ByteRange {
                            start: key_start,
                            end,
                        },
                    });
                    continue;
                }
                if matches!(self.peek().kind, TokenKind::LBrace) {
                    let open = self.take();
                    let (children, close) = if self.depth >= MAX_DEPTH {
                        self.errors.push(error(
                            self.src,
                            "maximum nesting depth exceeded",
                            open.range.start,
                        ));
                        (Vec::new(), self.consume_clause())
                    } else {
                        self.depth += 1;
                        let children = self.nodes(true);
                        self.depth -= 1;
                        let close = if matches!(self.peek().kind, TokenKind::RBrace) {
                            Some(self.take())
                        } else {
                            None
                        };
                        (children, close)
                    };
                    let end = close.as_ref().map_or(open.range.end, |x| x.range.end);
                    if close.is_none() {
                        self.errors
                            .push(error(self.src, "unclosed clause", open.range.start));
                    }
                    v.push(CstNode::Assignment {
                        key_prefix: key_prefix.clone(),
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
                        key_prefix: key_prefix.clone(),
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
                key_prefix,
                key,
                operator,
                value,
                ..
            } => {
                if let Some(prefix) = key_prefix {
                    out.push_str(&render_token(prefix));
                    out.push(' ');
                }
                print_nodes(std::slice::from_ref(key), depth, out);
                out.push_str(operator.text());
                out.push(' ');
                print_nodes(std::slice::from_ref(value), depth, out);
                out.push('\n')
            }
            CstNode::ColourLiteral { raw, .. } => {
                out.push_str(raw);
                out.push(' ');
            }
            CstNode::Clause { children, .. } => {
                out.push_str("{\n");
                print_nodes(children, depth + 1, out);
                out.push_str("} ")
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypedValue {
    String(String),
    QuotedString(String),
    Integer(i64),
    Decimal(String),
    Boolean(bool),
    Rgb(Vec<i64>),
    Hsv {
        components: Vec<String>,
        degrees: bool,
    },
}

#[must_use]
pub fn classify_scalar(raw: &str, quoted: bool) -> TypedValue {
    if quoted {
        return TypedValue::QuotedString(raw.to_owned());
    }
    if raw == "yes" {
        return TypedValue::Boolean(true);
    }
    if raw == "no" {
        return TypedValue::Boolean(false);
    }
    let unsigned = raw.strip_prefix('-').unwrap_or(raw);
    let leading_zero = unsigned.len() > 1
        && unsigned.starts_with('0')
        && unsigned.as_bytes().get(1).is_some_and(u8::is_ascii_digit);
    if !leading_zero {
        if let Ok(value) = raw.parse::<i64>() {
            return TypedValue::Integer(value);
        }
        if raw.parse::<f64>().is_ok() && raw.chars().any(|value| matches!(value, '.' | 'e' | 'E')) {
            return TypedValue::Decimal(raw.to_owned());
        }
    }
    TypedValue::String(raw.to_owned())
}

#[must_use]
pub fn classify_colour_literal(source: &str) -> Option<TypedValue> {
    let tokens = lex(source).ok()?;
    let values: Vec<_> = tokens
        .iter()
        .filter(|token| {
            !token.is_trivia() && !matches!(token.kind, TokenKind::Eof | TokenKind::Comment)
        })
        .collect();
    let (head, body) = values.split_first()?;
    let mut at = 0;
    let degrees = head.value == "hsv360"
        || (head.value == "hsv" && body.first().is_some_and(|token| token.value == "360"));
    if head.value == "hsv" && degrees {
        at = 1;
    }
    let open = body.get(at)?;
    if !matches!(open.kind, TokenKind::LBrace) {
        return None;
    }
    let close = body.last()?;
    if !matches!(close.kind, TokenKind::RBrace) {
        return None;
    }
    let components = &body[at + 1..body.len() - 1];
    if !(3..=4).contains(&components.len()) {
        return None;
    }
    match head.value.as_str() {
        "rgb" | "RGB" => components
            .iter()
            .map(|token| token.value.parse::<i64>().ok())
            .collect::<Option<Vec<_>>>()
            .map(TypedValue::Rgb),
        "hsv" | "HSV" | "hsv360" => {
            let values = components
                .iter()
                .map(|token| token.value.parse::<f64>().ok().map(|_| token.value.clone()))
                .collect::<Option<Vec<_>>>()?;
            Some(TypedValue::Hsv {
                components: values,
                degrees,
            })
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScriptEncoding {
    Utf8,
    Windows1252,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecodeError {
    pub offset: usize,
    pub message: &'static str,
}

pub fn decode_script_bytes(bytes: &[u8], encoding: ScriptEncoding) -> Result<String, DecodeError> {
    match encoding {
        ScriptEncoding::Utf8 => std::str::from_utf8(bytes)
            .map(str::to_owned)
            .map_err(|error| DecodeError {
                offset: error.valid_up_to(),
                message: "invalid UTF-8",
            }),
        ScriptEncoding::Windows1252 => Ok(bytes
            .iter()
            .map(|byte| decode_windows_1252(*byte))
            .collect()),
    }
}

fn decode_windows_1252(byte: u8) -> char {
    const SPECIAL: [char; 32] = [
        '€', '\u{0081}', '‚', 'ƒ', '„', '…', '†', '‡', 'ˆ', '‰', 'Š', '‹', 'Œ', '\u{008D}', 'Ž',
        '\u{008F}', '\u{0090}', '‘', '’', '“', '”', '•', '–', '—', '˜', '™', 'š', '›', 'œ',
        '\u{009D}', 'ž', 'Ÿ',
    ];
    match byte {
        0x80..=0x9F => SPECIAL[usize::from(byte - 0x80)],
        _ => char::from_u32(u32::from(byte)).unwrap_or(char::REPLACEMENT_CHARACTER),
    }
}

#[must_use]
pub fn print_canonical(cst: &Cst) -> String {
    let mut output = String::new();
    print_canonical_nodes(&cst.roots, 0, &mut output);
    output
}

fn print_canonical_nodes(nodes: &[CstNode], depth: usize, output: &mut String) {
    for node in nodes {
        output.push_str(&"\t".repeat(depth));
        match node {
            CstNode::Comment { token } => {
                output.push_str(&token.raw);
                output.push('\n');
            }
            CstNode::Bare { token } | CstNode::Error { token } | CstNode::Trivia { token } => {
                output.push_str(&render_token(token));
                output.push('\n');
            }
            CstNode::Assignment {
                key_prefix,
                key,
                operator,
                value,
                ..
            } => {
                if let Some(prefix) = key_prefix {
                    output.push_str(&render_token(prefix));
                    output.push(' ');
                }
                output.push_str(&render_node_inline(key));
                output.push(' ');
                output.push_str(operator.text());
                output.push(' ');
                match value.as_ref() {
                    CstNode::Clause { children, .. } => {
                        output.push_str("{\n");
                        print_canonical_nodes(children, depth + 1, output);
                        output.push_str(&"\t".repeat(depth));
                        output.push_str("}\n");
                    }
                    CstNode::ColourLiteral { typed, .. } => {
                        output.push_str("{\n");
                        match typed.as_ref() {
                            TypedValue::Rgb(values) => {
                                for value in values {
                                    output.push_str(&"\t".repeat(depth + 1));
                                    output.push_str(&value.to_string());
                                    output.push('\n');
                                }
                            }
                            TypedValue::Hsv { components, .. } => {
                                for value in components {
                                    output.push_str(&"\t".repeat(depth + 1));
                                    output.push_str(value);
                                    output.push('\n');
                                }
                            }
                            _ => {}
                        }
                        output.push_str(&"\t".repeat(depth));
                        output.push_str("}\n");
                    }
                    other => {
                        output.push_str(&render_node_inline(other));
                        output.push('\n');
                    }
                }
            }
            CstNode::Clause { children, .. } => {
                output.push_str("{\n");
                print_canonical_nodes(children, depth + 1, output);
                output.push_str(&"\t".repeat(depth));
                output.push_str("}\n");
            }
            CstNode::ColourLiteral { raw, .. } => {
                output.push_str(raw);
                output.push('\n');
            }
        }
    }
}

fn render_node_inline(node: &CstNode) -> String {
    match node {
        CstNode::Bare { token }
        | CstNode::Error { token }
        | CstNode::Comment { token }
        | CstNode::Trivia { token } => render_token(token),
        CstNode::ColourLiteral { raw, .. } => raw.clone(),
        CstNode::Clause { .. } | CstNode::Assignment { .. } => String::new(),
    }
}

fn render_token(token: &Token) -> String {
    if matches!(token.kind, TokenKind::QuotedString) {
        format!("\"{}\"", token.value)
    } else {
        token.value.clone()
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
    fn diagnostics_have_stable_codes_and_single_clause_error() {
        let cases = [
            ("x = \"unterminated", "SYNTAX_UNCLOSED_QUOTE"),
            ("x = { y = 1", "SYNTAX_UNCLOSED_CLAUSE"),
            ("}", "SYNTAX_UNEXPECTED_RBRACE"),
            ("x =", "SYNTAX_MISSING_VALUE"),
            ("x = rgb { 1 2 }", "SYNTAX_INVALID_COLOUR_COMPONENTS"),
        ];
        for (source, code) in cases {
            let errors = parse(source).expect_err("fixture must fail");
            assert_eq!(errors.len(), 1, "{source}");
            assert_eq!(errors[0].code, code, "{source}");
        }
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
    fn maximum_nesting_boundary_is_enforced_without_recursion() {
        for levels in [MAX_DEPTH, MAX_DEPTH + 1, 10_000] {
            let source = format!(
                "a={{{}x{}}}",
                "b={".repeat(levels - 1),
                "}".repeat(levels - 1)
            );
            let loss_aware = parse_loss_aware(&source);
            assert!(loss_aware.tokens.iter().all(
                |token| token.range.start <= token.range.end && token.range.end <= source.len()
            ));
            if levels == MAX_DEPTH {
                assert!(parse(&source).is_ok());
            } else {
                let errors = parse(&source).expect_err("excessive nesting must fail");
                assert!(
                    errors
                        .iter()
                        .any(|error| error.message.contains("maximum nesting"))
                );
            }
        }
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
    fn typed_scalars_preserve_leading_zero_and_int64() {
        assert_eq!(classify_scalar("yes", false), TypedValue::Boolean(true));
        assert_eq!(classify_scalar("no", false), TypedValue::Boolean(false));
        assert_eq!(
            classify_scalar("80000000000000", false),
            TypedValue::Integer(80_000_000_000_000)
        );
        assert_eq!(
            classify_scalar("007", false),
            TypedValue::String("007".to_owned())
        );
        assert_eq!(
            classify_scalar("1.25", false),
            TypedValue::Decimal("1.25".to_owned())
        );
        assert_eq!(
            classify_scalar("yes", true),
            TypedValue::QuotedString("yes".to_owned())
        );
    }

    #[test]
    fn rgb_hsv_and_alpha_are_typed() {
        assert_eq!(
            classify_colour_literal("rgb { 1 2 3 4 }"),
            Some(TypedValue::Rgb(vec![1, 2, 3, 4]))
        );
        assert_eq!(
            classify_colour_literal("HSV { 0.1 0.2 0.3 }"),
            Some(TypedValue::Hsv {
                components: vec!["0.1".into(), "0.2".into(), "0.3".into()],
                degrees: false
            })
        );
        assert_eq!(
            classify_colour_literal("hsv 360 { 1 2 3 }"),
            Some(TypedValue::Hsv {
                components: vec!["1".into(), "2".into(), "3".into()],
                degrees: true
            })
        );
        assert_eq!(classify_colour_literal("rgb { 1 2 }"), None);
    }

    #[test]
    fn colour_literals_are_assignment_values() {
        let source =
            "a = rgb { 1 2 3 } b = RGB { 1 2 3 4 } c = HSV { 0.1 0.2 0.3 } d = hsv 360 { 1 2 3 4 }";
        let parsed = parse(source).unwrap();
        assert_eq!(parsed.roots.len(), 4);
        assert!(parsed.roots.iter().all(|node| matches!(node, CstNode::Assignment { value, .. } if matches!(value.as_ref(), CstNode::ColourLiteral { .. }))));
        assert_eq!(parse(&print_canonical(&parsed)).unwrap().roots.len(), 4);
        assert!(parse("bad = rgb { 1 2 }").is_err());
        assert!(parse("bad = HSV { one two three }").is_err());
    }

    #[test]
    fn windows_1252_decoder_is_explicit() {
        assert_eq!(
            decode_script_bytes(&[0x53, 0x8A, 0x9A], ScriptEncoding::Windows1252).unwrap(),
            "SŠš"
        );
        assert!(decode_script_bytes(&[0xFF], ScriptEncoding::Utf8).is_err());
    }

    #[test]
    fn signed_values_missing_values_and_standalone_clauses() {
        let parsed = parse("negative = -12 decimal = +1.5 exponent = -2e+3 { one two }").unwrap();
        let values: Vec<_> = parsed
            .tokens
            .iter()
            .map(|token| token.value.as_str())
            .collect();
        assert!(values.contains(&"-12"));
        assert!(values.contains(&"+1.5"));
        assert!(values.contains(&"-2e+3"));
        assert!(matches!(parsed.roots.last(), Some(CstNode::Clause { .. })));
        let errors =
            parse("outer = { missing = }").expect_err("missing assignment value must fail");
        assert!(errors.iter().any(|error| error.message == "MissingValue"));
    }

    #[test]
    fn jomini_key_prefix_is_preserved_and_printed() {
        let parsed = parse("not_event country_event = { value = yes }").unwrap();
        let CstNode::Assignment {
            key_prefix, key, ..
        } = &parsed.roots[0]
        else {
            panic!("expected assignment");
        };
        assert_eq!(
            key_prefix.as_ref().map(|token| token.value.as_str()),
            Some("not_event")
        );
        assert!(matches!(key.as_ref(), CstNode::Bare { token } if token.value == "country_event"));
        assert_eq!(
            print_canonical(&parsed),
            "not_event country_event = {\n\tvalue = yes\n}\n"
        );
        let reparsed = parse(&print_canonical(&parsed)).unwrap();
        assert_eq!(print_canonical(&reparsed), print_canonical(&parsed));
    }

    #[test]
    fn canonical_printer_matches_simple_fixture_shape() {
        let parsed = parse("key=value label={ valuea valueb }").unwrap();
        assert_eq!(
            print_canonical(&parsed),
            "key = value\nlabel = {\n\tvaluea\n\tvalueb\n}\n"
        );
    }

    #[test]
    fn stable() {
        let s = "a={b=1} c=\"x\"";
        let a = parse(s).unwrap().normalized();
        assert_eq!(parse(&a).unwrap().normalized(), a)
    }
}
