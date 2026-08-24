#![forbid(unsafe_code)]
#![allow(
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    missing_docs,
    dead_code,
    unused_variables,
    unused_mut,
    ambiguous_glob_reexports
)]
//! Deterministic, lossless Rust frontend and runtime model for Paradox FX shaders.
//! Unknown and malformed input stays observable; bounded traversal protects editor clients.

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};

pub const MAX_INPUT_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_INCLUDE_DEPTH: usize = 256;
pub const MAX_COMPILE_UNIT_MEMBERS: usize = 4096;
pub const MAX_MACRO_EXPANSION_DEPTH: usize = 64;
pub const MAX_SATISFIABILITY_SYMBOLS: usize = 12;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct TextSpan {
    pub start_offset: usize,
    pub end_offset: usize,
}
impl TextSpan {
    pub const fn new(start_offset: usize, end_offset: usize) -> Self {
        Self {
            start_offset,
            end_offset,
        }
    }
    pub const fn length(self) -> usize {
        self.end_offset.saturating_sub(self.start_offset)
    }
}
fn slice_text(text: &str, span: TextSpan) -> &str {
    text.get(span.start_offset..span.end_offset).unwrap_or("")
}
fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || matches!(c, '_' | '$' | '@')
}
fn is_ident_part(c: char) -> bool {
    c.is_alphanumeric() || matches!(c, '_' | '$' | '@' | '.' | ':' | '/' | '\\' | '-' | '!')
}
fn is_newline(b: u8) -> bool {
    b == b'\r' || b == b'\n'
}
fn line_end(text: &[u8], mut i: usize) -> usize {
    while i < text.len() && !is_newline(text[i]) {
        i += 1;
    }
    i
}

pub mod syntax {
    use super::*;

    #[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub enum ShaderTokenKind {
        Identifier,
        NumberLiteral,
        StringLiteral,
        Whitespace,
        NewLine,
        LineComment,
        BlockComment,
        DirectiveLine,
        HlslOpen,
        HlslClose,
        OpenBrace,
        CloseBrace,
        OpenParen,
        CloseParen,
        OpenBracket,
        CloseBracket,
        Comma,
        Semicolon,
        Colon,
        Equals,
        Dot,
        Operator,
        BadToken,
        EndOfFile,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct ShaderToken {
        pub kind: ShaderTokenKind,
        pub text: String,
        pub span: TextSpan,
    }
    impl ShaderToken {
        pub fn is_trivia(&self) -> bool {
            matches!(
                self.kind,
                ShaderTokenKind::Whitespace
                    | ShaderTokenKind::NewLine
                    | ShaderTokenKind::LineComment
                    | ShaderTokenKind::BlockComment
            )
        }
    }
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub enum SyntaxDiagnosticKind {
        UnterminatedString,
        UnterminatedComment,
        UnterminatedBlock,
        UnterminatedHlslRegion,
        UnexpectedClosingDelimiter,
        MissingName,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct SyntaxDiagnostic {
        pub kind: SyntaxDiagnosticKind,
        pub message: String,
        pub span: TextSpan,
    }
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
    pub enum ShaderNodeKind {
        ShaderDocument,
        Includes,
        IncludeFile,
        VertexShader,
        PixelShader,
        GeometryShader,
        MainCode,
        VertexStruct,
        ConstantBuffer,
        BlendState,
        DepthStencilState,
        RasterizerState,
        Samplers,
        Sampler,
        Effect,
        Property,
        HlslRegion,
        PreprocessorDirective,
        UnknownNode,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct ShaderSyntaxNode {
        pub kind: ShaderNodeKind,
        pub name: Option<String>,
        pub span: TextSpan,
        pub name_span: Option<TextSpan>,
        pub token_start: usize,
        pub token_end: usize,
        pub children: Vec<ShaderSyntaxNode>,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct ShaderSyntaxTree {
        pub filepath: String,
        pub text: String,
        pub tokens: Vec<ShaderToken>,
        pub root: ShaderSyntaxNode,
        pub diagnostics: Vec<SyntaxDiagnostic>,
    }
    impl ShaderSyntaxTree {
        pub fn is_lossless(&self) -> bool {
            let mut end = 0;
            for token in self
                .tokens
                .iter()
                .filter(|t| t.kind != ShaderTokenKind::EndOfFile)
            {
                if token.span.start_offset != end {
                    return false;
                }
                end = token.span.end_offset;
            }
            end == self.text.len()
        }
        pub fn source_text<'a>(&'a self, node: &ShaderSyntaxNode) -> &'a str {
            slice_text(&self.text, node.span)
        }
    }

    fn add(
        tokens: &mut Vec<ShaderToken>,
        text: &str,
        kind: ShaderTokenKind,
        start: usize,
        end: usize,
    ) {
        tokens.push(ShaderToken {
            kind,
            text: text.get(start..end).unwrap_or("").to_owned(),
            span: TextSpan::new(start, end),
        });
    }
    fn directive_at(bytes: &[u8], offset: usize, line_has_content: bool) -> bool {
        if line_has_content || offset >= bytes.len() || !matches!(bytes[offset], b'#' | b'@') {
            return false;
        }
        let mut i = offset + 1;
        while i < bytes.len() && matches!(bytes[i], b' ' | b'\t') {
            i += 1;
        }
        let start = i;
        while i < bytes.len() && (bytes[i] as char).is_ascii_alphabetic() {
            i += 1;
        }
        if start == i {
            return false;
        }
        matches!(
            std::str::from_utf8(&bytes[start..i])
                .unwrap_or("")
                .to_ascii_lowercase()
                .as_str(),
            "if" | "ifdef"
                | "ifndef"
                | "elif"
                | "else"
                | "endif"
                | "define"
                | "undef"
                | "include"
                | "pragma"
                | "error"
                | "line"
        )
    }
    pub fn lex(text: &str) -> (Vec<ShaderToken>, Vec<SyntaxDiagnostic>) {
        let mut tokens = Vec::new();
        let mut diagnostics = Vec::new();
        let bytes = text.as_bytes();
        let mut i = 0;
        let mut line_content = false;
        while i < bytes.len() {
            let start = i;
            if is_newline(bytes[i]) {
                i += 1;
                if bytes[start] == b'\r' && i < bytes.len() && bytes[i] == b'\n' {
                    i += 1;
                }
                add(&mut tokens, text, ShaderTokenKind::NewLine, start, i);
                line_content = false;
                continue;
            }
            if matches!(bytes[i], b' ' | b'\t' | 0x0c) {
                i += 1;
                while i < bytes.len() && matches!(bytes[i], b' ' | b'\t' | 0x0c) {
                    i += 1;
                }
                add(&mut tokens, text, ShaderTokenKind::Whitespace, start, i);
                continue;
            }
            if directive_at(bytes, i, line_content) {
                i = line_end(bytes, i);
                add(&mut tokens, text, ShaderTokenKind::DirectiveLine, start, i);
                line_content = true;
                continue;
            }
            if bytes[i] == b'#' || bytes[i..].starts_with(b"//") {
                i = line_end(bytes, i);
                add(&mut tokens, text, ShaderTokenKind::LineComment, start, i);
                line_content = true;
                continue;
            }
            if bytes[i..].starts_with(b"/*") {
                i += 2;
                let mut terminated = false;
                while i < bytes.len() {
                    if bytes[i..].starts_with(b"*/") {
                        i += 2;
                        terminated = true;
                        break;
                    }
                    i += 1;
                }
                add(&mut tokens, text, ShaderTokenKind::BlockComment, start, i);
                line_content = true;
                if !terminated {
                    diagnostics.push(SyntaxDiagnostic {
                        kind: SyntaxDiagnosticKind::UnterminatedComment,
                        message: "Unterminated block comment.".into(),
                        span: TextSpan::new(start, i),
                    });
                }
                continue;
            }
            if bytes[i] == b'"' || bytes[i] == 39 {
                let quote = bytes[i];
                i += 1;
                let mut terminated = false;
                while i < bytes.len() && !is_newline(bytes[i]) {
                    if bytes[i] == 92 && i + 1 < bytes.len() {
                        i += 2;
                    } else if bytes[i] == quote {
                        i += 1;
                        terminated = true;
                        break;
                    } else {
                        i += 1;
                    }
                }
                add(&mut tokens, text, ShaderTokenKind::StringLiteral, start, i);
                line_content = true;
                if !terminated {
                    diagnostics.push(SyntaxDiagnostic {
                        kind: SyntaxDiagnosticKind::UnterminatedString,
                        message: "Unterminated string literal.".into(),
                        span: TextSpan::new(start, i),
                    });
                }
                continue;
            }
            if bytes[i..].starts_with(b"[[") {
                i += 2;
                add(&mut tokens, text, ShaderTokenKind::HlslOpen, start, i);
                line_content = true;
                continue;
            }
            if bytes[i..].starts_with(b"]]") {
                i += 2;
                add(&mut tokens, text, ShaderTokenKind::HlslClose, start, i);
                line_content = true;
                continue;
            }
            let c = text[start..].chars().next().unwrap_or('\0');
            if is_ident_start(c) {
                i += c.len_utf8();
                while i < bytes.len() {
                    let n = text[i..].chars().next().unwrap_or('\0');
                    if !is_ident_part(n) {
                        break;
                    }
                    i += n.len_utf8();
                }
                add(&mut tokens, text, ShaderTokenKind::Identifier, start, i);
                line_content = true;
                continue;
            }
            if bytes[i].is_ascii_digit()
                || (bytes[i] == b'.' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_digit())
            {
                i += 1;
                while i < bytes.len()
                    && (bytes[i].is_ascii_alphanumeric() || matches!(bytes[i], b'.' | b'_'))
                {
                    i += 1;
                }
                add(&mut tokens, text, ShaderTokenKind::NumberLiteral, start, i);
                line_content = true;
                continue;
            }
            let (kind, width) = match bytes[i] {
                b'{' => (ShaderTokenKind::OpenBrace, 1),
                b'}' => (ShaderTokenKind::CloseBrace, 1),
                b'(' => (ShaderTokenKind::OpenParen, 1),
                b')' => (ShaderTokenKind::CloseParen, 1),
                b'[' => (ShaderTokenKind::OpenBracket, 1),
                b']' => (ShaderTokenKind::CloseBracket, 1),
                b',' => (ShaderTokenKind::Comma, 1),
                b';' => (ShaderTokenKind::Semicolon, 1),
                b':' => (ShaderTokenKind::Colon, 1),
                b'=' if i + 1 < bytes.len() && bytes[i + 1] == b'=' => {
                    (ShaderTokenKind::Operator, 2)
                }
                b'=' => (ShaderTokenKind::Equals, 1),
                b'.' => (ShaderTokenKind::Dot, 1),
                b'+' | b'-' | b'*' | b'/' | b'%' | b'!' | b'<' | b'>' | b'&' | b'|' | b'^'
                | b'~' | b'?' => {
                    let width = if i + 1 < bytes.len()
                        && (bytes[i + 1] == b'='
                            || (bytes[i] == b'&' && bytes[i + 1] == b'&')
                            || (bytes[i] == b'|' && bytes[i + 1] == b'|'))
                    {
                        2
                    } else {
                        1
                    };
                    (ShaderTokenKind::Operator, width)
                }
                _ => (ShaderTokenKind::BadToken, 1),
            };
            i += width;
            add(&mut tokens, text, kind, start, i);
            line_content = true;
        }
        tokens.push(ShaderToken {
            kind: ShaderTokenKind::EndOfFile,
            text: String::new(),
            span: TextSpan::new(text.len(), text.len()),
        });
        (tokens, diagnostics)
    }
    fn trivia(kind: ShaderTokenKind) -> bool {
        matches!(
            kind,
            ShaderTokenKind::Whitespace
                | ShaderTokenKind::NewLine
                | ShaderTokenKind::LineComment
                | ShaderTokenKind::BlockComment
        )
    }
    fn next_significant(tokens: &[ShaderToken], mut i: usize, end: usize) -> usize {
        while i < end && trivia(tokens[i].kind) {
            i += 1;
        }
        i
    }
    fn matching(
        tokens: &[ShaderToken],
        open: ShaderTokenKind,
        close: ShaderTokenKind,
        start: usize,
        end: usize,
    ) -> Option<usize> {
        let mut depth = 0;
        for i in start..end {
            if tokens[i].kind == open {
                depth += 1;
            } else if tokens[i].kind == close {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
        }
        None
    }
    fn classify(parent: Option<ShaderNodeKind>, keyword: &str) -> ShaderNodeKind {
        match (keyword.to_ascii_lowercase().as_str(), parent) {
            ("includes", _) => ShaderNodeKind::Includes,
            ("vertexshader", _) => ShaderNodeKind::VertexShader,
            ("pixelshader", _) => ShaderNodeKind::PixelShader,
            ("geometryshader", _) => ShaderNodeKind::GeometryShader,
            ("vertexstruct", _) => ShaderNodeKind::VertexStruct,
            ("constantbuffer", _) => ShaderNodeKind::ConstantBuffer,
            ("blendstate", _) => ShaderNodeKind::BlendState,
            ("depthstencilstate", _) => ShaderNodeKind::DepthStencilState,
            ("rasterizerstate", _) => ShaderNodeKind::RasterizerState,
            ("samplers", _) => ShaderNodeKind::Samplers,
            ("effect", _) => ShaderNodeKind::Effect,
            (_, Some(ShaderNodeKind::Samplers)) => ShaderNodeKind::Sampler,
            _ => ShaderNodeKind::Property,
        }
    }
    fn unquote(value: &str) -> String {
        if value.len() >= 2
            && ((value.starts_with('"') && value.ends_with('"'))
                || (value.starts_with('\'') && value.ends_with('\'')))
        {
            value[1..value.len() - 1].to_owned()
        } else {
            value.to_owned()
        }
    }

    pub fn parse(filepath: &str, text: &str) -> ShaderSyntaxTree {
        let (tokens, mut diagnostics) = lex(text);
        let end = tokens.len().saturating_sub(1);
        fn sequence(
            tokens: &[ShaderToken],
            text: &str,
            diagnostics: &mut Vec<SyntaxDiagnostic>,
            parent: Option<ShaderNodeKind>,
            mut current: usize,
            end: usize,
        ) -> Vec<ShaderSyntaxNode> {
            let mut nodes = Vec::new();
            while current < end {
                let token = &tokens[current];
                if trivia(token.kind) {
                    current += 1;
                    continue;
                }
                if token.kind == ShaderTokenKind::DirectiveLine {
                    nodes.push(ShaderSyntaxNode {
                        kind: ShaderNodeKind::PreprocessorDirective,
                        name: None,
                        span: token.span,
                        name_span: None,
                        token_start: current,
                        token_end: current,
                        children: Vec::new(),
                    });
                    current += 1;
                    continue;
                }
                if token.kind == ShaderTokenKind::HlslOpen {
                    let close = matching(
                        tokens,
                        ShaderTokenKind::HlslOpen,
                        ShaderTokenKind::HlslClose,
                        current,
                        end,
                    )
                    .unwrap_or(end.saturating_sub(1));
                    if close >= end || tokens[close].kind != ShaderTokenKind::HlslClose {
                        diagnostics.push(SyntaxDiagnostic {
                            kind: SyntaxDiagnosticKind::UnterminatedHlslRegion,
                            message: "Unterminated embedded HLSL region; expected ]].".into(),
                            span: TextSpan::new(token.span.start_offset, text.len()),
                        });
                    }
                    nodes.push(ShaderSyntaxNode {
                        kind: ShaderNodeKind::HlslRegion,
                        name: None,
                        span: TextSpan::new(token.span.start_offset, tokens[close].span.end_offset),
                        name_span: None,
                        token_start: current,
                        token_end: close,
                        children: Vec::new(),
                    });
                    current = close.saturating_add(1);
                    continue;
                }
                if matches!(
                    token.kind,
                    ShaderTokenKind::CloseBrace
                        | ShaderTokenKind::CloseParen
                        | ShaderTokenKind::CloseBracket
                        | ShaderTokenKind::HlslClose
                ) {
                    diagnostics.push(SyntaxDiagnostic {
                        kind: SyntaxDiagnosticKind::UnexpectedClosingDelimiter,
                        message: "Unexpected closing delimiter.".into(),
                        span: token.span,
                    });
                    current += 1;
                    continue;
                }
                if token.kind != ShaderTokenKind::Identifier {
                    nodes.push(ShaderSyntaxNode {
                        kind: ShaderNodeKind::UnknownNode,
                        name: None,
                        span: token.span,
                        name_span: None,
                        token_start: current,
                        token_end: current,
                        children: Vec::new(),
                    });
                    current += 1;
                    continue;
                }
                let keyword = token.text.clone();
                let mut scan = next_significant(tokens, current + 1, end);
                let mut name_index = None;
                if scan < end && tokens[scan].kind == ShaderTokenKind::Identifier {
                    name_index = Some(scan);
                    scan = next_significant(tokens, scan + 1, end);
                }
                if keyword.eq_ignore_ascii_case("MainCode") {
                    let name = name_index;
                    let hlsl = next_significant(
                        tokens,
                        if let Some(i) = name {
                            next_significant(tokens, i + 1, end)
                        } else {
                            scan
                        },
                        end,
                    );
                    if hlsl < end && tokens[hlsl].kind == ShaderTokenKind::HlslOpen {
                        let close = matching(
                            tokens,
                            ShaderTokenKind::HlslOpen,
                            ShaderTokenKind::HlslClose,
                            hlsl,
                            end,
                        )
                        .unwrap_or(end.saturating_sub(1));
                        let mut children = sequence(
                            tokens,
                            text,
                            diagnostics,
                            Some(ShaderNodeKind::MainCode),
                            hlsl + 1,
                            close,
                        );
                        children.push(ShaderSyntaxNode {
                            kind: ShaderNodeKind::HlslRegion,
                            name: None,
                            span: TextSpan::new(
                                tokens[hlsl].span.start_offset,
                                tokens[close].span.end_offset,
                            ),
                            name_span: None,
                            token_start: hlsl,
                            token_end: close,
                            children: Vec::new(),
                        });
                        nodes.push(ShaderSyntaxNode {
                            kind: ShaderNodeKind::MainCode,
                            name: name.map(|i| tokens[i].text.clone()),
                            span: TextSpan::new(
                                token.span.start_offset,
                                tokens[close].span.end_offset,
                            ),
                            name_span: name.map(|i| tokens[i].span),
                            token_start: current,
                            token_end: close,
                            children,
                        });
                        current = close.saturating_add(1);
                        continue;
                    }
                }
                if scan < end && tokens[scan].kind == ShaderTokenKind::Equals {
                    scan = next_significant(tokens, scan + 1, end);
                }
                if scan < end && tokens[scan].kind == ShaderTokenKind::OpenParen {
                    scan = matching(
                        tokens,
                        ShaderTokenKind::OpenParen,
                        ShaderTokenKind::CloseParen,
                        scan,
                        end,
                    )
                    .map_or(end, |i| next_significant(tokens, i + 1, end));
                }
                if scan < end && tokens[scan].kind == ShaderTokenKind::OpenBrace {
                    let close = matching(
                        tokens,
                        ShaderTokenKind::OpenBrace,
                        ShaderTokenKind::CloseBrace,
                        scan,
                        end,
                    )
                    .unwrap_or(end.saturating_sub(1));
                    let kind = classify(parent, &keyword);
                    let special = matches!(
                        kind,
                        ShaderNodeKind::Includes
                            | ShaderNodeKind::VertexShader
                            | ShaderNodeKind::PixelShader
                            | ShaderNodeKind::GeometryShader
                            | ShaderNodeKind::Samplers
                    );
                    let name = if special {
                        None
                    } else if let Some(i) = name_index {
                        Some(tokens[i].text.clone())
                    } else if matches!(kind, ShaderNodeKind::Sampler | ShaderNodeKind::Property) {
                        Some(keyword.clone())
                    } else {
                        None
                    };
                    let name_span = if special {
                        None
                    } else if let Some(i) = name_index {
                        Some(tokens[i].span)
                    } else if matches!(kind, ShaderNodeKind::Sampler | ShaderNodeKind::Property) {
                        Some(token.span)
                    } else {
                        None
                    };
                    let children = if kind == ShaderNodeKind::Includes {
                        let mut includes = Vec::new();
                        let mut nested = 0usize;
                        for i in scan + 1..close {
                            match tokens[i].kind {
                                ShaderTokenKind::OpenBrace => nested += 1,
                                ShaderTokenKind::CloseBrace => nested = nested.saturating_sub(1),
                                ShaderTokenKind::StringLiteral if nested == 0 => {
                                    includes.push(ShaderSyntaxNode {
                                        kind: ShaderNodeKind::IncludeFile,
                                        name: Some(unquote(&tokens[i].text)),
                                        span: tokens[i].span,
                                        name_span: Some(tokens[i].span),
                                        token_start: i,
                                        token_end: i,
                                        children: Vec::new(),
                                    })
                                }
                                _ => {}
                            }
                        }
                        includes
                    } else {
                        sequence(tokens, text, diagnostics, Some(kind), scan + 1, close)
                    };
                    nodes.push(ShaderSyntaxNode {
                        kind,
                        name,
                        span: TextSpan::new(token.span.start_offset, tokens[close].span.end_offset),
                        name_span,
                        token_start: current,
                        token_end: close,
                        children,
                    });
                    if close + 1 >= end {
                        diagnostics.push(SyntaxDiagnostic {
                            kind: SyntaxDiagnosticKind::UnterminatedBlock,
                            message: format!("Unterminated {keyword} block; expected }}."),
                            span: TextSpan::new(token.span.start_offset, text.len()),
                        });
                    }
                    current = close.saturating_add(1);
                    continue;
                }
                let mut p = current;
                while p + 1 < end
                    && tokens[p].kind != ShaderTokenKind::Semicolon
                    && tokens[p].kind != ShaderTokenKind::NewLine
                {
                    p += 1;
                }
                let kind = if keyword.eq_ignore_ascii_case("Effect") {
                    ShaderNodeKind::Effect
                } else if keyword.eq_ignore_ascii_case("VertexStruct") {
                    ShaderNodeKind::VertexStruct
                } else if keyword.eq_ignore_ascii_case("ConstantBuffer") {
                    ShaderNodeKind::ConstantBuffer
                } else {
                    ShaderNodeKind::Property
                };
                nodes.push(ShaderSyntaxNode {
                    kind,
                    name: if kind == ShaderNodeKind::Property {
                        Some(keyword)
                    } else {
                        name_index.map(|i| tokens[i].text.clone())
                    },
                    span: TextSpan::new(
                        token.span.start_offset,
                        tokens[p.min(end.saturating_sub(1))].span.end_offset,
                    ),
                    name_span: if kind == ShaderNodeKind::Property {
                        Some(token.span)
                    } else {
                        name_index.map(|i| tokens[i].span)
                    },
                    token_start: current,
                    token_end: p.min(end.saturating_sub(1)),
                    children: Vec::new(),
                });
                current = p + 1;
            }
            nodes
        }
        let children = sequence(&tokens, text, &mut diagnostics, None, 0, end);
        let root = ShaderSyntaxNode {
            kind: ShaderNodeKind::ShaderDocument,
            name: None,
            span: TextSpan::new(0, text.len()),
            name_span: None,
            token_start: 0,
            token_end: end,
            children,
        };
        ShaderSyntaxTree {
            filepath: filepath.to_owned(),
            text: text.to_owned(),
            tokens,
            root,
            diagnostics,
        }
    }
    pub fn descendants(node: &ShaderSyntaxNode) -> Vec<&ShaderSyntaxNode> {
        fn walk<'a>(node: &'a ShaderSyntaxNode, out: &mut Vec<&'a ShaderSyntaxNode>) {
            for child in &node.children {
                out.push(child);
                walk(child, out);
            }
        }
        let mut out = Vec::new();
        walk(node, &mut out);
        out
    }
    pub fn nodes_of_kind(tree: &ShaderSyntaxTree, kind: ShaderNodeKind) -> Vec<&ShaderSyntaxNode> {
        descendants(&tree.root)
            .into_iter()
            .filter(|node| node.kind == kind)
            .collect()
    }
    pub fn source_text<'a>(tree: &'a ShaderSyntaxTree, node: &ShaderSyntaxNode) -> &'a str {
        tree.source_text(node)
    }
}

pub use syntax::*;

pub mod preprocessor {
    use super::*;
    use crate::syntax::{ShaderSyntaxTree, ShaderTokenKind};

    #[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
    pub enum PresenceCondition {
        Always,
        Never,
        Defined(String),
        Symbol(String),
        Equals(String, String),
        Not(Box<PresenceCondition>),
        And(Vec<PresenceCondition>),
        Or(Vec<PresenceCondition>),
        UnknownCondition(String),
    }
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub enum ConditionValue {
        ConditionTrue,
        ConditionFalse,
        ConditionUnknown,
    }
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub enum PreprocessorDirectiveKind {
        If,
        IfDef,
        IfNDef,
        Elif,
        Else,
        EndIf,
        Define,
        Undef,
        Include,
        Pragma,
        Error,
        UnknownDirective,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub enum MacroKind {
        ObjectLike,
        FunctionLike { parameters: Vec<String> },
        EnginePredefined,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct MacroDefinition {
        pub name: String,
        pub kind: MacroKind,
        pub replacement: String,
        pub span: TextSpan,
        pub condition: PresenceCondition,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct PreprocessorDirective {
        pub kind: PreprocessorDirectiveKind,
        pub keyword: String,
        pub argument: String,
        pub span: TextSpan,
        pub condition: PresenceCondition,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct PresenceRegion {
        pub span: TextSpan,
        pub condition: PresenceCondition,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct PreprocessorDiagnostic {
        pub code: String,
        pub message: String,
        pub span: TextSpan,
    }
    #[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
    pub struct PreprocessorResult {
        pub directives: Vec<PreprocessorDirective>,
        pub macros: Vec<MacroDefinition>,
        pub regions: Vec<PresenceRegion>,
        pub diagnostics: Vec<PreprocessorDiagnostic>,
    }
    #[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
    pub struct MacroEnvironment {
        pub defined: BTreeSet<String>,
        pub values: BTreeMap<String, String>,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct PlatformVariant {
        pub name: String,
        pub environment: MacroEnvironment,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct VariantCondition {
        pub condition: PresenceCondition,
        pub active_variants: Vec<String>,
        pub unknown_variants: Vec<String>,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct ExpandedFragment {
        pub text: String,
        pub source_span: TextSpan,
        pub expansion_stack: Vec<String>,
    }

    impl PresenceCondition {
        #[must_use]
        pub fn simplify(self) -> Self {
            match self {
                Self::Not(inner) => match inner.simplify() {
                    Self::Always => Self::Never,
                    Self::Never => Self::Always,
                    Self::Not(nested) => *nested,
                    value => Self::Not(Box::new(value)),
                },
                Self::And(items) => {
                    let mut output = Vec::new();
                    for item in items {
                        let item = item.simplify();
                        if item == Self::Never {
                            return Self::Never;
                        }
                        if item != Self::Always && !output.contains(&item) {
                            output.push(item);
                        }
                    }
                    if output.iter().any(|x| {
                        output
                            .iter()
                            .any(|y| matches!(y, Self::Not(inner) if **inner == *x))
                    }) {
                        Self::Never
                    } else if output.len() == 1 {
                        output.remove(0)
                    } else {
                        Self::And(output)
                    }
                }
                Self::Or(items) => {
                    let mut output = Vec::new();
                    for item in items {
                        let item = item.simplify();
                        if item == Self::Always {
                            return Self::Always;
                        }
                        if item != Self::Never && !output.contains(&item) {
                            output.push(item);
                        }
                    }
                    if output.iter().any(|x| {
                        output
                            .iter()
                            .any(|y| matches!(y, Self::Not(inner) if **inner == *x))
                    }) {
                        Self::Always
                    } else if output.len() == 1 {
                        output.remove(0)
                    } else {
                        Self::Or(output)
                    }
                }
                value => value,
            }
        }
    }
    #[must_use]
    pub fn conjunction(left: PresenceCondition, right: PresenceCondition) -> PresenceCondition {
        PresenceCondition::And(vec![left, right]).simplify()
    }
    #[must_use]
    pub fn disjunction(left: PresenceCondition, right: PresenceCondition) -> PresenceCondition {
        PresenceCondition::Or(vec![left, right]).simplify()
    }
    #[must_use]
    pub fn negate(value: PresenceCondition) -> PresenceCondition {
        PresenceCondition::Not(Box::new(value)).simplify()
    }

    #[derive(Clone, Debug)]
    enum ExpressionToken {
        Identifier(String),
        Number(String),
        Not,
        And,
        Or,
        Equals,
        NotEquals,
        Open,
        Close,
        Other(char),
    }
    fn tokenize_expression(text: &str) -> Vec<ExpressionToken> {
        let bytes = text.as_bytes();
        let mut index = 0;
        let mut result = Vec::new();
        while index < bytes.len() {
            if bytes[index].is_ascii_whitespace() {
                index += 1;
                continue;
            }
            if bytes[index].is_ascii_alphabetic() || bytes[index] == b'_' {
                let start = index;
                index += 1;
                while index < bytes.len()
                    && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_')
                {
                    index += 1;
                }
                result.push(ExpressionToken::Identifier(text[start..index].to_owned()));
                continue;
            }
            if bytes[index].is_ascii_digit() {
                let start = index;
                index += 1;
                while index < bytes.len()
                    && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_')
                {
                    index += 1;
                }
                result.push(ExpressionToken::Number(text[start..index].to_owned()));
                continue;
            }
            let pair = if index + 1 < bytes.len() {
                &text[index..index + 2]
            } else {
                ""
            };
            match pair {
                "&&" => {
                    result.push(ExpressionToken::And);
                    index += 2;
                }
                "||" => {
                    result.push(ExpressionToken::Or);
                    index += 2;
                }
                "==" => {
                    result.push(ExpressionToken::Equals);
                    index += 2;
                }
                "!=" => {
                    result.push(ExpressionToken::NotEquals);
                    index += 2;
                }
                _ => {
                    result.push(match bytes[index] {
                        b'!' => ExpressionToken::Not,
                        b'(' => ExpressionToken::Open,
                        b')' => ExpressionToken::Close,
                        other => ExpressionToken::Other(other as char),
                    });
                    index += 1;
                }
            }
        }
        result
    }
    pub fn parse_condition(text: &str) -> PresenceCondition {
        let tokens = tokenize_expression(text);
        let mut position = 0;
        fn primary(
            tokens: &[ExpressionToken],
            position: &mut usize,
            source: &str,
        ) -> PresenceCondition {
            match tokens.get(*position) {
                Some(ExpressionToken::Identifier(name)) if name.eq_ignore_ascii_case("defined") => {
                    *position += 1;
                    if matches!(tokens.get(*position), Some(ExpressionToken::Open)) {
                        *position += 1;
                    }
                    let name = match tokens.get(*position) {
                        Some(ExpressionToken::Identifier(name)) => name.clone(),
                        _ => return PresenceCondition::UnknownCondition(source.to_owned()),
                    };
                    *position += 1;
                    if matches!(tokens.get(*position), Some(ExpressionToken::Close)) {
                        *position += 1;
                    }
                    PresenceCondition::Defined(name)
                }
                Some(ExpressionToken::Identifier(name)) => {
                    *position += 1;
                    PresenceCondition::Symbol(name.clone())
                }
                Some(ExpressionToken::Number(number)) => {
                    *position += 1;
                    match number.as_str() {
                        "0" => PresenceCondition::Never,
                        "1" => PresenceCondition::Always,
                        _ => PresenceCondition::Symbol(number.clone()),
                    }
                }
                Some(ExpressionToken::Open) => {
                    *position += 1;
                    let value = parse_or(tokens, position, source);
                    if matches!(tokens.get(*position), Some(ExpressionToken::Close)) {
                        *position += 1;
                    }
                    value
                }
                Some(_) => {
                    *position += 1;
                    PresenceCondition::UnknownCondition(source.to_owned())
                }
                None => PresenceCondition::UnknownCondition(source.to_owned()),
            }
        }
        fn unary(
            tokens: &[ExpressionToken],
            position: &mut usize,
            source: &str,
        ) -> PresenceCondition {
            if matches!(tokens.get(*position), Some(ExpressionToken::Not)) {
                *position += 1;
                negate(unary(tokens, position, source))
            } else {
                primary(tokens, position, source)
            }
        }
        fn value(condition: &PresenceCondition) -> Option<String> {
            match condition {
                PresenceCondition::Symbol(name) | PresenceCondition::Defined(name) => {
                    Some(name.clone())
                }
                PresenceCondition::Always => Some("1".into()),
                PresenceCondition::Never => Some("0".into()),
                _ => None,
            }
        }
        fn equality(
            tokens: &[ExpressionToken],
            position: &mut usize,
            source: &str,
        ) -> PresenceCondition {
            let left = unary(tokens, position, source);
            match tokens.get(*position) {
                Some(ExpressionToken::Equals) | Some(ExpressionToken::NotEquals) => {
                    let not_equal =
                        matches!(tokens.get(*position), Some(ExpressionToken::NotEquals));
                    *position += 1;
                    let right = unary(tokens, position, source);
                    match (value(&left), value(&right)) {
                        (Some(left), Some(right)) => {
                            let result = PresenceCondition::Equals(left, right);
                            if not_equal { negate(result) } else { result }
                        }
                        _ => PresenceCondition::UnknownCondition(source.to_owned()),
                    }
                }
                _ => left,
            }
        }
        fn parse_and(
            tokens: &[ExpressionToken],
            position: &mut usize,
            source: &str,
        ) -> PresenceCondition {
            let mut value = equality(tokens, position, source);
            while matches!(tokens.get(*position), Some(ExpressionToken::And)) {
                *position += 1;
                value = conjunction(value, equality(tokens, position, source));
            }
            value
        }
        fn parse_or(
            tokens: &[ExpressionToken],
            position: &mut usize,
            source: &str,
        ) -> PresenceCondition {
            let mut value = parse_and(tokens, position, source);
            while matches!(tokens.get(*position), Some(ExpressionToken::Or)) {
                *position += 1;
                value = disjunction(value, parse_and(tokens, position, source));
            }
            value
        }
        if tokens.is_empty() {
            PresenceCondition::UnknownCondition(text.to_owned())
        } else {
            parse_or(&tokens, &mut position, text).simplify()
        }
    }
    fn split_directive(raw: &str) -> (String, String) {
        let body = raw
            .trim_start()
            .trim_start_matches('#')
            .trim_start_matches('@')
            .trim_start();
        let split = body.find(char::is_whitespace).unwrap_or(body.len());
        (
            body[..split].to_ascii_lowercase(),
            body[split..].trim().to_owned(),
        )
    }
    fn directive_kind(keyword: &str) -> PreprocessorDirectiveKind {
        match keyword {
            "if" => PreprocessorDirectiveKind::If,
            "ifdef" => PreprocessorDirectiveKind::IfDef,
            "ifndef" => PreprocessorDirectiveKind::IfNDef,
            "elif" => PreprocessorDirectiveKind::Elif,
            "else" => PreprocessorDirectiveKind::Else,
            "endif" => PreprocessorDirectiveKind::EndIf,
            "define" => PreprocessorDirectiveKind::Define,
            "undef" => PreprocessorDirectiveKind::Undef,
            "include" => PreprocessorDirectiveKind::Include,
            "pragma" => PreprocessorDirectiveKind::Pragma,
            "error" => PreprocessorDirectiveKind::Error,
            _ => PreprocessorDirectiveKind::UnknownDirective,
        }
    }
    fn first_identifier(text: &str) -> Option<(String, usize)> {
        let mut start = None;
        for (index, ch) in text.char_indices() {
            if ch.is_alphabetic() || ch == '_' {
                start = Some(index);
                break;
            }
        }
        let start = start?;
        let mut end = start;
        for (relative, ch) in text[start..].char_indices() {
            if !(ch.is_alphanumeric() || ch == '_') {
                break;
            }
            end = start + relative + ch.len_utf8();
        }
        Some((text[start..end].to_owned(), start))
    }

    pub fn analyze(tree: &ShaderSyntaxTree) -> PreprocessorResult {
        let mut result = PreprocessorResult::default();
        let mut current = PresenceCondition::Always;
        let mut stack: Vec<(PresenceCondition, PresenceCondition)> = Vec::new();
        for token in tree
            .tokens
            .iter()
            .filter(|token| token.kind == ShaderTokenKind::DirectiveLine)
        {
            let (keyword, argument) = split_directive(&token.text);
            let kind = directive_kind(&keyword);
            let condition = match kind {
                PreprocessorDirectiveKind::If => {
                    conjunction(current.clone(), parse_condition(&argument))
                }
                PreprocessorDirectiveKind::IfDef => conjunction(
                    current.clone(),
                    PresenceCondition::Defined(argument.clone()),
                ),
                PreprocessorDirectiveKind::IfNDef => conjunction(
                    current.clone(),
                    negate(PresenceCondition::Defined(argument.clone())),
                ),
                PreprocessorDirectiveKind::Elif => stack.last().map_or_else(
                    || PresenceCondition::UnknownCondition("elif without if".into()),
                    |(parent, taken)| {
                        conjunction(
                            parent.clone(),
                            conjunction(negate(taken.clone()), parse_condition(&argument)),
                        )
                    },
                ),
                PreprocessorDirectiveKind::Else => stack.last().map_or_else(
                    || PresenceCondition::UnknownCondition("else without if".into()),
                    |(parent, taken)| conjunction(parent.clone(), negate(taken.clone())),
                ),
                _ => current.clone(),
            }
            .simplify();
            result.directives.push(PreprocessorDirective {
                kind,
                keyword: keyword.clone(),
                argument: argument.clone(),
                span: token.span,
                condition: condition.clone(),
            });
            match kind {
                PreprocessorDirectiveKind::If
                | PreprocessorDirectiveKind::IfDef
                | PreprocessorDirectiveKind::IfNDef => {
                    let branch = match kind {
                        PreprocessorDirectiveKind::If => parse_condition(&argument),
                        PreprocessorDirectiveKind::IfDef => {
                            PresenceCondition::Defined(argument.clone())
                        }
                        PreprocessorDirectiveKind::IfNDef => {
                            negate(PresenceCondition::Defined(argument.clone()))
                        }
                        _ => PresenceCondition::Always,
                    };
                    stack.push((current.clone(), branch));
                    current = condition;
                }
                PreprocessorDirectiveKind::Elif => {
                    if let Some((parent, taken)) = stack.last_mut() {
                        *taken = disjunction(taken.clone(), parse_condition(&argument));
                        current = condition;
                    } else {
                        result.diagnostics.push(PreprocessorDiagnostic {
                            code: "CWFX103".into(),
                            message: "Unexpected preprocessor elif without a matching if.".into(),
                            span: token.span,
                        });
                    }
                }
                PreprocessorDirectiveKind::Else => {
                    if stack.is_empty() {
                        result.diagnostics.push(PreprocessorDiagnostic {
                            code: "CWFX103".into(),
                            message: "Unexpected preprocessor else without a matching if.".into(),
                            span: token.span,
                        });
                    } else if let Some((parent, taken)) = stack.last() {
                        current = conjunction(parent.clone(), negate(taken.clone()));
                    }
                }
                PreprocessorDirectiveKind::EndIf => {
                    if let Some((parent, _)) = stack.pop() {
                        current = parent;
                    } else {
                        result.diagnostics.push(PreprocessorDiagnostic {
                            code: "CWFX103".into(),
                            message: "Unexpected preprocessor endif without a matching if.".into(),
                            span: token.span,
                        });
                    }
                }
                PreprocessorDirectiveKind::Define => {
                    if let Some((name, offset)) = first_identifier(&argument) {
                        let rest = argument[offset + name.len()..].trim();
                        let (macro_kind, replacement) = if rest.starts_with('(') {
                            let close = rest.find(')').unwrap_or(0);
                            let parameters = if close > 0 {
                                rest[1..close]
                                    .split(',')
                                    .map(str::trim)
                                    .filter(|value| !value.is_empty())
                                    .map(str::to_owned)
                                    .collect()
                            } else {
                                Vec::new()
                            };
                            (
                                MacroKind::FunctionLike { parameters },
                                rest.get(close + 1..).unwrap_or("").trim().to_owned(),
                            )
                        } else {
                            (MacroKind::ObjectLike, rest.to_owned())
                        };
                        result.macros.push(MacroDefinition {
                            name,
                            kind: macro_kind,
                            replacement,
                            span: token.span,
                            condition: current.clone(),
                        });
                    }
                }
                _ => {}
            }
        }
        for node in crate::syntax::descendants(&tree.root) {
            if node.kind != crate::syntax::ShaderNodeKind::PreprocessorDirective
                && node.span.length() > 0
            {
                result.regions.push(PresenceRegion {
                    span: node.span,
                    condition: condition_at(node.span.start_offset, &result),
                });
            }
        }
        result
            .regions
            .sort_by_key(|region| region.span.start_offset);
        result
    }
    pub fn condition_at(offset: usize, result: &PreprocessorResult) -> PresenceCondition {
        result
            .regions
            .iter()
            .find(|region| offset >= region.span.start_offset && offset < region.span.end_offset)
            .map_or(PresenceCondition::Always, |region| region.condition.clone())
    }
    pub fn evaluate(
        environment: &MacroEnvironment,
        condition: &PresenceCondition,
    ) -> ConditionValue {
        match condition.clone().simplify() {
            PresenceCondition::Always => ConditionValue::ConditionTrue,
            PresenceCondition::Never => ConditionValue::ConditionFalse,
            PresenceCondition::Defined(name) => {
                if environment.defined.contains(&name) {
                    ConditionValue::ConditionTrue
                } else {
                    ConditionValue::ConditionFalse
                }
            }
            PresenceCondition::Symbol(name) => match environment.values.get(&name) {
                Some(value) if value == "0" => ConditionValue::ConditionFalse,
                Some(_) => ConditionValue::ConditionTrue,
                None if environment.defined.contains(&name) => ConditionValue::ConditionTrue,
                None => ConditionValue::ConditionFalse,
            },
            PresenceCondition::Equals(left, right) => {
                let left = environment.values.get(&left).cloned().unwrap_or(left);
                let right = environment.values.get(&right).cloned().unwrap_or(right);
                if left == right {
                    ConditionValue::ConditionTrue
                } else {
                    ConditionValue::ConditionFalse
                }
            }
            PresenceCondition::Not(inner) => match evaluate(environment, &inner) {
                ConditionValue::ConditionTrue => ConditionValue::ConditionFalse,
                ConditionValue::ConditionFalse => ConditionValue::ConditionTrue,
                ConditionValue::ConditionUnknown => ConditionValue::ConditionUnknown,
            },
            PresenceCondition::And(items) => {
                let mut unknown = false;
                for item in items {
                    match evaluate(environment, &item) {
                        ConditionValue::ConditionFalse => return ConditionValue::ConditionFalse,
                        ConditionValue::ConditionUnknown => unknown = true,
                        ConditionValue::ConditionTrue => {}
                    }
                }
                if unknown {
                    ConditionValue::ConditionUnknown
                } else {
                    ConditionValue::ConditionTrue
                }
            }
            PresenceCondition::Or(items) => {
                let mut unknown = false;
                for item in items {
                    match evaluate(environment, &item) {
                        ConditionValue::ConditionTrue => return ConditionValue::ConditionTrue,
                        ConditionValue::ConditionUnknown => unknown = true,
                        ConditionValue::ConditionFalse => {}
                    }
                }
                if unknown {
                    ConditionValue::ConditionUnknown
                } else {
                    ConditionValue::ConditionFalse
                }
            }
            PresenceCondition::UnknownCondition(_) => ConditionValue::ConditionUnknown,
        }
    }
    pub fn condition_symbols(condition: &PresenceCondition) -> BTreeSet<String> {
        let mut result = BTreeSet::new();
        fn collect(condition: &PresenceCondition, result: &mut BTreeSet<String>) {
            match condition {
                PresenceCondition::Defined(name) | PresenceCondition::Symbol(name) => {
                    result.insert(name.clone());
                }
                PresenceCondition::Equals(left, right) => {
                    result.insert(left.clone());
                    result.insert(right.clone());
                }
                PresenceCondition::Not(inner) => collect(inner, result),
                PresenceCondition::And(items) | PresenceCondition::Or(items) => {
                    for item in items {
                        collect(item, result);
                    }
                }
                _ => {}
            }
        }
        collect(condition, &mut result);
        result
    }
    pub fn satisfiable(condition: &PresenceCondition) -> ConditionValue {
        let names: Vec<_> = condition_symbols(condition).into_iter().collect();
        if names.len() > MAX_SATISFIABILITY_SYMBOLS {
            return ConditionValue::ConditionUnknown;
        }
        for mask in 0..(1usize << names.len()) {
            let mut environment = MacroEnvironment::default();
            for (index, name) in names.iter().enumerate() {
                if mask & (1usize << index) != 0 {
                    environment.defined.insert(name.clone());
                }
            }
            if evaluate(&environment, condition) == ConditionValue::ConditionTrue {
                return ConditionValue::ConditionTrue;
            }
        }
        ConditionValue::ConditionFalse
    }
    pub fn default_platform_variants() -> Vec<PlatformVariant> {
        vec![
            PlatformVariant {
                name: "directx11".into(),
                environment: MacroEnvironment {
                    defined: ["PDX_DIRECTX_11", "PDX_WINDOWS"]
                        .into_iter()
                        .map(str::to_owned)
                        .collect(),
                    values: BTreeMap::new(),
                },
            },
            PlatformVariant {
                name: "opengl".into(),
                environment: MacroEnvironment {
                    defined: ["PDX_OPENGL"].into_iter().map(str::to_owned).collect(),
                    values: BTreeMap::new(),
                },
            },
            PlatformVariant {
                name: "pssl".into(),
                environment: MacroEnvironment {
                    defined: ["PDX_PSSL"].into_iter().map(str::to_owned).collect(),
                    values: BTreeMap::new(),
                },
            },
        ]
    }
    pub fn compare_variants(
        variants: &[PlatformVariant],
        conditions: &[PresenceCondition],
    ) -> Vec<VariantCondition> {
        let mut seen = HashSet::new();
        conditions
            .iter()
            .filter(|condition| seen.insert(format!("{condition:?}")))
            .map(|condition| {
                let mut active = Vec::new();
                let mut unknown = Vec::new();
                for variant in variants {
                    match evaluate(&variant.environment, condition) {
                        ConditionValue::ConditionTrue => active.push(variant.name.clone()),
                        ConditionValue::ConditionUnknown => unknown.push(variant.name.clone()),
                        ConditionValue::ConditionFalse => {}
                    }
                }
                VariantCondition {
                    condition: condition.clone(),
                    active_variants: active,
                    unknown_variants: unknown,
                }
            })
            .collect()
    }
    pub fn expand_object_macro(
        environment: &MacroEnvironment,
        macros: &[MacroDefinition],
        name: &str,
    ) -> ExpandedFragment {
        let map: HashMap<_, _> = macros
            .iter()
            .filter(|macro_def| {
                matches!(macro_def.kind, MacroKind::ObjectLike)
                    && evaluate(environment, &macro_def.condition) != ConditionValue::ConditionFalse
            })
            .map(|macro_def| (macro_def.name.clone(), macro_def))
            .collect();
        fn expand(
            depth: usize,
            stack: &mut Vec<String>,
            name: &str,
            map: &HashMap<String, &MacroDefinition>,
        ) -> ExpandedFragment {
            if depth >= MAX_MACRO_EXPANSION_DEPTH || stack.iter().any(|item| item == name) {
                let mut stack = stack.clone();
                stack.push(name.into());
                return ExpandedFragment {
                    text: name.into(),
                    source_span: TextSpan::default(),
                    expansion_stack: stack,
                };
            }
            let Some(macro_def) = map.get(name) else {
                return ExpandedFragment {
                    text: name.into(),
                    source_span: TextSpan::default(),
                    expansion_stack: stack.clone(),
                };
            };
            let replacement = macro_def.replacement.trim();
            if !replacement.is_empty()
                && replacement
                    .chars()
                    .all(|character| character.is_alphanumeric() || character == '_')
            {
                stack.push(name.into());
                let result = expand(depth + 1, stack, replacement, map);
                stack.pop();
                result
            } else {
                let mut stack = stack.clone();
                stack.push(name.into());
                ExpandedFragment {
                    text: macro_def.replacement.clone(),
                    source_span: macro_def.span,
                    expansion_stack: stack,
                }
            }
        }
        expand(0, &mut Vec::new(), name, &map)
    }
}

pub use preprocessor::*;

pub mod hlsl {
    use super::*;
    use crate::preprocessor::{PreprocessorResult, PresenceCondition, condition_at};
    use crate::syntax::{ShaderSyntaxTree, ShaderToken, ShaderTokenKind};
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
    pub enum ShaderStage {
        VertexStage,
        PixelStage,
        GeometryStage,
        UnknownStage,
    }
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
    pub enum ScalarKind {
        Bool,
        Int,
        UInt,
        Half,
        Float,
        Double,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
    pub enum HlslType {
        VoidType,
        ScalarType(ScalarKind),
        VectorType(ScalarKind, usize),
        MatrixType(ScalarKind, usize, usize),
        ArrayType(Box<HlslType>, Option<usize>),
        StructType(String),
        TextureType(String),
        SamplerType(String),
        BufferType(String, Option<Box<HlslType>>),
        UnknownType(String),
        ErrorType,
    }
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
    pub enum ParameterDirection {
        In,
        Out,
        InOut,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct HlslParameter {
        pub name: String,
        pub parameter_type: HlslType,
        pub direction: ParameterDirection,
        pub semantic: Option<String>,
        pub span: TextSpan,
    }
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
    pub enum HlslSymbolKind {
        TypeSymbol,
        StructSymbol,
        FieldSymbol,
        ConstantBufferSymbol,
        ResourceSymbol,
        SamplerSymbol,
        FunctionSymbol,
        ParameterSymbol,
        GlobalVariableSymbol,
        LocalVariableSymbol,
        MacroSymbol,
    }
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
    pub enum HlslScopeKind {
        FileScope,
        StructScope,
        FunctionScope,
        LexicalScope,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct ResourceBinding {
        pub register_class: String,
        pub register_index: i32,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct HlslSymbol {
        pub id: String,
        pub name: String,
        pub kind: HlslSymbolKind,
        pub symbol_type: HlslType,
        pub span: TextSpan,
        pub selection_span: TextSpan,
        pub scope_id: usize,
        pub condition: PresenceCondition,
        pub stage: ShaderStage,
        pub parameters: Vec<HlslParameter>,
        pub semantic: Option<String>,
        pub binding: Option<ResourceBinding>,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct HlslScope {
        pub id: usize,
        pub kind: HlslScopeKind,
        pub parent_id: Option<usize>,
        pub span: TextSpan,
    }
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
    pub enum HlslReferenceKind {
        ReadReference,
        WriteReference,
        CallReference,
        TypeReference,
        MemberReference,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct HlslReference {
        pub name: String,
        pub kind: HlslReferenceKind,
        pub span: TextSpan,
        pub scope_id: usize,
        pub condition: PresenceCondition,
        pub stage: ShaderStage,
        pub candidate_ids: Vec<String>,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct HlslDiagnostic {
        pub code: String,
        pub message: String,
        pub span: TextSpan,
        pub condition: PresenceCondition,
        pub stage: ShaderStage,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct HlslCallEdge {
        pub caller_id: Option<String>,
        pub callee_ids: Vec<String>,
        pub span: TextSpan,
        pub condition: PresenceCondition,
    }
    #[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
    pub struct HlslAnalysis {
        pub symbols: Vec<HlslSymbol>,
        pub references: Vec<HlslReference>,
        pub scopes: Vec<HlslScope>,
        pub diagnostics: Vec<HlslDiagnostic>,
        pub calls: Vec<HlslCallEdge>,
    }
    pub fn parse_type_name(name: &str) -> HlslType {
        let lower = name.trim().to_ascii_lowercase();
        let scalar = match lower.as_str() {
            "bool" => Some(ScalarKind::Bool),
            "int" => Some(ScalarKind::Int),
            "uint" => Some(ScalarKind::UInt),
            "half" => Some(ScalarKind::Half),
            "float" => Some(ScalarKind::Float),
            "double" => Some(ScalarKind::Double),
            _ => None,
        };
        if let Some(kind) = scalar {
            return HlslType::ScalarType(kind);
        }
        for (prefix, kind) in [
            ("float", ScalarKind::Float),
            ("half", ScalarKind::Half),
            ("int", ScalarKind::Int),
            ("uint", ScalarKind::UInt),
            ("double", ScalarKind::Double),
        ] {
            if let Some(width) = lower
                .strip_prefix(prefix)
                .and_then(|x| x.parse::<usize>().ok())
            {
                if (2..=4).contains(&width) {
                    return HlslType::VectorType(kind, width);
                }
            }
        }
        if lower == "void" {
            HlslType::VoidType
        } else if lower.starts_with("texture") {
            HlslType::TextureType(name.trim().into())
        } else if lower.starts_with("sampler") {
            HlslType::SamplerType(name.trim().into())
        } else if lower.starts_with("buffer") {
            HlslType::BufferType(name.trim().into(), None)
        } else {
            HlslType::StructType(name.trim().into())
        }
    }
    fn stable_id(file: &str, kind: HlslSymbolKind, name: &str, offset: usize) -> String {
        format!(
            "shader:{}:{kind:?}:{name}:{offset}",
            file.replace('\\', "/").to_ascii_lowercase()
        )
    }
    fn significant(tree: &ShaderSyntaxTree) -> Vec<ShaderToken> {
        tree.tokens
            .iter()
            .filter(|token| !token.is_trivia() && token.kind != ShaderTokenKind::EndOfFile)
            .cloned()
            .collect()
    }
    fn matching(
        tokens: &[ShaderToken],
        open: ShaderTokenKind,
        close: ShaderTokenKind,
        start: usize,
    ) -> Option<usize> {
        let mut depth = 0;
        for i in start..tokens.len() {
            if tokens[i].kind == open {
                depth += 1;
            } else if tokens[i].kind == close {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
        }
        None
    }
    fn stage_at(tree: &ShaderSyntaxTree, offset: usize) -> ShaderStage {
        for node in crate::syntax::nodes_of_kind(tree, crate::syntax::ShaderNodeKind::VertexShader)
        {
            if offset >= node.span.start_offset && offset < node.span.end_offset {
                return ShaderStage::VertexStage;
            }
        }
        for node in crate::syntax::nodes_of_kind(tree, crate::syntax::ShaderNodeKind::PixelShader) {
            if offset >= node.span.start_offset && offset < node.span.end_offset {
                return ShaderStage::PixelStage;
            }
        }
        for node in
            crate::syntax::nodes_of_kind(tree, crate::syntax::ShaderNodeKind::GeometryShader)
        {
            if offset >= node.span.start_offset && offset < node.span.end_offset {
                return ShaderStage::GeometryStage;
            }
        }
        ShaderStage::UnknownStage
    }
    fn parse_parameters(tokens: &[ShaderToken], open: usize, close: usize) -> Vec<HlslParameter> {
        let mut result = Vec::new();
        let mut start = open + 1;
        let mut depth = 0usize;
        for i in open + 1..=close {
            let boundary = i == close || (tokens[i].kind == ShaderTokenKind::Comma && depth == 0);
            if boundary {
                let segment = &tokens[start..i];
                let ids: Vec<_> = segment
                    .iter()
                    .filter(|token| token.kind == ShaderTokenKind::Identifier)
                    .collect();
                if ids.len() >= 2 {
                    let direction = match ids[0].text.to_ascii_lowercase().as_str() {
                        "out" => ParameterDirection::Out,
                        "inout" => ParameterDirection::InOut,
                        _ => ParameterDirection::In,
                    };
                    let type_index = if matches!(
                        ids[0].text.to_ascii_lowercase().as_str(),
                        "in" | "out" | "inout"
                    ) {
                        1
                    } else {
                        0
                    };
                    if type_index + 1 < ids.len() {
                        result.push(HlslParameter {
                            name: ids[type_index + 1].text.clone(),
                            parameter_type: parse_type_name(&ids[type_index].text),
                            direction,
                            semantic: segment
                                .windows(2)
                                .find(|window| window[0].kind == ShaderTokenKind::Colon)
                                .map(|window| window[1].text.clone()),
                            span: TextSpan::new(
                                segment.first().map_or(0, |token| token.span.start_offset),
                                segment.last().map_or(0, |token| token.span.end_offset),
                            ),
                        });
                    }
                }
                start = i + 1;
            } else if matches!(
                tokens[i].kind,
                ShaderTokenKind::OpenParen
                    | ShaderTokenKind::OpenBracket
                    | ShaderTokenKind::OpenBrace
            ) {
                depth += 1;
            } else if matches!(
                tokens[i].kind,
                ShaderTokenKind::CloseParen
                    | ShaderTokenKind::CloseBracket
                    | ShaderTokenKind::CloseBrace
            ) {
                depth = depth.saturating_sub(1);
            }
        }
        result
    }
    pub fn resolve_overload(
        argument_types: &[HlslType],
        candidates: &[HlslSymbol],
    ) -> Vec<HlslSymbol> {
        let mut scored: Vec<_> = candidates
            .iter()
            .cloned()
            .filter_map(|symbol| {
                if symbol.parameters.len() != argument_types.len() {
                    return None;
                }
                let mut score = 0;
                for (argument, parameter) in argument_types.iter().zip(&symbol.parameters) {
                    if argument == &parameter.parameter_type {
                        score += 4;
                    } else if matches!(argument, HlslType::UnknownType(_))
                        || matches!(parameter.parameter_type, HlslType::UnknownType(_))
                    {
                        score += 1;
                    } else {
                        return None;
                    }
                }
                Some((score, symbol))
            })
            .collect();
        scored.sort_by(|left, right| right.0.cmp(&left.0).then(left.1.id.cmp(&right.1.id)));
        let best = scored.first().map(|item| item.0);
        scored
            .into_iter()
            .filter(|item| Some(item.0) == best)
            .take(1)
            .map(|item| item.1)
            .collect()
    }
    pub fn analyze(tree: &ShaderSyntaxTree, preprocessor: &PreprocessorResult) -> HlslAnalysis {
        let mut result = HlslAnalysis {
            scopes: vec![HlslScope {
                id: 0,
                kind: HlslScopeKind::FileScope,
                parent_id: None,
                span: tree.root.span,
            }],
            ..HlslAnalysis::default()
        };
        let tokens = significant(tree);
        let mut declarations = HashSet::new();
        let mut index = 0;
        while index < tokens.len() {
            if tokens[index].kind == ShaderTokenKind::Identifier
                && tokens[index].text.eq_ignore_ascii_case("struct")
                && index + 2 < tokens.len()
                && tokens[index + 1].kind == ShaderTokenKind::Identifier
                && tokens[index + 2].kind == ShaderTokenKind::OpenBrace
            {
                if let Some(close) = matching(
                    &tokens,
                    ShaderTokenKind::OpenBrace,
                    ShaderTokenKind::CloseBrace,
                    index + 2,
                ) {
                    let name = &tokens[index + 1];
                    result.symbols.push(HlslSymbol {
                        id: stable_id(
                            &tree.filepath,
                            HlslSymbolKind::StructSymbol,
                            &name.text,
                            name.span.start_offset,
                        ),
                        name: name.text.clone(),
                        kind: HlslSymbolKind::StructSymbol,
                        symbol_type: HlslType::StructType(name.text.clone()),
                        span: TextSpan::new(
                            tokens[index].span.start_offset,
                            tokens[close].span.end_offset,
                        ),
                        selection_span: name.span,
                        scope_id: 0,
                        condition: condition_at(name.span.start_offset, preprocessor),
                        stage: stage_at(tree, name.span.start_offset),
                        parameters: Vec::new(),
                        semantic: None,
                        binding: None,
                    });
                    declarations.insert((name.span.start_offset, name.span.end_offset));
                    let scope_id = result.scopes.len();
                    result.scopes.push(HlslScope {
                        id: scope_id,
                        kind: HlslScopeKind::StructScope,
                        parent_id: Some(0),
                        span: TextSpan::new(
                            tokens[index].span.start_offset,
                            tokens[close].span.end_offset,
                        ),
                    });
                    index = close + 1;
                    continue;
                }
            }
            if index + 2 < tokens.len()
                && tokens[index].kind == ShaderTokenKind::Identifier
                && tokens[index + 1].kind == ShaderTokenKind::Identifier
                && tokens[index + 2].kind == ShaderTokenKind::OpenParen
            {
                let return_type = parse_type_name(&tokens[index].text);
                let name = &tokens[index + 1];
                if let Some(close) = matching(
                    &tokens,
                    ShaderTokenKind::OpenParen,
                    ShaderTokenKind::CloseParen,
                    index + 2,
                ) {
                    let body = if close + 1 < tokens.len()
                        && tokens[close + 1].kind == ShaderTokenKind::OpenBrace
                    {
                        matching(
                            &tokens,
                            ShaderTokenKind::OpenBrace,
                            ShaderTokenKind::CloseBrace,
                            close + 1,
                        )
                        .unwrap_or(close + 1)
                    } else {
                        close
                    };
                    let parameters = parse_parameters(&tokens, index + 2, close);
                    let id = stable_id(
                        &tree.filepath,
                        HlslSymbolKind::FunctionSymbol,
                        &name.text,
                        name.span.start_offset,
                    );
                    result.symbols.push(HlslSymbol {
                        id: id.clone(),
                        name: name.text.clone(),
                        kind: HlslSymbolKind::FunctionSymbol,
                        symbol_type: return_type,
                        span: TextSpan::new(
                            tokens[index].span.start_offset,
                            tokens[body].span.end_offset,
                        ),
                        selection_span: name.span,
                        scope_id: 0,
                        condition: condition_at(name.span.start_offset, preprocessor),
                        stage: stage_at(tree, name.span.start_offset),
                        parameters: parameters.clone(),
                        semantic: None,
                        binding: None,
                    });
                    declarations.insert((name.span.start_offset, name.span.end_offset));
                    for parameter in parameters {
                        declarations
                            .insert((parameter.span.start_offset, parameter.span.end_offset));
                        result.symbols.push(HlslSymbol {
                            id: stable_id(
                                &tree.filepath,
                                HlslSymbolKind::ParameterSymbol,
                                &parameter.name,
                                parameter.span.start_offset,
                            ),
                            name: parameter.name.clone(),
                            kind: HlslSymbolKind::ParameterSymbol,
                            symbol_type: parameter.parameter_type.clone(),
                            span: parameter.span,
                            selection_span: parameter.span,
                            scope_id: 0,
                            condition: condition_at(parameter.span.start_offset, preprocessor),
                            stage: stage_at(tree, parameter.span.start_offset),
                            parameters: Vec::new(),
                            semantic: parameter.semantic,
                            binding: None,
                        });
                    }
                    index = body.saturating_add(1);
                    continue;
                }
            }
            if index + 1 < tokens.len()
                && tokens[index].kind == ShaderTokenKind::Identifier
                && tokens[index + 1].kind == ShaderTokenKind::Identifier
                && !tokens
                    .get(index + 2)
                    .is_some_and(|token| token.kind == ShaderTokenKind::OpenParen)
            {
                let name = &tokens[index + 1];
                let kind = if tokens[index]
                    .text
                    .to_ascii_lowercase()
                    .starts_with("sampler")
                {
                    HlslSymbolKind::SamplerSymbol
                } else if tokens[index]
                    .text
                    .to_ascii_lowercase()
                    .starts_with("texture")
                {
                    HlslSymbolKind::ResourceSymbol
                } else if index > 0 {
                    HlslSymbolKind::LocalVariableSymbol
                } else {
                    HlslSymbolKind::GlobalVariableSymbol
                };
                result.symbols.push(HlslSymbol {
                    id: stable_id(&tree.filepath, kind, &name.text, name.span.start_offset),
                    name: name.text.clone(),
                    kind,
                    symbol_type: parse_type_name(&tokens[index].text),
                    span: TextSpan::new(tokens[index].span.start_offset, name.span.end_offset),
                    selection_span: name.span,
                    scope_id: 0,
                    condition: condition_at(name.span.start_offset, preprocessor),
                    stage: stage_at(tree, name.span.start_offset),
                    parameters: Vec::new(),
                    semantic: None,
                    binding: None,
                });
                declarations.insert((name.span.start_offset, name.span.end_offset));
            }
            index += 1;
        }
        let keywords = [
            "struct", "return", "if", "else", "for", "while", "float", "float2", "float3",
            "float4", "int", "uint", "bool", "void", "const", "static", "in", "out", "inout",
            "true", "false", "register",
        ];
        for (position, token) in tokens.iter().enumerate() {
            if token.kind != ShaderTokenKind::Identifier
                || declarations.contains(&(token.span.start_offset, token.span.end_offset))
                || keywords
                    .iter()
                    .any(|keyword| keyword.eq_ignore_ascii_case(&token.text))
            {
                continue;
            }
            let previous = position.checked_sub(1).and_then(|x| tokens.get(x));
            let next = tokens.get(position + 1);
            let kind = if previous.is_some_and(|item| item.kind == ShaderTokenKind::Dot) {
                HlslReferenceKind::MemberReference
            } else if next.is_some_and(|item| item.kind == ShaderTokenKind::OpenParen) {
                HlslReferenceKind::CallReference
            } else if next.is_some_and(|item| item.kind == ShaderTokenKind::Equals) {
                HlslReferenceKind::WriteReference
            } else if next.is_some_and(|item| item.kind == ShaderTokenKind::Identifier) {
                HlslReferenceKind::TypeReference
            } else {
                HlslReferenceKind::ReadReference
            };
            let candidates: Vec<_> = result
                .symbols
                .iter()
                .filter(|symbol| symbol.name.eq_ignore_ascii_case(&token.text))
                .map(|symbol| symbol.id.clone())
                .collect();
            let reference = HlslReference {
                name: token.text.clone(),
                kind,
                span: token.span,
                scope_id: 0,
                condition: condition_at(token.span.start_offset, preprocessor),
                stage: stage_at(tree, token.span.start_offset),
                candidate_ids: candidates.clone(),
            };
            if kind == HlslReferenceKind::CallReference {
                result.calls.push(HlslCallEdge {
                    caller_id: None,
                    callee_ids: candidates,
                    span: token.span,
                    condition: reference.condition.clone(),
                });
            }
            result.references.push(reference);
        }
        result
    }
    pub fn analyze_text(
        filepath: &str,
        text: &str,
    ) -> (ShaderSyntaxTree, PreprocessorResult, HlslAnalysis) {
        let tree = crate::syntax::parse(filepath, text);
        let preprocessor = crate::preprocessor::analyze(&tree);
        let hlsl = analyze(&tree, &preprocessor);
        (tree, preprocessor, hlsl)
    }
}

pub use hlsl::*;

pub mod project {
    use super::*;
    use crate::preprocessor::{
        ConditionValue, MacroEnvironment, PresenceCondition, condition_at, evaluate, satisfiable,
    };
    #[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
    pub enum ShaderOrigin {
        CurrentDocument,
        Workspace,
        Dependency(usize),
        Vanilla,
    }
    pub fn origin_rank(origin: &ShaderOrigin) -> usize {
        match origin {
            ShaderOrigin::CurrentDocument => 0,
            ShaderOrigin::Workspace => 1,
            ShaderOrigin::Dependency(_) => 2,
            ShaderOrigin::Vanilla => 3,
        }
    }
    pub fn dependency_order(origin: &ShaderOrigin) -> usize {
        match origin {
            ShaderOrigin::Dependency(value) => *value,
            _ => 0,
        }
    }
    pub fn canonicalize_path(path: &str) -> String {
        let value = PathBuf::from(path);
        let value = std::fs::canonicalize(&value)
            .unwrap_or(value)
            .to_string_lossy()
            .replace('\\', "/")
            .trim_end_matches('/')
            .to_owned();
        if cfg!(windows) {
            value.to_ascii_lowercase()
        } else {
            value
        }
    }
    pub fn normalize_logical_path(path: &str) -> String {
        let value = path.replace('\\', "/").trim_start_matches('/').to_owned();
        if cfg!(windows) {
            value.to_ascii_lowercase()
        } else {
            value
        }
    }
    pub fn same_file_path(left: &str, right: &str) -> bool {
        canonicalize_path(left) == canonicalize_path(right)
    }
    pub fn is_shader_file(path: &str) -> bool {
        Path::new(path)
            .extension()
            .and_then(|x| x.to_str())
            .is_some_and(|x| x.eq_ignore_ascii_case("shader") || x.eq_ignore_ascii_case("fxh"))
    }
    pub fn pos_from_offset(text: &str, offset: usize) -> (usize, usize) {
        let value = &text[..offset.min(text.len())];
        let line = value.bytes().filter(|byte| *byte == b'\n').count() + 1;
        let column = value.rsplit_once('\n').map_or(value.len(), |(_, rest)| {
            rest.trim_end_matches('\r').encode_utf16().count()
        });
        (line, column)
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct ShaderSnapshot {
        pub canonical_path: String,
        pub display_path: String,
        pub logical_path: String,
        pub origin: ShaderOrigin,
        pub text: String,
        pub content_hash: String,
    }
    pub fn content_hash_for_text(text: &str) -> String {
        let mut hash = 14695981039346656037_u64;
        for byte in text.as_bytes() {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(1099511628211);
        }
        format!("{hash:016x}")
    }
    pub fn create_snapshot(
        origin: ShaderOrigin,
        filepath: &str,
        logicalpath: &str,
        text: &str,
    ) -> ShaderSnapshot {
        ShaderSnapshot {
            canonical_path: canonicalize_path(filepath),
            display_path: filepath.into(),
            logical_path: if logicalpath.trim().is_empty() {
                filepath.into()
            } else {
                logicalpath.into()
            },
            origin,
            text: text.into(),
            content_hash: content_hash_for_text(text),
        }
    }
    pub fn sort_key(snapshot: &ShaderSnapshot) -> (usize, usize, String) {
        (
            origin_rank(&snapshot.origin),
            dependency_order(&snapshot.origin),
            snapshot.canonical_path.clone(),
        )
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct ShaderSemanticSnapshot {
        pub syntax: crate::syntax::ShaderSyntaxTree,
        pub preprocessor: crate::preprocessor::PreprocessorResult,
        pub hlsl: crate::hlsl::HlslAnalysis,
    }
    pub fn semantic_snapshot(snapshot: &ShaderSnapshot) -> ShaderSemanticSnapshot {
        let (syntax, preprocessor, hlsl) =
            crate::hlsl::analyze_text(&snapshot.display_path, &snapshot.text);
        ShaderSemanticSnapshot {
            syntax,
            preprocessor,
            hlsl,
        }
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct IncludeEntry {
        pub target: String,
        pub start: usize,
        pub length: usize,
        pub condition: PresenceCondition,
    }
    fn include_target(value: &str) -> Option<String> {
        let value = value.trim();
        if value.len() >= 2
            && ((value.starts_with('"') && value.ends_with('"'))
                || (value.starts_with('<') && value.ends_with('>')))
        {
            Some(value[1..value.len() - 1].into())
        } else {
            None
        }
    }
    pub fn extract_includes(snapshot: &ShaderSnapshot) -> Vec<IncludeEntry> {
        let semantic = semantic_snapshot(snapshot);
        let mut result = Vec::new();
        for node in crate::syntax::nodes_of_kind(
            &semantic.syntax,
            crate::syntax::ShaderNodeKind::IncludeFile,
        ) {
            if let (Some(target), Some(span)) = (&node.name, node.name_span) {
                result.push(IncludeEntry {
                    target: target.clone(),
                    start: span.start_offset + usize::from(span.length() >= 2),
                    length: span.length().saturating_sub(2),
                    condition: condition_at(span.start_offset, &semantic.preprocessor),
                });
            }
        }
        for directive in &semantic.preprocessor.directives {
            if directive.kind == crate::preprocessor::PreprocessorDirectiveKind::Include {
                if let Some(target) = include_target(&directive.argument) {
                    let start = directive.span.start_offset
                        + slice_text(&snapshot.text, directive.span)
                            .find(&target)
                            .unwrap_or(0);
                    result.push(IncludeEntry {
                        target: target.clone(),
                        start,
                        length: target.len(),
                        condition: directive.condition.clone(),
                    });
                }
            }
        }
        result.sort_by_key(|entry| entry.start);
        result.dedup_by(|left, right| left.start == right.start && left.target == right.target);
        result
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub enum IncludeResolution {
        Resolved(Vec<ShaderSnapshot>),
        Ambiguous(Vec<ShaderSnapshot>),
        Missing,
    }
    pub fn resolve_include(
        snapshots: &[ShaderSnapshot],
        from: &ShaderSnapshot,
        target: &str,
    ) -> IncludeResolution {
        let finish = |mut values: Vec<ShaderSnapshot>| {
            values.sort_by_key(sort_key);
            values.dedup_by(|left, right| left.canonical_path == right.canonical_path);
            if values.is_empty() {
                IncludeResolution::Missing
            } else {
                IncludeResolution::Resolved(values)
            }
        };
        if Path::new(target).is_absolute() {
            return finish(
                snapshots
                    .iter()
                    .filter(|snapshot| snapshot.canonical_path == canonicalize_path(target))
                    .cloned()
                    .collect(),
            );
        }
        let directory = Path::new(&from.display_path)
            .parent()
            .unwrap_or(Path::new(""));
        let relative = canonicalize_path(&directory.join(target).to_string_lossy());
        let local: Vec<_> = snapshots
            .iter()
            .filter(|snapshot| snapshot.canonical_path == relative)
            .cloned()
            .collect();
        if !local.is_empty() {
            return finish(local);
        }
        let wanted = normalize_logical_path(target);
        let values: Vec<_> = snapshots
            .iter()
            .filter(|snapshot| {
                let path = normalize_logical_path(&snapshot.logical_path);
                path == wanted || path.ends_with(&format!("/{wanted}"))
            })
            .cloned()
            .collect();
        let logicals: HashSet<_> = values
            .iter()
            .map(|snapshot| normalize_logical_path(&snapshot.logical_path))
            .collect();
        if logicals.len() > 1 {
            let mut values = values;
            values.sort_by_key(sort_key);
            IncludeResolution::Ambiguous(values)
        } else {
            finish(values)
        }
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub enum IncludeProblem {
        MissingInclude {
            including_path: String,
            target: String,
            start: usize,
            length: usize,
        },
        AmbiguousInclude {
            including_path: String,
            target: String,
            start: usize,
            length: usize,
            candidates: Vec<String>,
        },
        CyclicInclude {
            including_path: String,
            target: String,
            start: usize,
            length: usize,
            cycle_path: Vec<String>,
        },
        IncludeBudgetExceeded {
            including_path: String,
            target: String,
            start: usize,
            length: usize,
            budget: String,
            limit: usize,
        },
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct IncludeGraphEdge {
        pub including_path: String,
        pub target: String,
        pub resolved_path: Option<String>,
        pub condition: PresenceCondition,
        pub start: usize,
        pub length: usize,
    }
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    pub struct CompileUnit {
        pub root: ShaderSnapshot,
        pub members: Vec<ShaderSnapshot>,
        pub effective: Vec<ShaderSnapshot>,
        pub problems: Vec<IncludeProblem>,
        pub edges: Vec<IncludeGraphEdge>,
    }
    pub fn build_compile_unit(snapshots: &[ShaderSnapshot], root: &ShaderSnapshot) -> CompileUnit {
        build_compile_unit_where(snapshots, root, |condition| {
            satisfiable(condition) != ConditionValue::ConditionFalse
        })
    }
    pub fn build_compile_unit_for_environment(
        environment: &MacroEnvironment,
        snapshots: &[ShaderSnapshot],
        root: &ShaderSnapshot,
    ) -> CompileUnit {
        build_compile_unit_where(snapshots, root, |condition| {
            evaluate(environment, condition) != ConditionValue::ConditionFalse
        })
    }
    fn build_compile_unit_where<F: Fn(&PresenceCondition) -> bool>(
        snapshots: &[ShaderSnapshot],
        root: &ShaderSnapshot,
        include: F,
    ) -> CompileUnit {
        let mut members = Vec::new();
        let mut visited = HashSet::new();
        let mut problems = Vec::new();
        let mut edges = Vec::new();
        fn expand<F: Fn(&PresenceCondition) -> bool>(
            snapshots: &[ShaderSnapshot],
            snapshot: &ShaderSnapshot,
            chain: &[String],
            members: &mut Vec<ShaderSnapshot>,
            visited: &mut HashSet<String>,
            problems: &mut Vec<IncludeProblem>,
            edges: &mut Vec<IncludeGraphEdge>,
            include: &F,
        ) {
            let mut chain = chain.to_vec();
            chain.push(snapshot.canonical_path.clone());
            for entry in extract_includes(snapshot)
                .into_iter()
                .filter(|entry| include(&entry.condition))
            {
                match resolve_include(snapshots, snapshot, &entry.target) {
                    IncludeResolution::Resolved(values) => {
                        let best = values.first().cloned();
                        let Some(best) = best else {
                            continue;
                        };
                        edges.push(IncludeGraphEdge {
                            including_path: snapshot.display_path.clone(),
                            target: entry.target.clone(),
                            resolved_path: Some(best.display_path.clone()),
                            condition: entry.condition.clone(),
                            start: entry.start,
                            length: entry.length,
                        });
                        if chain.contains(&best.canonical_path) {
                            problems.push(IncludeProblem::CyclicInclude {
                                including_path: snapshot.display_path.clone(),
                                target: entry.target,
                                start: entry.start,
                                length: entry.length,
                                cycle_path: chain
                                    .iter()
                                    .cloned()
                                    .chain([best.display_path.clone()])
                                    .collect(),
                            });
                            continue;
                        }
                        if members.len() >= MAX_COMPILE_UNIT_MEMBERS {
                            problems.push(IncludeProblem::IncludeBudgetExceeded {
                                including_path: snapshot.display_path.clone(),
                                target: entry.target,
                                start: entry.start,
                                length: entry.length,
                                budget: "members".into(),
                                limit: MAX_COMPILE_UNIT_MEMBERS,
                            });
                            continue;
                        }
                        if visited.insert(best.canonical_path.clone()) {
                            members.push(best.clone());
                        }
                        if chain.len() < MAX_INCLUDE_DEPTH {
                            expand(
                                snapshots, &best, &chain, members, visited, problems, edges,
                                include,
                            );
                        } else {
                            problems.push(IncludeProblem::IncludeBudgetExceeded {
                                including_path: snapshot.display_path.clone(),
                                target: entry.target,
                                start: entry.start,
                                length: entry.length,
                                budget: "depth".into(),
                                limit: MAX_INCLUDE_DEPTH,
                            });
                        }
                    }
                    IncludeResolution::Ambiguous(values) => {
                        edges.push(IncludeGraphEdge {
                            including_path: snapshot.display_path.clone(),
                            target: entry.target.clone(),
                            resolved_path: None,
                            condition: entry.condition.clone(),
                            start: entry.start,
                            length: entry.length,
                        });
                        problems.push(IncludeProblem::AmbiguousInclude {
                            including_path: snapshot.display_path.clone(),
                            target: entry.target,
                            start: entry.start,
                            length: entry.length,
                            candidates: values
                                .into_iter()
                                .map(|value| value.display_path)
                                .collect(),
                        });
                    }
                    IncludeResolution::Missing => {
                        edges.push(IncludeGraphEdge {
                            including_path: snapshot.display_path.clone(),
                            target: entry.target.clone(),
                            resolved_path: None,
                            condition: entry.condition.clone(),
                            start: entry.start,
                            length: entry.length,
                        });
                        problems.push(IncludeProblem::MissingInclude {
                            including_path: snapshot.display_path.clone(),
                            target: entry.target,
                            start: entry.start,
                            length: entry.length,
                        });
                    }
                }
            }
        }
        if visited.insert(root.canonical_path.clone()) {
            members.push(root.clone());
            expand(
                snapshots,
                root,
                &[],
                &mut members,
                &mut visited,
                &mut problems,
                &mut edges,
                &include,
            );
        }
        let mut groups: BTreeMap<String, Vec<ShaderSnapshot>> = BTreeMap::new();
        for snapshot in &members {
            groups
                .entry(normalize_logical_path(&snapshot.logical_path))
                .or_default()
                .push(snapshot.clone());
        }
        let mut effective: Vec<_> = groups
            .into_values()
            .filter_map(|mut values| {
                values.sort_by_key(sort_key);
                values.into_iter().next()
            })
            .collect();
        effective.sort_by_key(sort_key);
        CompileUnit {
            root: root.clone(),
            members,
            effective,
            problems,
            edges,
        }
    }
    pub fn reverse_include_map(snapshots: &[ShaderSnapshot]) -> BTreeMap<String, Vec<String>> {
        let mut result = BTreeMap::new();
        for snapshot in snapshots {
            for entry in extract_includes(snapshot) {
                if let IncludeResolution::Resolved(values) =
                    resolve_include(snapshots, snapshot, &entry.target)
                {
                    if let Some(target) = values.first() {
                        result
                            .entry(target.canonical_path.clone())
                            .or_insert_with(Vec::new)
                            .push(snapshot.canonical_path.clone());
                    }
                }
            }
        }
        for values in result.values_mut() {
            values.sort();
            values.dedup();
        }
        result
    }
}

pub use project::*;
