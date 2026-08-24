#![allow(
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::doc_markdown,
    clippy::possible_missing_else,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::trim_split_whitespace,
    clippy::semicolon_if_nothing_returned
)]
//! Strict, bounded parsers for the metadata reports emitted by `CWTools`.

use cwtools_script_syntax::{ScriptEncoding, decode_script_bytes};
use std::collections::{BTreeMap, BTreeSet};

pub const MAX_INPUT_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_ENTRIES: usize = 100_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError {
    InputTooLarge {
        bytes: usize,
    },
    TooManyEntries {
        entries: usize,
    },
    Malformed {
        section: &'static str,
        line: usize,
        message: String,
    },
}
impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InputTooLarge { bytes } => write!(f, "input exceeds 16 MiB ({bytes} bytes)"),
            Self::TooManyEntries { entries } => write!(f, "too many entries ({entries})"),
            Self::Malformed {
                section,
                line,
                message,
            } => write!(f, "malformed {section} at line {line}: {message}"),
        }
    }
}
impl std::error::Error for ParseError {}

type Lines = Vec<String>;
fn lines(input: &[u8]) -> Result<Lines, ParseError> {
    if input.len() > MAX_INPUT_BYTES {
        return Err(ParseError::InputTooLarge { bytes: input.len() });
    }
    let text = decode_script_bytes(input, ScriptEncoding::Windows1252).map_err(|e| {
        ParseError::Malformed {
            section: "encoding",
            line: 1,
            message: e.message.into(),
        }
    })?;
    Ok(text
        .lines()
        .map(|line| line.strip_suffix('\r').unwrap_or(line).to_owned())
        .collect())
}
fn fail(section: &'static str, line: usize, message: impl Into<String>) -> ParseError {
    ParseError::Malformed {
        section,
        line,
        message: message.into(),
    }
}
fn csv(value: &str) -> Vec<String> {
    value
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_owned)
        .collect()
}
fn count(n: &mut usize) -> Result<(), ParseError> {
    *n += 1;
    if *n > MAX_ENTRIES {
        Err(ParseError::TooManyEntries { entries: *n })
    } else {
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StaticModifier {
    pub number: i32,
    pub tag: String,
    pub name: String,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Modifier {
    pub tag: String,
    pub category_id: String,
}
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SetupLog {
    pub static_modifiers: Vec<StaticModifier>,
    pub modifiers: Vec<Modifier>,
}

pub fn parse_setup_log_bytes(input: &[u8]) -> Result<SetupLog, ParseError> {
    let ls = lines(input)?;
    let mut out = SetupLog::default();
    let mut n = 0;
    let mut header = false;
    let mut printing = false;
    let mut i = 0;
    while i < ls.len() {
        let s = ls[i].trim();
        if s.contains("Initializing Database: CStaticModifierDatabase") {
            header = true;
        }
        if s.contains("Printing Modifier Definitions") {
            printing = true;
        }
        if s.starts_with("Static Modifier #") {
            let number = s
                .strip_prefix("Static Modifier #")
                .and_then(|v| v.trim().split_whitespace().next())
                .and_then(|v| v.parse().ok())
                .ok_or_else(|| fail("setup", i + 1, "invalid static modifier number"))?;
            let tag = ls
                .get(i + 1)
                .and_then(|v| v.trim().strip_prefix("tag = "))
                .map(str::trim)
                .filter(|v| !v.is_empty())
                .ok_or_else(|| fail("setup", i + 2, "missing tag"))?;
            let name = ls
                .get(i + 2)
                .and_then(|v| v.trim().strip_prefix("name = "))
                .map(str::trim)
                .ok_or_else(|| fail("setup", i + 3, "missing name"))?;
            out.static_modifiers.push(StaticModifier {
                number,
                tag: tag.to_owned(),
                name: name.to_owned(),
            });
            count(&mut n)?;
            i += 3;
            continue;
        }
        if printing {
            if let Some(rest) = s.strip_prefix("Tag: ") {
                let (tag, categories) = rest
                    .split_once(", Categories: ")
                    .ok_or_else(|| fail("setup", i + 1, "expected Tag: foo, Categories: N"))?;
                if tag.trim().is_empty() {
                    return Err(fail("setup", i + 1, "empty tag"));
                }
                let category_id = categories
                    .trim()
                    .parse::<i64>()
                    .map_err(|_| fail("setup", i + 1, "category count must be one integer"))?;
                if category_id < 0 {
                    return Err(fail("setup", i + 1, "negative category count"));
                }
                out.modifiers.push(Modifier {
                    tag: tag.trim().to_owned(),
                    category_id: category_id.to_string(),
                });
                count(&mut n)?;
            }
        }
        i += 1;
    }
    if !header {
        return Err(fail("setup", 1, "missing Initializing Database header"));
    }
    if !printing {
        return Err(fail(
            "setup",
            1,
            "missing Printing Modifier Definitions section",
        ));
    }
    if out.static_modifiers.is_empty() {
        return Err(fail("setup", 1, "no static modifiers"));
    }
    if out.modifiers.is_empty() {
        return Err(fail("setup", 1, "no modifier definitions"));
    }
    Ok(out)
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DataTypes {
    pub promotes: BTreeMap<String, String>,
    pub functions: BTreeMap<String, String>,
    pub confident_functions: BTreeMap<String, String>,
    pub types: BTreeMap<String, BTreeMap<String, String>>,
    pub type_names: BTreeSet<String>,
}
fn merge(map: &mut BTreeMap<String, String>, key: String, value: String) {
    match map.get(&key).map(String::as_str) {
        Some("[unregistered]") => {
            map.insert(key, value);
        }
        Some(_) if value == "[unregistered]" => {}
        _ => {
            map.insert(key, value);
        }
    }
}
fn parse_arrow(line: &str) -> Option<(String, String)> {
    let (a, b) = line.split_once("->")?;
    let key = a.trim().trim_matches('"');
    let value = b.trim().trim_end_matches('}').trim().trim_matches('"');
    (!key.is_empty() && !value.is_empty()).then(|| (key.to_owned(), value.to_owned()))
}

pub fn parse_data_types_bytes(input: &[u8]) -> Result<DataTypes, ParseError> {
    let ls = lines(input)?;
    let mut d = DataTypes::default();
    let mut section = None;
    let mut current = None;
    let mut depth = 0i32;
    let mut n = 0;
    let mut seen = BTreeSet::new();
    for (ix, raw) in ls.iter().enumerate() {
        let line = ix + 1;
        let s = raw.trim();
        if s.is_empty() {
            continue;
        }
        if s.starts_with("Global Promotes") {
            section = Some("promotes");
            seen.insert("promotes");
        } else if s.starts_with("Global Functions") {
            section = Some("functions");
            seen.insert("functions");
        } else if s.starts_with("Types") && s.contains('=') {
            section = Some("types");
            seen.insert("types");
        }
        if s.contains('=') && s.ends_with('{') {
            let key = s.split('=').next().unwrap_or("").trim().to_owned();
            if section == Some("types") && depth == 1 {
                d.type_names.insert(key.clone());
                d.types.entry(key.clone()).or_default();
                current = Some(key);
            }
        }
        if let Some((key, value)) = parse_arrow(s) {
            match section {
                Some("promotes") => merge(&mut d.promotes, key, value),
                Some("functions") => {
                    merge(&mut d.functions, key.clone(), value.clone());
                    if value != "[unregistered]" {
                        d.confident_functions.insert(key, value);
                    }
                }
                Some("types") => {
                    if let Some(name) = &current {
                        merge(d.types.get_mut(name).expect("type exists"), key, value);
                    }
                }
                _ => return Err(fail("datatypes", line, "entry outside required section")),
            }
            count(&mut n)?;
        }
        depth += s.chars().filter(|c| *c == '{').count() as i32;
        depth -= s.chars().filter(|c| *c == '}').count() as i32;
        if depth < 0 {
            return Err(fail("datatypes", line, "unexpected closing brace"));
        }
        if depth == 1 && section == Some("types") {
            current = None;
        }
    }
    if depth != 0 {
        return Err(fail("datatypes", ls.len().max(1), "unbalanced braces"));
    }
    if !seen.contains("promotes") || !seen.contains("functions") || !seen.contains("types") {
        return Err(fail("datatypes", 1, "missing required section"));
    }
    Ok(d)
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct EventTargetLink {
    pub name: String,
    pub desc: String,
    pub requires_data: bool,
    pub wildcard: bool,
    pub global: bool,
    pub input_scopes: Vec<String>,
    pub output_scopes: Vec<String>,
}
fn separator(s: &str) -> bool {
    !s.is_empty() && s.chars().all(|c| c == '-' || c == '=')
}
fn parse_links(input: &[u8]) -> Result<Vec<EventTargetLink>, ParseError> {
    let ls = lines(input)?;
    let mut out = Vec::new();
    let mut cur = None;
    let mut header = false;
    let mut footer = false;
    let mut n = 0;
    for (ix, raw) in ls.iter().enumerate() {
        let s = raw.trim();
        if s.contains("Event Target Links") {
            header = true;
        }
        if separator(s) {
            let had_entry = cur.is_some();
            if cur.is_some() {
                out.push(cur.take().unwrap());
                count(&mut n)?;
            }
            if header && had_entry {
                footer = true;
            }
            continue;
        }
        if let Some(rest) = s.strip_prefix("- ") {
            if let Some((name, desc)) = rest.split_once(" - ") {
                cur = Some(EventTargetLink {
                    name: name.trim().into(),
                    desc: desc.trim().into(),
                    ..Default::default()
                });
            }
        } else if let Some(x) = cur.as_mut() {
            if s.eq_ignore_ascii_case("Requires Data: yes") {
                x.requires_data = true
            } else if s.eq_ignore_ascii_case("Wild Card: yes") {
                x.wildcard = true
            } else if s.eq_ignore_ascii_case("Global Link: yes") {
                x.global = true
            } else if let Some(v) = s.strip_prefix("Input Scopes: ") {
                x.input_scopes = csv(v)
            } else if let Some(v) = s.strip_prefix("Output Scopes: ") {
                x.output_scopes = csv(v)
            }
        }
        let _ = ix;
    }
    if let Some(x) = cur {
        out.push(x);
        count(&mut n)?;
    }
    if !header || !footer {
        return Err(fail("links", 1, "missing header/spacer/footer"));
    }
    if out.is_empty() {
        return Err(fail("links", 1, "no links"));
    }
    Ok(out)
}
pub fn parse_event_target_links_bytes(input: &[u8]) -> Result<Vec<EventTargetLink>, ParseError> {
    parse_links(input)
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct JominiDoc {
    pub name: String,
    pub desc: String,
    pub traits: Option<String>,
    pub scopes: Vec<String>,
    pub targets: Vec<String>,
}
pub fn parse_trigger_docs_bytes(input: &[u8]) -> Result<Vec<JominiDoc>, ParseError> {
    parse_docs(input, "Trigger Documentation:")
}
pub fn parse_effect_docs_bytes(input: &[u8]) -> Result<Vec<JominiDoc>, ParseError> {
    parse_docs(input, "Effect Documentation:")
}
fn parse_docs(input: &[u8], header: &str) -> Result<Vec<JominiDoc>, ParseError> {
    let ls = lines(input)?;
    let h = ls
        .iter()
        .position(|l| l.trim() == header)
        .ok_or_else(|| fail("docs", 1, format!("missing {header}")))?;
    let mut out = Vec::new();
    let mut cur = None;
    let mut n = 0;
    let mut spacer = false;
    for (ix, raw) in ls.iter().enumerate().skip(h + 1) {
        let s = raw.trim();
        if separator(s) {
            spacer = true;
            continue;
        }
        if let Some(rest) = s.strip_prefix("- ") {
            if let Some(x) = cur.take() {
                out.push(x);
                count(&mut n)?;
            }
            if let Some((name, desc)) = rest.split_once(" - ") {
                cur = Some(JominiDoc {
                    name: name.trim().into(),
                    desc: desc.trim().into(),
                    ..Default::default()
                });
            }
        } else if let Some(x) = cur.as_mut() {
            if let Some(v) = s.strip_prefix("Traits: ") {
                x.traits = Some(v.trim().into())
            } else if let Some(v) = s.strip_prefix("Supported Scopes: ") {
                x.scopes = csv(v)
            } else if let Some(v) = s.strip_prefix("Supported Targets: ") {
                x.targets = csv(v)
            } else if !s.is_empty() {
                x.desc.push(' ');
                x.desc.push_str(s)
            }
        }
        let _ = ix;
    }
    if let Some(x) = cur {
        out.push(x);
        count(&mut n)?;
    }
    if !spacer || out.is_empty() {
        return Err(fail("docs", h + 1, "missing spacer or entries"));
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn setup() -> Vec<u8> {
        b"noise\nInitializing Database: CStaticModifierDatabase\r\nStatic Modifier # 1\r\ntag = foo\r\nname = Caf\xE9\r\nPrinting Modifier Definitions\r\nTag: foo, Categories: 3\r\n".to_vec()
    }
    #[test]
    fn setup_valid_cp1252() {
        assert_eq!(
            parse_setup_log_bytes(&setup()).unwrap().static_modifiers[0].name,
            "Café"
        );
    }
    #[test]
    fn setup_requires_header() {
        let mut x = setup();
        x.retain(|b| *b != b'I');
        assert!(parse_setup_log_bytes(&x).is_err());
    }
    #[test]
    fn setup_rejects_category_list() {
        let mut x = setup();
        x.extend_from_slice(b"Tag: bar, Categories: 1, 2\n");
        assert!(parse_setup_log_bytes(&x).is_err());
    }
    #[test]
    fn setup_duplicates_preserved() {
        let mut x = setup();
        x.extend_from_slice(b"Tag: foo, Categories: 4\n");
        assert_eq!(parse_setup_log_bytes(&x).unwrap().modifiers.len(), 2);
    }
    fn types() -> Vec<u8> {
        b"Global Promotes = {\n a -> [unregistered]\n a -> Planet\n}\nGlobal Functions = {\n f -> [unregistered]\n f -> Character\n}\nTypes = {\n X = {\n y -> z\n }\n}\n".to_vec()
    }
    #[test]
    fn types_nested_merge() {
        let x = parse_data_types_bytes(&types()).unwrap();
        assert_eq!(x.promotes["a"], "Planet");
        assert_eq!(x.functions["f"], "Character");
        assert_eq!(x.types["X"]["y"], "z");
    }
    #[test]
    fn types_missing_section() {
        let x = b"Global Promotes = { a -> b }";
        assert!(parse_data_types_bytes(x).is_err());
    }
    #[test]
    fn types_unbalanced() {
        let x = b"Global Promotes = {\n a -> b\nGlobal Functions = {}\nTypes = {}";
        assert!(parse_data_types_bytes(x).is_err());
    }
    #[test]
    fn types_duplicate_confidence() {
        let x = types();
        let d = parse_data_types_bytes(&x).unwrap();
        assert_eq!(d.confident_functions["f"], "Character");
    }
    fn docs(h: &str) -> Vec<u8> {
        format!("{h}\n--------------------\n- foo - First line\nsecond line\nTraits: numeric\nSupported Scopes: Character, Planet\nSupported Targets: Country\n").into_bytes()
    }
    #[test]
    fn trigger_docs_multiline() {
        let d = parse_trigger_docs_bytes(&docs("Trigger Documentation:")).unwrap();
        assert!(d[0].desc.contains("second line"));
        assert_eq!(d[0].scopes.len(), 2);
    }
    #[test]
    fn effect_docs_header() {
        assert!(parse_effect_docs_bytes(&docs("Effect Documentation:")).is_ok());
    }
    #[test]
    fn docs_wrong_header() {
        assert!(parse_trigger_docs_bytes(&docs("Effect Documentation:")).is_err());
    }
    #[test]
    fn docs_duplicates() {
        let mut x = docs("Trigger Documentation:");
        x.extend_from_slice(b"- foo - Again\n");
        assert_eq!(parse_trigger_docs_bytes(&x).unwrap().len(), 2);
    }
    #[test]
    fn links_header_and_fields() {
        let x=b"Event Target Links\n====================\n- foo - desc\nRequires Data: yes\nInput Scopes: A, B\n--------------------\n";
        let l = parse_event_target_links_bytes(x).unwrap();
        assert!(l[0].requires_data);
        assert_eq!(l[0].input_scopes.len(), 2);
    }
    #[test]
    fn links_missing_footer() {
        let x = b"Event Target Links\n====================\n- foo - desc\n";
        assert!(parse_event_target_links_bytes(x).is_err());
    }
    #[test]
    fn bounds() {
        assert!(matches!(
            parse_setup_log_bytes(&vec![b'x'; MAX_INPUT_BYTES + 1]),
            Err(ParseError::InputTooLarge { .. })
        ));
    }
}
