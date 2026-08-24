#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet, HashSet};

use regex::{Captures, Regex};

#[must_use]
pub const fn should_use_immediate_fallback(
    writer_busy: bool,
    _validation: bool,
    heavy: bool,
) -> bool {
    writer_busy || heavy
}

#[must_use]
pub const fn can_return_empty_fallback(writer_busy: bool, _validation: bool) -> bool {
    writer_busy
}

fn is_prefix_boundary(value: char) -> bool {
    value.is_whitespace()
        || matches!(
            value,
            '=' | '<' | '>' | '{' | '}' | ',' | '|' | '(' | ')' | '[' | ']' | '"'
        )
        || value as u32 == 39
}

#[must_use]
pub fn prefix_from_text_before_cursor(text: &str) -> Option<&str> {
    let boundary = text
        .char_indices()
        .rev()
        .find(|(_, value)| is_prefix_boundary(*value))
        .map_or(0, |(offset, value)| offset + value.len_utf8());
    let token = &text[boundary..];
    let prefix = token.rsplit_once('.').map_or(token, |(_, suffix)| suffix);
    (!prefix.trim().is_empty()).then_some(prefix)
}

#[must_use]
pub fn line_before_cursor(text: &str, line: i64, character_utf16: i64) -> String {
    if line < 0 {
        return String::new();
    }
    let Some(content) = text
        .split('\n')
        .nth(usize::try_from(line).unwrap_or(usize::MAX))
    else {
        return String::new();
    };
    let content = content.strip_suffix('\r').unwrap_or(content);
    let target = usize::try_from(character_utf16.max(0)).unwrap_or(usize::MAX);
    let mut units = 0;
    let mut end = content.len();
    for (offset, value) in content.char_indices() {
        if units >= target {
            end = offset;
            break;
        }
        units += value.len_utf16();
    }
    content[..end].to_owned()
}

#[must_use]
pub fn prefix_at_position(text: &str, line: i64, character: i64) -> Option<String> {
    prefix_from_text_before_cursor(&line_before_cursor(text, line, character)).map(str::to_owned)
}

#[must_use]
pub fn completion_cache_key(
    path: &str,
    hash: i64,
    line: i64,
    character: i64,
    debug: bool,
    insert_replace: bool,
) -> String {
    format!("{path}|{hash}|{line}|{character}|{debug}|{insert_replace}")
}

fn is_token_character(value: char) -> bool {
    !value.is_whitespace() && !matches!(value, '.' | '|' | '"' | '=' | '{' | '}' | ',')
}

#[must_use]
pub fn token_range_in_line(line: &str, character: u32) -> (u32, u32, u32) {
    let max = u32::try_from(line.encode_utf16().count()).unwrap_or(u32::MAX);
    let cursor = character.min(max);
    let chars: Vec<_> = line
        .char_indices()
        .scan(0_u32, |unit, (_, value)| {
            let start = *unit;
            *unit += u32::try_from(value.len_utf16()).unwrap_or(2);
            Some((value, start, *unit))
        })
        .collect();
    let mut start = cursor;
    for (value, unit_start, unit_end) in chars.iter().rev() {
        if *unit_end > cursor {
            continue;
        }
        if !is_token_character(*value) {
            break;
        }
        start = *unit_start;
    }
    let mut end = cursor;
    for (value, unit_start, unit_end) in &chars {
        if *unit_start < cursor {
            continue;
        }
        if !is_token_character(*value) {
            break;
        }
        end = *unit_end;
    }
    (start, cursor, end)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticDirectoryPath {
    pub path: String,
    pub entity_types: Vec<String>,
}

fn has_scheme(value: &str) -> bool {
    let Some((prefix, _)) = value.split_once(':') else {
        return false;
    };
    let mut chars = prefix.chars();
    chars
        .next()
        .is_some_and(|value| value.is_ascii_alphabetic())
        && chars.all(|value| value.is_ascii_alphanumeric() || matches!(value, '+' | '-' | '.'))
}

#[must_use]
pub fn normalize_semantic_directory(value: &str) -> Option<String> {
    let trimmed = value.trim();
    if trimmed.is_empty()
        || trimmed.starts_with('/')
        || trimmed.starts_with(char::from(92))
        || has_scheme(trimmed)
        || trimmed.chars().any(|value| {
            matches!(value, '*' | '?' | '$' | '<' | '>' | '{' | '}' | '[' | ']')
                || value as u32 == 0
        })
    {
        return None;
    }
    let slash = trimmed.replace(char::from(92), "/");
    let slash = slash.trim_end_matches('/');
    let relative = if slash.eq_ignore_ascii_case("game") {
        ""
    } else if slash
        .get(..5)
        .is_some_and(|prefix| prefix.eq_ignore_ascii_case("game/"))
    {
        &slash[5..]
    } else {
        slash
    };
    let segments: Vec<_> = relative.split('/').collect();
    if segments.is_empty()
        || segments.iter().any(|segment| {
            segment.trim().is_empty()
                || matches!(*segment, "." | "..")
                || has_scheme(segment)
                || segment.chars().any(|value| value as u32 == 0)
        })
    {
        return None;
    }
    Some(segments.join("/"))
}

#[must_use]
pub fn build_semantic_directories<'a>(
    definitions: impl IntoIterator<Item = (&'a str, Vec<&'a str>)>,
) -> Vec<SemanticDirectoryPath> {
    let mut paths: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (entity, candidates) in definitions {
        let entity = entity.trim().to_lowercase();
        if entity.is_empty() {
            continue;
        }
        for candidate in candidates {
            if let Some(path) = normalize_semantic_directory(candidate) {
                paths.entry(path).or_default().insert(entity.clone());
            }
        }
    }
    paths
        .into_iter()
        .map(|(path, values)| SemanticDirectoryPath {
            path,
            entity_types: values.into_iter().collect(),
        })
        .collect()
}

pub const MAX_OVERLAY_FILES: usize = 64;
pub const MAX_OVERLAY_FILE_CHARS: usize = 2_000_000;
pub const MAX_OVERLAY_TOTAL_CHARS: usize = 8_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PayloadDecision {
    Accept,
    Duplicate,
    Oversized,
    Truncated,
}

#[must_use]
pub fn admit_overlay_payload<'a>(
    items: impl IntoIterator<Item = (&'a str, i64)>,
    case_insensitive: bool,
) -> Vec<PayloadDecision> {
    let mut seen = HashSet::new();
    let mut total = 0_usize;
    items
        .into_iter()
        .enumerate()
        .map(|(index, (path, length))| {
            if index >= MAX_OVERLAY_FILES {
                return PayloadDecision::Truncated;
            }
            let length = usize::try_from(length.max(0)).unwrap_or(usize::MAX);
            total = total.saturating_add(length);
            if length > MAX_OVERLAY_FILE_CHARS || total > MAX_OVERLAY_TOTAL_CHARS {
                return PayloadDecision::Oversized;
            }
            let key = if case_insensitive {
                path.to_lowercase()
            } else {
                path.to_owned()
            };
            if seen.insert(key) {
                PayloadDecision::Accept
            } else {
                PayloadDecision::Duplicate
            }
        })
        .collect()
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FoldingSpan {
    pub start_line: u32,
    pub start_character: u32,
    pub end_line: u32,
    pub end_character: Option<u32>,
}

#[must_use]
pub fn folding_ranges(text: &str) -> Vec<FoldingSpan> {
    let mut spans = Vec::new();
    let mut stack = Vec::new();
    let (mut line, mut character, mut line_start) = (0_u32, 0_u32, 0_usize);
    let (mut in_string, mut escaped, mut in_comment) = (false, false, false);
    for (offset, current) in text.char_indices() {
        if in_comment {
            if current == '\n' {
                in_comment = false;
            }
        } else if in_string {
            if escaped {
                escaped = false;
            } else if current as u32 == 92 {
                escaped = true;
            } else if current == '"' {
                in_string = false;
            }
        } else {
            match current {
                '#' => in_comment = true,
                '"' => in_string = true,
                '{' => stack.push((line, character)),
                '}' => {
                    if let Some((start_line, start_character)) = stack.pop() {
                        if line > start_line {
                            let own_line =
                                text[line_start..offset].chars().all(char::is_whitespace);
                            let end_line = if own_line { line - 1 } else { line };
                            if end_line > start_line {
                                spans.push(FoldingSpan {
                                    start_line,
                                    start_character,
                                    end_line,
                                    end_character: (!own_line).then_some(character),
                                });
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        if current == '\n' {
            line += 1;
            character = 0;
            line_start = offset + 1;
        } else {
            character += u32::try_from(current.len_utf16()).unwrap_or(2);
        }
    }
    spans.sort_unstable();
    spans
}

pub const MAX_LOCALISATION_REFERENCE_DEPTH: usize = 8;
pub const MAX_LOCALISATION_EXPANDED_LENGTH: usize = 4096;

fn strip_localisation_quotes(value: &str) -> &str {
    let trimmed = value.trim();
    if trimmed.len() >= 2 && trimmed.starts_with('"') && trimmed.ends_with('"') {
        &trimmed[1..trimmed.len() - 1]
    } else {
        trimmed
    }
}

fn bounded(value: &str) -> String {
    value
        .chars()
        .take(MAX_LOCALISATION_EXPANDED_LENGTH)
        .collect()
}

fn valid_reference_key(value: &str) -> bool {
    !value.is_empty()
        && value.chars().all(|ch| {
            ch.is_ascii_alphanumeric()
                || matches!(ch, '_' | '@' | '.' | ':' | '/' | '-')
                || ch as u32 == 39
        })
}

fn resolve_localisation_text(
    depth: usize,
    visited: &BTreeSet<String>,
    text: &str,
    localisation: &BTreeMap<String, String>,
    variables: &BTreeMap<String, String>,
) -> String {
    let text = bounded(text);
    if depth >= MAX_LOCALISATION_REFERENCE_DEPTH || text.is_empty() {
        return text;
    }
    let reference = Regex::new(r"\$([^$\r\n]+)\$").expect("static reference regex");
    let whitespace = Regex::new(r"(?i)^\$(?:t|tt|TABBED_NEW_LINE|NEW_LINE)\$$")
        .expect("static whitespace regex");
    let references = reference.replace_all(&text, |captures: &Captures<'_>| {
        let original = captures.get(0).map_or("", |value| value.as_str());
        if whitespace.is_match(original) {
            return " ".to_owned();
        }
        let payload = captures.get(1).map_or("", |value| value.as_str());
        let key = payload.split('|').next().unwrap_or_default().trim();
        if !valid_reference_key(key) || visited.contains(key) {
            return original.to_owned();
        }
        let Some(replacement) = localisation.get(key).or_else(|| variables.get(key)) else {
            return original.to_owned();
        };
        let mut next = visited.clone();
        next.insert(key.to_owned());
        resolve_localisation_text(
            depth + 1,
            &next,
            strip_localisation_quotes(replacement),
            localisation,
            variables,
        )
    });
    let concept = Regex::new(r"\[\s*'([^'\]\r\n]+)'(?:\s*,?\s*'?([^'\]\r\n]*)'?)?\s*\]")
        .expect("static concept regex");
    bounded(
        &concept.replace_all(&references, |captures: &Captures<'_>| {
            let explicit = captures.get(2).map_or("", |value| value.as_str());
            if !explicit.trim().is_empty() {
                return resolve_localisation_text(
                    depth + 1,
                    visited,
                    explicit,
                    localisation,
                    variables,
                );
            }
            let key = captures.get(1).map_or("", |value| value.as_str());
            if visited.contains(key) {
                return captures
                    .get(0)
                    .map_or("", |value| value.as_str())
                    .to_owned();
            }
            let Some(replacement) = localisation.get(key).or_else(|| variables.get(key)) else {
                return captures
                    .get(0)
                    .map_or("", |value| value.as_str())
                    .to_owned();
            };
            let mut next = visited.clone();
            next.insert(key.to_owned());
            resolve_localisation_text(
                depth + 1,
                &next,
                strip_localisation_quotes(replacement),
                localisation,
                variables,
            )
        }),
    )
}

/// Formats the bounded plain-text label used by localisation inlay hints.
///
/// # Panics
/// Panics only if a checked-in static regular expression is invalid.
#[must_use]
pub fn format_localisation_hint(
    localisation: &BTreeMap<String, String>,
    variables: &BTreeMap<String, String>,
    description: &str,
) -> Option<String> {
    let normalized = description
        .replace("\r\n", " ")
        .replace('\n', " ")
        .replace("\\n", " ");
    let resolved = resolve_localisation_text(
        0,
        &BTreeSet::new(),
        strip_localisation_quotes(normalized.trim()),
        localisation,
        variables,
    );
    let sequence =
        Regex::new(r"\(\s*\d+\?:(?:[^()]|\([^()]*\))*\)").expect("static sequence regex");
    let icon = Regex::new(r"(?:Â)?£([A-Za-z0-9_.:-]+)(?:\|([^£Â\s\[\]]+))?(?:Â)?£?")
        .expect("static icon regex");
    let style = Regex::new(r"(?:(?:Â)?§|搂)[A-Za-z0-9!%-]").expect("static style regex");
    let whitespace_marker =
        Regex::new(r"(?i)\$(?:t|tt|TABBED_NEW_LINE|NEW_LINE)\$").expect("static whitespace regex");
    let collapsed = Regex::new(r"\s+").expect("static whitespace regex");
    let no_sequence = sequence.replace_all(&resolved, "");
    let icons = icon.replace_all(&no_sequence, |captures: &Captures<'_>| {
        let name = captures.get(1).map_or("", |value| value.as_str());
        captures.get(2).map_or_else(
            || format!("£{name}£"),
            |modifier| format!("£{name}|{}£", modifier.as_str()),
        )
    });
    let markers = whitespace_marker.replace_all(&icons, " ");
    let styles = style.replace_all(&markers, "");
    let clean = collapsed.replace_all(&styles, " ").trim().to_owned();
    if clean.is_empty() {
        return None;
    }
    let count = clean.chars().count();
    Some(if count > 50 {
        format!("{}...", clean.chars().take(50).collect::<String>())
    } else {
        clean
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn fallback_contract() {
        assert!(!should_use_immediate_fallback(false, true, false));
        assert!(should_use_immediate_fallback(true, false, false));
        assert!(should_use_immediate_fallback(false, false, true));
        assert!(!can_return_empty_fallback(false, true));
    }
    #[test]
    fn completion_contract() {
        assert_eq!(
            prefix_from_text_before_cursor("x = modifier:fo"),
            Some("modifier:fo")
        );
        assert_eq!(
            prefix_from_text_before_cursor("scope.member"),
            Some("member")
        );
        assert_eq!(prefix_at_position("x = foo\r\ny", 0, 7), Some("foo".into()));
        assert_eq!(token_range_in_line("x = modifier:foo", 8), (4, 8, 16));
    }
    #[test]
    fn catalog_contract() {
        assert_eq!(
            normalize_semantic_directory(" game/common\\foo/ "),
            Some("common/foo".into())
        );
        for bad in ["/abs", "../x", "a//b", "file:x", "common/*"] {
            assert_eq!(normalize_semantic_directory(bad), None);
        }
        let built = build_semantic_directories([
            (" Event ", vec!["game/events", "events"]),
            ("event", vec!["events"]),
        ]);
        assert_eq!(
            built,
            vec![SemanticDirectoryPath {
                path: "events".into(),
                entity_types: vec!["event".into()]
            }]
        );
    }
    #[test]
    fn overlay_contract() {
        assert_eq!(
            admit_overlay_payload([("A", 1), ("a", 1), ("b", 2_000_001)], true),
            vec![
                PayloadDecision::Accept,
                PayloadDecision::Duplicate,
                PayloadDecision::Oversized
            ]
        );
        assert_eq!(
            admit_overlay_payload((0..65).map(|_| ("x", 0)), false)[64],
            PayloadDecision::Truncated
        );
    }
    #[test]
    fn localisation_preview_is_bounded_and_cycle_safe() {
        let localisation = BTreeMap::from([
            (
                "ROOT".to_owned(),
                "\"Hello $NAME$ §Y£energy£§!\"".to_owned(),
            ),
            ("LOOP".to_owned(), "$LOOP$".to_owned()),
            ("CONCEPT".to_owned(), "Concept Name".to_owned()),
        ]);
        let variables = BTreeMap::from([("NAME".to_owned(), "Commander".to_owned())]);
        assert_eq!(
            format_localisation_hint(&localisation, &variables, "$ROOT$"),
            Some("Hello Commander £energy£".to_owned())
        );
        assert_eq!(
            format_localisation_hint(&localisation, &variables, "['CONCEPT']"),
            Some("Concept Name".to_owned())
        );
        assert_eq!(
            format_localisation_hint(&localisation, &variables, "$LOOP$"),
            Some("$LOOP$".to_owned())
        );
        let long = "a".repeat(100);
        assert_eq!(
            format_localisation_hint(&BTreeMap::new(), &BTreeMap::new(), &long)
                .unwrap()
                .chars()
                .count(),
            53
        );
    }

    #[test]
    fn folding_contract() {
        let text = "root = {\n value = \"}\" # {\n child = {\n  x = 1\n }\n}\nunclosed = {";
        let ranges = folding_ranges(text);
        assert_eq!(ranges.len(), 2);
        assert_eq!(ranges[0].start_line, 0);
        assert_eq!(ranges[1].start_line, 2);
    }
}
