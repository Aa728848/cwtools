//! Bounded parsers for Stellaris documentation logs.

use cwtools_script_syntax::{ScriptEncoding, decode_script_bytes};

const MAX_INPUT: usize = 16 * 1024 * 1024;
const MAX_SEARCH: usize = 4000;
const MAX_ENTRIES: usize = 100_000;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DocumentationBundle {
    pub triggers: Vec<DocEntry>,
    pub effects: Vec<DocEntry>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DocEntry {
    pub name: String,
    pub description: String,
    pub usage: String,
    pub scopes: Vec<String>,
    pub targets: Vec<String>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModifierEntry {
    pub tag: String,
    pub categories: Vec<String>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DocsError {
    InputTooLarge,
    Decode,
    MissingHeader(String),
    MissingFooter,
    Malformed,
    TooManyEntries,
    SearchLimit,
}

fn text(bytes: &[u8]) -> Result<String, DocsError> {
    if bytes.len() > MAX_INPUT {
        return Err(DocsError::InputTooLarge);
    }
    decode_script_bytes(bytes, ScriptEncoding::Windows1252).map_err(|_| DocsError::Decode)
}
fn lines(s: &str) -> Vec<&str> {
    s.lines()
        .map(|x| x.strip_suffix('\r').unwrap_or(x))
        .collect()
}
fn split_values(s: &str) -> Vec<String> {
    s.split(',')
        .flat_map(|x| x.split_whitespace())
        .filter(|x| !x.is_empty())
        .map(str::to_owned)
        .collect()
}
fn section<'a>(
    ls: &'a [&'a str],
    header: &str,
    next: Option<&str>,
) -> Result<&'a [&'a str], DocsError> {
    let at = ls
        .iter()
        .position(|x| {
            x.to_ascii_lowercase()
                .contains(&header.to_ascii_lowercase())
        })
        .ok_or_else(|| DocsError::MissingHeader(header.to_owned()))?;
    let end = next
        .and_then(|h| {
            ls.iter()
                .skip(at + 1)
                .position(|x| x.to_ascii_lowercase().contains(&h.to_ascii_lowercase()))
                .map(|n| at + 1 + n)
        })
        .unwrap_or(ls.len());
    let footer = ls
        .iter()
        .skip(at + 1)
        .position(|x| x.trim_start().starts_with("================="));
    if footer.is_none() {
        return Err(DocsError::MissingFooter);
    }
    Ok(&ls[at + 1..end])
}
fn parse_doc_section(ls: &[&str]) -> Result<Vec<DocEntry>, DocsError> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < ls.len() {
        let line = ls[i].trim();
        let Some((name, first_desc)) = line.split_once(" - ") else {
            i += 1;
            continue;
        };
        if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            i += 1;
            continue;
        }
        if out.len() >= MAX_ENTRIES {
            return Err(DocsError::TooManyEntries);
        }
        let desc = first_desc.trim().to_owned();
        let mut usage = String::new();
        let mut scopes = Vec::new();
        let mut targets = Vec::new();
        i += 1;
        while i < ls.len() {
            let x = ls[i].trim();
            let low = x.to_ascii_lowercase();
            if low.starts_with("supported scopes:") {
                scopes = split_values(x.split_once(':').map_or("", |(_, v)| v.trim()));
                i += 1;
                break;
            }
            if low.starts_with("supported targets:") {
                targets = split_values(x.split_once(':').map_or("", |(_, v)| v.trim()));
                i += 1;
                break;
            }
            if x.starts_with("=================") {
                break;
            }
            if !x.is_empty() {
                if low.starts_with("supported ") {
                    return Err(DocsError::Malformed);
                }
                if usage.is_empty() {
                    x.clone_into(&mut usage);
                } else {
                    usage.push('\n');
                    usage.push_str(x);
                }
            }
            i += 1;
        }
        out.push(DocEntry {
            name: name.to_owned(),
            description: desc,
            usage,
            scopes,
            targets,
        });
    }
    if out.is_empty() {
        return Err(DocsError::Malformed);
    }
    Ok(out)
}

/// # Errors
/// Returns an error for invalid encoding, malformed sections, missing headers/footers, or bounds violations.
pub fn parse_docs_bytes(bytes: &[u8]) -> Result<DocumentationBundle, DocsError> {
    let s = text(bytes)?;
    let ls = lines(&s);
    let t = section(&ls, "trigger documentation", Some("effect documentation"))?;
    let e = section(&ls, "effect documentation", None)?;
    Ok(DocumentationBundle {
        triggers: parse_doc_section(t)?,
        effects: parse_doc_section(e)?,
    })
}

/// # Errors
/// Returns an error for invalid encoding, malformed input, missing headers, or bounds violations.
pub fn parse_modifiers_bytes(bytes: &[u8]) -> Result<Vec<ModifierEntry>, DocsError> {
    let s = text(bytes)?;
    let ls = lines(&s);
    let at = ls
        .iter()
        .position(|x| {
            x.to_ascii_lowercase()
                .contains("printing modifier definitions:")
        })
        .ok_or(DocsError::MissingHeader(
            "Printing Modifier Definitions:".to_owned(),
        ))?;
    if at > MAX_SEARCH * 5000 {
        return Err(DocsError::SearchLimit);
    }
    let mut out = Vec::new();
    for x in ls.iter().skip(at + 1) {
        let x = x.trim();
        if !x.starts_with("- ") {
            continue;
        }
        let Some((tag, cats)) = x[2..].split_once(", Category:") else {
            continue;
        };
        if out.len() >= MAX_ENTRIES {
            return Err(DocsError::TooManyEntries);
        }
        let tag = tag.trim();
        if tag.is_empty() {
            return Err(DocsError::Malformed);
        }
        out.push(ModifierEntry {
            tag: tag.to_owned(),
            categories: cats
                .split(',')
                .map(str::trim)
                .filter(|x| !x.is_empty())
                .map(str::to_owned)
                .collect(),
        });
    }
    if out.is_empty() {
        Err(DocsError::Malformed)
    } else {
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cp1252() {
        let x = parse_modifiers_bytes(
            b"Printing Modifier Definitions:\r\n- caf\xE9, Category: Pops, Planets\r\n",
        )
        .unwrap();
        assert_eq!(x[0].tag, "café");
        assert_eq!(x[0].categories.len(), 2);
    }
    #[test]
    fn bad() {
        assert!(matches!(
            parse_docs_bytes(b"x"),
            Err(DocsError::MissingHeader(_))
        ));
        assert!(matches!(
            parse_modifiers_bytes(b"x"),
            Err(DocsError::MissingHeader(_))
        ));
    }
    #[test]
    fn bounds() {
        assert!(matches!(
            parse_docs_bytes(&vec![0; MAX_INPUT + 1]),
            Err(DocsError::InputTooLarge)
        ));
    }
}
