#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fmt;
use std::sync::{Arc, RwLock};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceId(u32);

impl SourceId {
    #[must_use]
    pub const fn new(value: u32) -> Self {
        Self(value)
    }
    #[must_use]
    pub const fn get(self) -> u32 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Range {
    pub source: SourceId,
    pub start: Position,
    pub end: Position,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TextRange {
    pub start: Position,
    pub end: Position,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TextChange {
    pub range: Option<TextRange>,
    pub range_length: Option<u32>,
    pub text: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LineIndex {
    line_starts: Vec<usize>,
    line_ends: Vec<usize>,
}

impl LineIndex {
    #[must_use]
    pub fn new(text: &str) -> Self {
        let bytes = text.as_bytes();
        let mut line_starts = vec![0];
        let mut line_ends = Vec::new();
        for (offset, byte) in bytes.iter().copied().enumerate() {
            if byte == b'\n' {
                line_ends.push(if offset > 0 && bytes[offset - 1] == b'\r' {
                    offset - 1
                } else {
                    offset
                });
                line_starts.push(offset + 1);
            }
        }
        line_ends.push(text.len());
        Self {
            line_starts,
            line_ends,
        }
    }

    #[must_use]
    pub fn line_count(&self) -> usize {
        self.line_starts.len()
    }

    #[must_use]
    pub fn position(&self, text: &str, byte_offset: usize) -> Option<Position> {
        if byte_offset > text.len() || !text.is_char_boundary(byte_offset) {
            return None;
        }
        let line = self
            .line_starts
            .partition_point(|start| *start <= byte_offset)
            .saturating_sub(1);
        let start = self.line_starts[line];
        let content_offset = byte_offset.min(self.line_ends[line]);
        Some(Position {
            line: u32::try_from(line).ok()?,
            character: u32::try_from(text[start..content_offset].encode_utf16().count()).ok()?,
        })
    }

    #[must_use]
    pub fn byte_offset(&self, text: &str, position: Position) -> Option<usize> {
        let line = usize::try_from(position.line).ok()?;
        let start = *self.line_starts.get(line)?;
        let end = *self.line_ends.get(line)?;
        let target = usize::try_from(position.character).ok()?;
        let mut units = 0;
        for (relative, character) in text[start..end].char_indices() {
            if units == target {
                return Some(start + relative);
            }
            units += character.len_utf16();
            if units > target {
                return None;
            }
        }
        (units == target).then_some(end)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Document {
    pub source: SourceId,
    pub text: String,
    pub version: i64,
    pub saved: bool,
    pub line_index: LineIndex,
}

impl Document {
    fn new(source: SourceId, text: String, version: i64) -> Self {
        let line_index = LineIndex::new(&text);
        Self {
            source,
            text,
            version,
            saved: true,
            line_index,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DocumentError {
    AlreadyOpen(SourceId),
    NotOpen(SourceId),
    StaleVersion { current: i64, incoming: i64 },
    InvalidRange(TextRange),
    RangeLengthMismatch { expected: u32, actual: usize },
}

impl fmt::Display for DocumentError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}
impl std::error::Error for DocumentError {}

#[derive(Clone, Debug, Default)]
pub struct DocumentStore {
    documents: BTreeMap<SourceId, Document>,
}

impl DocumentStore {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
    #[must_use]
    pub fn get(&self, source: SourceId) -> Option<&Document> {
        self.documents.get(&source)
    }

    /// Opens a new overlay.
    /// # Errors
    /// Returns [`DocumentError::AlreadyOpen`] for duplicate sources.
    pub fn open(
        &mut self,
        source: SourceId,
        text: impl Into<String>,
        version: i64,
    ) -> Result<(), DocumentError> {
        if self.documents.contains_key(&source) {
            return Err(DocumentError::AlreadyOpen(source));
        }
        self.documents
            .insert(source, Document::new(source, text.into(), version));
        Ok(())
    }

    /// Applies an ordered batch atomically.
    /// # Errors
    /// Returns a version or strict UTF-16 range validation error.
    pub fn change(
        &mut self,
        source: SourceId,
        version: i64,
        changes: &[TextChange],
    ) -> Result<(), DocumentError> {
        let document = self
            .documents
            .get(&source)
            .ok_or(DocumentError::NotOpen(source))?;
        if version <= document.version {
            return Err(DocumentError::StaleVersion {
                current: document.version,
                incoming: version,
            });
        }
        let mut text = document.text.clone();
        for change in changes {
            if let Some(range) = change.range {
                let index = LineIndex::new(&text);
                let start = index
                    .byte_offset(&text, range.start)
                    .ok_or(DocumentError::InvalidRange(range))?;
                let end = index
                    .byte_offset(&text, range.end)
                    .ok_or(DocumentError::InvalidRange(range))?;
                if start > end {
                    return Err(DocumentError::InvalidRange(range));
                }
                if let Some(expected) = change.range_length {
                    let actual = text[start..end].encode_utf16().count();
                    if usize::try_from(expected).ok() != Some(actual) {
                        return Err(DocumentError::RangeLengthMismatch { expected, actual });
                    }
                }
                text.replace_range(start..end, &change.text);
            } else {
                text.clone_from(&change.text);
            }
        }
        let Some(document) = self.documents.get_mut(&source) else {
            return Err(DocumentError::NotOpen(source));
        };
        document.text = text;
        document.version = version;
        document.saved = false;
        document.line_index = LineIndex::new(&document.text);
        Ok(())
    }

    /// Marks an overlay saved and optionally replaces its authoritative text.
    /// # Errors
    /// Returns [`DocumentError::NotOpen`] for unknown sources.
    pub fn save(&mut self, source: SourceId, text: Option<String>) -> Result<(), DocumentError> {
        let document = self
            .documents
            .get_mut(&source)
            .ok_or(DocumentError::NotOpen(source))?;
        if let Some(text) = text {
            document.text = text;
            document.line_index = LineIndex::new(&document.text);
        }
        document.saved = true;
        Ok(())
    }

    #[must_use]
    pub fn close(&mut self, source: SourceId) -> Option<Document> {
        self.documents.remove(&source)
    }
}

pub type SharedDocumentStore = Arc<RwLock<DocumentStore>>;
#[must_use]
pub fn shared_document_store() -> SharedDocumentStore {
    Arc::new(RwLock::new(DocumentStore::new()))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn pos(line: u32, character: u32) -> Position {
        Position { line, character }
    }

    #[test]
    fn unicode_crlf_positions_round_trip() {
        let text = "a😀\r\nβ\n";
        let index = LineIndex::new(text);
        assert_eq!(index.line_count(), 3);
        for position in [
            pos(0, 0),
            pos(0, 1),
            pos(0, 3),
            pos(1, 0),
            pos(1, 1),
            pos(2, 0),
        ] {
            let offset = index.byte_offset(text, position).unwrap();
            assert_eq!(index.position(text, offset), Some(position));
        }
        assert_eq!(index.byte_offset(text, pos(0, 2)), None);
    }

    #[test]
    fn ordered_changes_are_atomic_and_validate_range_length() {
        let id = SourceId::new(1);
        let mut store = DocumentStore::new();
        store.open(id, "a😀\r\nlast", 1).unwrap();
        let changes = [
            TextChange {
                range: Some(TextRange {
                    start: pos(0, 1),
                    end: pos(0, 3),
                }),
                range_length: Some(2),
                text: "β".into(),
            },
            TextChange {
                range: Some(TextRange {
                    start: pos(1, 0),
                    end: pos(1, 4),
                }),
                range_length: Some(4),
                text: "done".into(),
            },
        ];
        store.change(id, 2, &changes).unwrap();
        assert_eq!(store.get(id).unwrap().text, "aβ\r\ndone");
        let bad = TextChange {
            range: Some(TextRange {
                start: pos(0, 0),
                end: pos(0, 1),
            }),
            range_length: Some(9),
            text: String::new(),
        };
        assert!(store.change(id, 3, &[bad]).is_err());
        assert_eq!(store.get(id).unwrap().version, 2);
        assert_eq!(store.get(id).unwrap().text, "aβ\r\ndone");
    }

    #[test]
    fn open_change_save_close_lifecycle() {
        let id = SourceId::new(2);
        let mut store = DocumentStore::new();
        store.open(id, "a", 1).unwrap();
        store
            .change(
                id,
                2,
                &[TextChange {
                    range: None,
                    range_length: None,
                    text: "b".into(),
                }],
            )
            .unwrap();
        assert!(!store.get(id).unwrap().saved);
        store.save(id, None).unwrap();
        assert!(store.get(id).unwrap().saved);
        assert_eq!(store.close(id).unwrap().text, "b");
        assert!(store.close(id).is_none());
    }

    #[test]
    fn deterministic_unicode_position_sequences() {
        let atoms = ["a", "β", "😀", "\r\n", "\n"];
        let mut seed = 0x00C0_FFEE_u64;
        for _ in 0..200 {
            let mut text = String::new();
            for _ in 0..20 {
                seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                let index = usize::try_from(seed % u64::try_from(atoms.len()).unwrap()).unwrap();
                text.push_str(atoms[index]);
            }
            let index = LineIndex::new(&text);
            for (offset, _) in text
                .char_indices()
                .chain(std::iter::once((text.len(), '\0')))
            {
                let position = index.position(&text, offset).unwrap();
                assert_eq!(
                    index.byte_offset(&text, position),
                    Some(offset.min(index.line_ends[position.line as usize]))
                );
            }
        }
    }

    #[test]
    fn concurrent_reads_and_serialized_writes_are_consistent() {
        let id = SourceId::new(3);
        let store = shared_document_store();
        store.write().unwrap().open(id, String::new(), 0).unwrap();
        let workers: Vec<_> = (1..=32)
            .map(|version| {
                let store = store.clone();
                std::thread::spawn(move || {
                    let mut guard = store.write().unwrap();
                    if guard.get(id).unwrap().version < version {
                        guard
                            .change(
                                id,
                                version,
                                &[TextChange {
                                    range: None,
                                    range_length: None,
                                    text: version.to_string(),
                                }],
                            )
                            .unwrap();
                    }
                })
            })
            .collect();
        for worker in workers {
            worker.join().unwrap();
        }
        let guard = store.read().unwrap();
        let document = guard.get(id).unwrap();
        assert_eq!(document.text, document.version.to_string());
    }
}
