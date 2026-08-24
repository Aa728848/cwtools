#![forbid(unsafe_code)]

/// A source identifier is meaningful only inside its owning session.
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

/// Zero-based LSP position measured in UTF-16 code units.
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

/// Immutable line starts for exact byte/UTF-16 conversion.
#[derive(Clone, Debug)]
pub struct LineIndex {
    line_starts: Vec<usize>,
}

impl LineIndex {
    #[must_use]
    pub fn new(text: &str) -> Self {
        let mut line_starts = vec![0];
        for (offset, byte) in text.bytes().enumerate() {
            if byte == b'\n' {
                line_starts.push(offset + 1);
            }
        }
        Self { line_starts }
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
        let line_start = self.line_starts[line];
        let character = text[line_start..byte_offset].encode_utf16().count();
        Some(Position {
            line: u32::try_from(line).ok()?,
            character: u32::try_from(character).ok()?,
        })
    }

    #[must_use]
    pub fn byte_offset(&self, text: &str, position: Position) -> Option<usize> {
        let line = usize::try_from(position.line).ok()?;
        let start = *self.line_starts.get(line)?;
        let end = self
            .line_starts
            .get(line + 1)
            .copied()
            .unwrap_or(text.len());
        let target = usize::try_from(position.character).ok()?;
        let mut utf16 = 0;
        for (relative, character) in text[start..end].char_indices() {
            if utf16 == target {
                return Some(start + relative);
            }
            utf16 += character.len_utf16();
            if utf16 > target {
                return None;
            }
        }
        (utf16 == target).then_some(end)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_utf16_and_crlf_positions() {
        let text = "a😀\r\nβ";
        let index = LineIndex::new(text);
        for offset in text
            .char_indices()
            .map(|(offset, _)| offset)
            .chain([text.len()])
        {
            let position = index.position(text, offset).unwrap();
            assert_eq!(index.byte_offset(text, position), Some(offset));
        }
        assert_eq!(
            index.position(text, "a😀".len()),
            Some(Position {
                line: 0,
                character: 3
            })
        );
    }

    #[test]
    fn rejects_position_inside_surrogate_pair() {
        let text = "😀";
        assert_eq!(
            LineIndex::new(text).byte_offset(
                text,
                Position {
                    line: 0,
                    character: 1
                }
            ),
            None
        );
    }
}
