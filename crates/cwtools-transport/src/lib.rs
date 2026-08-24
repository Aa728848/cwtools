#![forbid(unsafe_code)]

use std::fmt;
use std::io::{self, BufRead, Write};

use cwtools_protocol::{DEFAULT_MAX_FRAME_BYTES, DEFAULT_MAX_HEADER_BYTES};

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_header_bytes: usize,
    pub max_frame_bytes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_header_bytes: DEFAULT_MAX_HEADER_BYTES,
            max_frame_bytes: DEFAULT_MAX_FRAME_BYTES,
        }
    }
}

#[derive(Debug)]
pub enum FrameError {
    Io(io::Error),
    Eof,
    HeaderTooLarge,
    InvalidHeader,
    DuplicateContentLength,
    FrameTooLarge { length: usize, maximum: usize },
    TruncatedPayload,
    InvalidUtf8,
}

impl fmt::Display for FrameError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}
impl std::error::Error for FrameError {}
impl From<io::Error> for FrameError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

/// Reads one strict Content-Length framed UTF-8 payload.
///
/// # Errors
/// Returns [`FrameError`] for I/O, malformed headers, limit violations, truncation, or invalid UTF-8.
pub fn read_frame<R: BufRead>(reader: &mut R, limits: Limits) -> Result<String, FrameError> {
    let mut header_bytes: usize = 0;
    let mut content_length = None;
    loop {
        let mut line = Vec::new();
        let read = reader.read_until(b'\n', &mut line)?;
        if read == 0 {
            return if header_bytes == 0 {
                Err(FrameError::Eof)
            } else {
                Err(FrameError::InvalidHeader)
            };
        }
        header_bytes = header_bytes
            .checked_add(read)
            .ok_or(FrameError::HeaderTooLarge)?;
        if header_bytes > limits.max_header_bytes {
            return Err(FrameError::HeaderTooLarge);
        }
        if !line.ends_with(b"\r\n") {
            return Err(FrameError::InvalidHeader);
        }
        if line == b"\r\n" {
            break;
        }
        let line =
            std::str::from_utf8(&line[..line.len() - 2]).map_err(|_| FrameError::InvalidHeader)?;
        let (name, value) = line.split_once(':').ok_or(FrameError::InvalidHeader)?;
        if name.eq_ignore_ascii_case("Content-Length") {
            if content_length.is_some() {
                return Err(FrameError::DuplicateContentLength);
            }
            let length = value
                .trim()
                .parse::<usize>()
                .map_err(|_| FrameError::InvalidHeader)?;
            if length > limits.max_frame_bytes {
                return Err(FrameError::FrameTooLarge {
                    length,
                    maximum: limits.max_frame_bytes,
                });
            }
            content_length = Some(length);
        }
    }
    let length = content_length.ok_or(FrameError::InvalidHeader)?;
    let mut payload = vec![0; length];
    if let Err(error) = reader.read_exact(&mut payload) {
        return if error.kind() == io::ErrorKind::UnexpectedEof {
            Err(FrameError::TruncatedPayload)
        } else {
            Err(FrameError::Io(error))
        };
    }
    String::from_utf8(payload).map_err(|_| FrameError::InvalidUtf8)
}

/// Writes and flushes one strict Content-Length framed payload.
///
/// # Errors
/// Returns [`FrameError`] for I/O or frame-limit violations.
pub fn write_frame<W: Write>(
    writer: &mut W,
    payload: &str,
    limits: Limits,
) -> Result<(), FrameError> {
    if payload.len() > limits.max_frame_bytes {
        return Err(FrameError::FrameTooLarge {
            length: payload.len(),
            maximum: limits.max_frame_bytes,
        });
    }
    write!(writer, "Content-Length: {}\r\n\r\n", payload.len())?;
    writer.write_all(payload.as_bytes())?;
    writer.flush()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{BufReader, Cursor};

    #[test]
    fn exact_round_trip() {
        let mut bytes = Vec::new();
        write_frame(&mut bytes, "{\"x\":\"😀\"}", Limits::default()).unwrap();
        assert_eq!(
            read_frame(&mut BufReader::new(Cursor::new(bytes)), Limits::default()).unwrap(),
            "{\"x\":\"😀\"}"
        );
    }

    #[test]
    fn rejects_duplicate_and_oversized_lengths() {
        let duplicate = b"Content-Length: 1\r\nContent-Length: 1\r\n\r\nx";
        assert!(matches!(
            read_frame(&mut BufReader::new(&duplicate[..]), Limits::default()),
            Err(FrameError::DuplicateContentLength)
        ));
        let oversized = b"Content-Length: 2\r\n\r\n{}";
        assert!(matches!(
            read_frame(
                &mut BufReader::new(&oversized[..]),
                Limits {
                    max_header_bytes: 100,
                    max_frame_bytes: 1
                }
            ),
            Err(FrameError::FrameTooLarge { .. })
        ));
    }

    #[test]
    fn rejects_bad_terminator_truncation_and_utf8() {
        assert!(matches!(
            read_frame(
                &mut BufReader::new(&b"Content-Length: 0\n\n"[..]),
                Limits::default()
            ),
            Err(FrameError::InvalidHeader)
        ));
        assert!(matches!(
            read_frame(
                &mut BufReader::new(&b"Content-Length: 2\r\n\r\nx"[..]),
                Limits::default()
            ),
            Err(FrameError::TruncatedPayload)
        ));
        assert!(matches!(
            read_frame(
                &mut BufReader::new(&b"Content-Length: 1\r\n\r\n\xff"[..]),
                Limits::default()
            ),
            Err(FrameError::InvalidUtf8)
        ));
    }
}
