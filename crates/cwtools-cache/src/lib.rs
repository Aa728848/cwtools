#![forbid(unsafe_code)]
//! Bounded, versioned, corruption-tolerant cache envelopes.

use flate2::Compression;
use flate2::read::ZlibDecoder;
use flate2::write::ZlibEncoder;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;
use std::fmt;
use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

pub const CACHE_MAGIC: [u8; 8] = *b"CWTCACHE";
pub const CACHE_SCHEMA_VERSION: u16 = 1;
pub const CACHE_HEADER_BYTES: usize = 54;
pub const MAX_GAME_ID_BYTES: usize = 128;
pub const DEFAULT_MAX_PAYLOAD_BYTES: usize = 64 * 1024 * 1024;
pub const DEFAULT_MAX_COMPRESSED_BYTES: usize = 64 * 1024 * 1024;

#[derive(
    Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize,
)]
#[serde(transparent)]
pub struct Fingerprint(pub u64);

impl Fingerprint {
    #[must_use]
    pub const fn new(value: u64) -> Self {
        Self(value)
    }

    #[must_use]
    pub fn to_hex(self) -> String {
        format!("{:016x}", self.0)
    }
}

impl fmt::Display for Fingerprint {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:016x}", self.0)
    }
}

/// Stable FNV-1a identity hashing. This is not an authentication primitive.
#[must_use]
pub fn fingerprint_bytes(bytes: &[u8]) -> Fingerprint {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0100_0000_01b3);
    }
    Fingerprint(hash)
}

#[must_use]
pub fn fingerprint_text(text: &str) -> Fingerprint {
    fingerprint_bytes(text.as_bytes())
}

/// Hash sorted logical path and content pairs, independent of input order.
#[must_use]
pub fn fingerprint_sources<I, P, T>(sources: I) -> Fingerprint
where
    I: IntoIterator<Item = (P, T)>,
    P: AsRef<str>,
    T: AsRef<str>,
{
    let mut values = sources
        .into_iter()
        .map(|(path, text)| (path.as_ref().replace('\\', "/"), text.as_ref().to_owned()))
        .collect::<Vec<_>>();
    values.sort();
    let mut bytes = Vec::new();
    for (path, text) in values {
        let path_len = u64::try_from(path.len()).unwrap_or(u64::MAX);
        let text_len = u64::try_from(text.len()).unwrap_or(u64::MAX);
        bytes.extend_from_slice(&path_len.to_le_bytes());
        bytes.extend_from_slice(path.as_bytes());
        bytes.extend_from_slice(&text_len.to_le_bytes());
        bytes.extend_from_slice(text.as_bytes());
    }
    fingerprint_bytes(&bytes)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CacheKey {
    pub game_id: String,
    pub rules_hash: Fingerprint,
    pub source_fingerprint: Fingerprint,
}

impl CacheKey {
    /// Creates a validated cache identity.
    ///
    /// # Errors
    /// Returns [`CacheError::InvalidGameId`] for empty, non-ASCII, or oversized ids.
    pub fn new(
        game_id: impl Into<String>,
        rules_hash: Fingerprint,
        source_fingerprint: Fingerprint,
    ) -> Result<Self, CacheError> {
        let game_id = game_id.into();
        if game_id.is_empty() || game_id.len() > MAX_GAME_ID_BYTES || !game_id.is_ascii() {
            return Err(CacheError::InvalidGameId);
        }
        Ok(Self {
            game_id,
            rules_hash,
            source_fingerprint,
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CompressionKind {
    None,
    Deflate,
}

impl CompressionKind {
    const fn byte(self) -> u8 {
        match self {
            Self::None => 0,
            Self::Deflate => 1,
        }
    }

    fn from_byte(byte: u8) -> Result<Self, CacheError> {
        match byte {
            0 => Ok(Self::None),
            1 => Ok(Self::Deflate),
            value => Err(CacheError::UnsupportedCompression(value)),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CacheMetadata {
    pub magic: [u8; 8],
    pub schema_version: u16,
    pub game_id: String,
    pub rules_hash: Fingerprint,
    pub source_fingerprint: Fingerprint,
    pub compression: CompressionKind,
    pub uncompressed_bytes: usize,
    pub stored_bytes: usize,
    pub checksum: Fingerprint,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CacheLimits {
    pub max_payload_bytes: usize,
    pub max_compressed_bytes: usize,
    pub max_game_id_bytes: usize,
}

impl Default for CacheLimits {
    fn default() -> Self {
        Self {
            max_payload_bytes: DEFAULT_MAX_PAYLOAD_BYTES,
            max_compressed_bytes: DEFAULT_MAX_COMPRESSED_BYTES,
            max_game_id_bytes: MAX_GAME_ID_BYTES,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CacheMissReason {
    NotFound,
    Io,
    InvalidMagic,
    UnsupportedSchema(u16),
    Truncated,
    InvalidHeader,
    InvalidGameId,
    GameMismatch { expected: String, actual: String },
    RulesMismatch,
    SourceMismatch,
    UnsupportedCompression(u8),
    PayloadTooLarge,
    DecompressionFailed,
    ChecksumMismatch,
    DeserializeFailed,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CacheRead<T> {
    pub value: Option<T>,
    pub metadata: Option<CacheMetadata>,
    pub miss: Option<CacheMissReason>,
}

impl<T> CacheRead<T> {
    #[must_use]
    pub fn hit(value: T, metadata: CacheMetadata) -> Self {
        Self {
            value: Some(value),
            metadata: Some(metadata),
            miss: None,
        }
    }

    #[must_use]
    pub fn miss(reason: CacheMissReason) -> Self {
        Self {
            value: None,
            metadata: None,
            miss: Some(reason),
        }
    }

    #[must_use]
    pub fn is_hit(&self) -> bool {
        self.value.is_some()
    }
}

#[derive(Debug)]
pub enum CacheError {
    Io(io::Error),
    InvalidGameId,
    PayloadTooLarge { bytes: usize, limit: usize },
    CompressedPayloadTooLarge { bytes: usize, limit: usize },
    Compression(io::Error),
    InvalidHeader,
    UnsupportedCompression(u8),
}

impl fmt::Display for CacheError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "cache I/O failed: {error}"),
            Self::InvalidGameId => {
                write!(formatter, "cache game id is empty, non-ASCII, or too long")
            }
            Self::PayloadTooLarge { bytes, limit } => {
                write!(
                    formatter,
                    "cache payload has {bytes} bytes; limit is {limit}"
                )
            }
            Self::CompressedPayloadTooLarge { bytes, limit } => {
                write!(
                    formatter,
                    "compressed cache payload has {bytes} bytes; limit is {limit}"
                )
            }
            Self::Compression(error) => write!(formatter, "cache compression failed: {error}"),
            Self::InvalidHeader => write!(formatter, "cache header cannot be represented"),
            Self::UnsupportedCompression(value) => {
                write!(formatter, "unsupported compression {value}")
            }
        }
    }
}

impl std::error::Error for CacheError {}

impl From<io::Error> for CacheError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

#[derive(Clone, Debug)]
pub struct CacheStore {
    path: PathBuf,
    limits: CacheLimits,
}

impl CacheStore {
    #[must_use]
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self {
            path: path.into(),
            limits: CacheLimits::default(),
        }
    }

    #[must_use]
    pub fn with_limits(path: impl Into<PathBuf>, limits: CacheLimits) -> Self {
        Self {
            path: path.into(),
            limits,
        }
    }

    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Atomically writes one bounded cache envelope.
    ///
    /// # Errors
    /// Returns an error for I/O, invalid identity, compression, or size limits.
    pub fn write_bytes(&self, key: &CacheKey, payload: &[u8]) -> Result<CacheMetadata, CacheError> {
        if payload.len() > self.limits.max_payload_bytes {
            return Err(CacheError::PayloadTooLarge {
                bytes: payload.len(),
                limit: self.limits.max_payload_bytes,
            });
        }
        if key.game_id.len() > self.limits.max_game_id_bytes
            || key.game_id.len() > u16::MAX as usize
        {
            return Err(CacheError::InvalidGameId);
        }
        let checksum = fingerprint_bytes(payload);
        let (compression, stored) = compress_payload(payload)?;
        if stored.len() > self.limits.max_compressed_bytes {
            return Err(CacheError::CompressedPayloadTooLarge {
                bytes: stored.len(),
                limit: self.limits.max_compressed_bytes,
            });
        }
        let metadata = CacheMetadata {
            magic: CACHE_MAGIC,
            schema_version: CACHE_SCHEMA_VERSION,
            game_id: key.game_id.clone(),
            rules_hash: key.rules_hash,
            source_fingerprint: key.source_fingerprint,
            compression,
            uncompressed_bytes: payload.len(),
            stored_bytes: stored.len(),
            checksum,
        };
        let encoded = encode_envelope(&metadata, &stored)?;
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)?;
        }
        let temporary = self
            .path
            .with_extension(format!("cache-tmp-{}", std::process::id()));
        fs::write(&temporary, encoded)?;
        if let Err(first) = fs::rename(&temporary, &self.path) {
            if self.path.exists() {
                if let Err(error) = fs::copy(&temporary, &self.path) {
                    let _ = fs::remove_file(&temporary);
                    return Err(CacheError::Io(error));
                }
                fs::remove_file(&temporary)?;
            } else {
                let _ = fs::remove_file(&temporary);
                return Err(CacheError::Io(first));
            }
        }
        Ok(metadata)
    }

    /// Serializes and atomically writes one bounded JSON cache value.
    ///
    /// # Errors
    /// Returns an error when serialization or envelope persistence fails.
    pub fn write_json<T: Serialize>(
        &self,
        key: &CacheKey,
        value: &T,
    ) -> Result<CacheMetadata, CacheError> {
        let bytes = serde_json::to_vec(value).map_err(|_| CacheError::InvalidHeader)?;
        self.write_bytes(key, &bytes)
    }

    /// Every invalid, old, corrupt, or mismatched cache is a safe miss.
    #[must_use]
    pub fn read_bytes(&self, expected: &CacheKey) -> CacheRead<Vec<u8>> {
        let bytes = match fs::read(&self.path) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                return CacheRead::miss(CacheMissReason::NotFound);
            }
            Err(_) => return CacheRead::miss(CacheMissReason::Io),
        };
        let (metadata, stored) = match decode_envelope(&bytes, self.limits) {
            Ok(value) => value,
            Err(reason) => return CacheRead::miss(reason),
        };
        if metadata.game_id != expected.game_id {
            return CacheRead::miss(CacheMissReason::GameMismatch {
                expected: expected.game_id.clone(),
                actual: metadata.game_id,
            });
        }
        if metadata.rules_hash != expected.rules_hash {
            return CacheRead::miss(CacheMissReason::RulesMismatch);
        }
        if metadata.source_fingerprint != expected.source_fingerprint {
            return CacheRead::miss(CacheMissReason::SourceMismatch);
        }
        match decompress_payload(
            metadata.compression,
            &stored,
            metadata.uncompressed_bytes,
            self.limits.max_payload_bytes,
        ) {
            Ok(payload) if fingerprint_bytes(&payload) == metadata.checksum => {
                CacheRead::hit(payload, metadata)
            }
            Ok(_) => CacheRead::miss(CacheMissReason::ChecksumMismatch),
            Err(reason) => CacheRead::miss(reason),
        }
    }

    #[must_use]
    pub fn read_json<T: DeserializeOwned>(&self, expected: &CacheKey) -> CacheRead<T> {
        let raw = self.read_bytes(expected);
        let Some(metadata) = raw.metadata else {
            return CacheRead::miss(raw.miss.unwrap_or(CacheMissReason::Io));
        };
        let Some(bytes) = raw.value else {
            return CacheRead::miss(raw.miss.unwrap_or(CacheMissReason::Io));
        };
        match serde_json::from_slice(&bytes) {
            Ok(value) => CacheRead::hit(value, metadata),
            Err(_) => CacheRead::miss(CacheMissReason::DeserializeFailed),
        }
    }

    #[must_use]
    pub fn inspect(&self) -> CacheRead<()> {
        let bytes = match fs::read(&self.path) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                return CacheRead::miss(CacheMissReason::NotFound);
            }
            Err(_) => return CacheRead::miss(CacheMissReason::Io),
        };
        match decode_envelope(&bytes, self.limits) {
            Ok((metadata, _)) => CacheRead::hit((), metadata),
            Err(reason) => CacheRead::miss(reason),
        }
    }
}

fn compress_payload(payload: &[u8]) -> Result<(CompressionKind, Vec<u8>), CacheError> {
    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::fast());
    encoder
        .write_all(payload)
        .map_err(CacheError::Compression)?;
    let compressed = encoder.finish().map_err(CacheError::Compression)?;
    if compressed.len() < payload.len() {
        Ok((CompressionKind::Deflate, compressed))
    } else {
        Ok((CompressionKind::None, payload.to_vec()))
    }
}

fn decompress_payload(
    kind: CompressionKind,
    stored: &[u8],
    expected: usize,
    limit: usize,
) -> Result<Vec<u8>, CacheMissReason> {
    if expected > limit {
        return Err(CacheMissReason::PayloadTooLarge);
    }
    match kind {
        CompressionKind::None => {
            if stored.len() != expected {
                return Err(CacheMissReason::Truncated);
            }
            Ok(stored.to_vec())
        }
        CompressionKind::Deflate => {
            let decoder = ZlibDecoder::new(stored);
            let mut output = Vec::with_capacity(expected.min(limit));
            decoder
                .take((limit as u64).saturating_add(1))
                .read_to_end(&mut output)
                .map_err(|_| CacheMissReason::DecompressionFailed)?;
            if output.len() != expected || output.len() > limit {
                Err(CacheMissReason::DecompressionFailed)
            } else {
                Ok(output)
            }
        }
    }
}

fn encode_envelope(metadata: &CacheMetadata, stored: &[u8]) -> Result<Vec<u8>, CacheError> {
    let game_len = u16::try_from(metadata.game_id.len()).map_err(|_| CacheError::InvalidHeader)?;
    let uncompressed =
        u64::try_from(metadata.uncompressed_bytes).map_err(|_| CacheError::InvalidHeader)?;
    let stored_len = u64::try_from(stored.len()).map_err(|_| CacheError::InvalidHeader)?;
    let mut bytes = Vec::with_capacity(CACHE_HEADER_BYTES + metadata.game_id.len() + stored.len());
    bytes.extend_from_slice(&metadata.magic);
    bytes.extend_from_slice(&metadata.schema_version.to_le_bytes());
    bytes.push(metadata.compression.byte());
    bytes.push(0);
    bytes.extend_from_slice(&game_len.to_le_bytes());
    bytes.extend_from_slice(&metadata.rules_hash.0.to_le_bytes());
    bytes.extend_from_slice(&metadata.source_fingerprint.0.to_le_bytes());
    bytes.extend_from_slice(&uncompressed.to_le_bytes());
    bytes.extend_from_slice(&stored_len.to_le_bytes());
    bytes.extend_from_slice(&metadata.checksum.0.to_le_bytes());
    bytes.extend_from_slice(metadata.game_id.as_bytes());
    bytes.extend_from_slice(stored);
    Ok(bytes)
}

fn decode_envelope(
    bytes: &[u8],
    limits: CacheLimits,
) -> Result<(CacheMetadata, Vec<u8>), CacheMissReason> {
    if bytes.len() < CACHE_HEADER_BYTES {
        return Err(CacheMissReason::Truncated);
    }
    if bytes[..8] != CACHE_MAGIC {
        return Err(CacheMissReason::InvalidMagic);
    }
    let schema_version = u16::from_le_bytes([bytes[8], bytes[9]]);
    if schema_version != CACHE_SCHEMA_VERSION {
        return Err(CacheMissReason::UnsupportedSchema(schema_version));
    }
    let compression = CompressionKind::from_byte(bytes[10]).map_err(|error| match error {
        CacheError::UnsupportedCompression(value) => CacheMissReason::UnsupportedCompression(value),
        _ => CacheMissReason::InvalidHeader,
    })?;
    let game_len = usize::from(u16::from_le_bytes([bytes[12], bytes[13]]));
    if game_len == 0 || game_len > limits.max_game_id_bytes {
        return Err(CacheMissReason::InvalidGameId);
    }
    let rules_hash = Fingerprint(u64::from_le_bytes(
        bytes[14..22]
            .try_into()
            .map_err(|_| CacheMissReason::InvalidHeader)?,
    ));
    let source_fingerprint = Fingerprint(u64::from_le_bytes(
        bytes[22..30]
            .try_into()
            .map_err(|_| CacheMissReason::InvalidHeader)?,
    ));
    let uncompressed_bytes_u64 = u64::from_le_bytes(
        bytes[30..38]
            .try_into()
            .map_err(|_| CacheMissReason::InvalidHeader)?,
    );
    let stored_bytes_u64 = u64::from_le_bytes(
        bytes[38..46]
            .try_into()
            .map_err(|_| CacheMissReason::InvalidHeader)?,
    );
    let checksum = Fingerprint(u64::from_le_bytes(
        bytes[46..54]
            .try_into()
            .map_err(|_| CacheMissReason::InvalidHeader)?,
    ));
    let uncompressed_bytes =
        usize::try_from(uncompressed_bytes_u64).map_err(|_| CacheMissReason::PayloadTooLarge)?;
    let stored_bytes =
        usize::try_from(stored_bytes_u64).map_err(|_| CacheMissReason::PayloadTooLarge)?;
    if uncompressed_bytes > limits.max_payload_bytes || stored_bytes > limits.max_compressed_bytes {
        return Err(CacheMissReason::PayloadTooLarge);
    }
    let payload_start = CACHE_HEADER_BYTES
        .checked_add(game_len)
        .ok_or(CacheMissReason::InvalidHeader)?;
    let payload_end = payload_start
        .checked_add(stored_bytes)
        .ok_or(CacheMissReason::InvalidHeader)?;
    if payload_end != bytes.len() {
        return Err(CacheMissReason::Truncated);
    }
    let game_id = std::str::from_utf8(&bytes[CACHE_HEADER_BYTES..payload_start])
        .map_err(|_| CacheMissReason::InvalidGameId)?
        .to_owned();
    if !game_id.is_ascii() {
        return Err(CacheMissReason::InvalidGameId);
    }
    let metadata = CacheMetadata {
        magic: CACHE_MAGIC,
        schema_version,
        game_id,
        rules_hash,
        source_fingerprint,
        compression,
        uncompressed_bytes,
        stored_bytes,
        checksum,
    };
    Ok((metadata, bytes[payload_start..payload_end].to_vec()))
}

#[derive(Clone, Debug)]
struct MemoryEntry<K, V> {
    key: K,
    value: V,
}

/// Deterministic LRU cache with an explicit capacity.
#[derive(Clone, Debug)]
pub struct BoundedMemoryCache<K, V> {
    capacity: usize,
    entries: VecDeque<MemoryEntry<K, V>>,
}

impl<K: Eq, V> BoundedMemoryCache<K, V> {
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            entries: VecDeque::new(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn clear(&mut self) {
        self.entries.clear();
    }

    pub fn insert(&mut self, key: K, value: V) {
        if self.capacity == 0 {
            return;
        }
        if let Some(index) = self.entries.iter().position(|entry| entry.key == key) {
            let _ = self.entries.remove(index);
        }
        self.entries.push_front(MemoryEntry { key, value });
        while self.entries.len() > self.capacity {
            let _ = self.entries.pop_back();
        }
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        let index = self.entries.iter().position(|entry| &entry.key == key)?;
        let entry = self.entries.remove(index)?;
        self.entries.push_front(entry);
        self.entries.front().map(|entry| &entry.value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp_path(name: &str) -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        std::env::temp_dir().join(format!("cwtools-cache-{name}-{nonce}.bin"))
    }

    fn key(source: &str) -> CacheKey {
        CacheKey::new("stellaris", Fingerprint::new(7), fingerprint_text(source)).unwrap()
    }

    #[test]
    fn round_trip_compressed_json_and_identity() {
        let path = temp_path("round-trip");
        let store = CacheStore::new(&path);
        let payload = vec!["same text ".repeat(1000), "second".to_owned()];
        let metadata = store.write_json(&key("source"), &payload).unwrap();
        assert_eq!(metadata.magic, CACHE_MAGIC);
        assert!(store.read_json::<Vec<String>>(&key("source")).is_hit());
        assert!(!store.read_json::<Vec<String>>(&key("other")).is_hit());
        let _ = fs::remove_file(path);
    }

    #[test]
    fn corrupt_and_old_files_are_misses() {
        let path = temp_path("corrupt");
        let store = CacheStore::new(&path);
        fs::write(&path, b"not a cache").unwrap();
        assert_eq!(store.inspect().miss, Some(CacheMissReason::Truncated));
        let mut old = vec![0u8; CACHE_HEADER_BYTES];
        old[..8].copy_from_slice(&CACHE_MAGIC);
        old[8..10].copy_from_slice(&0u16.to_le_bytes());
        fs::write(&path, old).unwrap();
        assert_eq!(
            store.inspect().miss,
            Some(CacheMissReason::UnsupportedSchema(0))
        );
        let _ = fs::remove_file(path);
    }

    #[test]
    fn bounded_memory_cache_evicts_lru() {
        let mut cache = BoundedMemoryCache::new(2);
        cache.insert("a", 1);
        cache.insert("b", 2);
        assert_eq!(cache.get(&"a"), Some(&1));
        cache.insert("c", 3);
        assert!(cache.get(&"b").is_none());
        assert_eq!(cache.get(&"a"), Some(&1));
    }

    #[test]
    fn source_fingerprint_is_order_independent() {
        let left = fingerprint_sources([("b", "2"), ("a", "1")]);
        let right = fingerprint_sources([("a", "1"), ("b", "2")]);
        assert_eq!(left, right);
    }
}
