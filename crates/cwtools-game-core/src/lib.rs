#![forbid(unsafe_code)]
#![allow(
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::double_must_use,
    clippy::must_use_candidate,
    clippy::manual_let_else,
    clippy::unnecessary_lazy_evaluations,
    clippy::cast_possible_truncation
)]
//! Game/session facade over syntax, rules, scopes, localisation, and workspace snapshots.

use cwtools_cache::{
    BoundedMemoryCache, CacheKey, CacheMetadata, CacheRead, CacheStore, Fingerprint,
    fingerprint_sources,
};
use cwtools_rule_ir::Document;
use cwtools_rules_engine::{RuleCatalog, ScopeUniverse};
use cwtools_scopes::{
    ScopeContext, ValueScopeCatalog,
    game::{self, GameScopeFamily},
};
use cwtools_script_syntax::{ScriptEncoding, decode_script_bytes};
use cwtools_workspace::{
    FullSnapshot, GameComputedData, Overwrite, SnapshotLimits, SnapshotSource,
    compute_full_snapshot, compute_rule_game_data, compute_snapshot_diagnostics,
    incremental::{Change, IncrementalStore},
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::PathBuf;

pub const MAX_LOCALISATION_FILES: usize = 100_000;
pub const MAX_LOCALISATION_ENTRIES: usize = 1_000_000;
pub const MAX_LOCALISATION_VALUE_BYTES: usize = 1024 * 1024;
pub const MAX_RULE_DOCUMENTS: usize = 100_000;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum GameId {
    Generic,
    Custom,
    Jomini,
    Ck2,
    Ck3,
    Eu4,
    Eu5,
    Hoi4,
    Imperator,
    Vic2,
    Vic3,
    Stellaris,
    CwtOnly,
}

impl GameId {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Generic => "generic",
            Self::Custom => "custom",
            Self::Jomini => "jomini",
            Self::Ck2 => "ck2",
            Self::Ck3 => "ck3",
            Self::Eu4 => "eu4",
            Self::Eu5 => "eu5",
            Self::Hoi4 => "hoi4",
            Self::Imperator => "imperator",
            Self::Vic2 => "vic2",
            Self::Vic3 => "vic3",
            Self::Stellaris => "stellaris",
            Self::CwtOnly => "cwt-only",
        }
    }

    #[must_use]
    pub const fn is_cwt_only(self) -> bool {
        matches!(self, Self::CwtOnly)
    }

    #[must_use]
    pub const fn is_jomini(self) -> bool {
        matches!(
            self,
            Self::Jomini | Self::Ck3 | Self::Eu5 | Self::Imperator | Self::Vic3
        )
    }

    #[must_use]
    pub const fn scope_family(self) -> Option<GameScopeFamily> {
        match self {
            Self::Ck2 => Some(GameScopeFamily::Ck2),
            Self::Ck3 => Some(GameScopeFamily::Ck3),
            Self::Eu4 => Some(GameScopeFamily::Eu4),
            Self::Eu5 => Some(GameScopeFamily::Eu5),
            Self::Hoi4 => Some(GameScopeFamily::Hoi4),
            Self::Imperator => Some(GameScopeFamily::Imperator),
            Self::Vic2 => Some(GameScopeFamily::Vic2),
            Self::Vic3 => Some(GameScopeFamily::Vic3),
            Self::Stellaris => Some(GameScopeFamily::Stellaris),
            Self::Generic | Self::Custom | Self::Jomini | Self::CwtOnly => None,
        }
    }
}

impl fmt::Display for GameId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum LocalisationFormat {
    Yaml,
    CsvSemicolon,
    Vic2Csv,
    None,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum TextEncoding {
    Utf8,
    Utf8Bom,
    Windows1252,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum LocalisationLanguage {
    English,
    French,
    German,
    Spanish,
    Russian,
    Polish,
    Portuguese,
    Chinese,
    Japanese,
    Korean,
    Turkish,
    Italian,
    Default,
}

impl LocalisationLanguage {
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::English => "l_english",
            Self::French => "l_french",
            Self::German => "l_german",
            Self::Spanish => "l_spanish",
            Self::Russian => "l_russian",
            Self::Polish => "l_polish",
            Self::Portuguese => "l_braz_por",
            Self::Chinese => "l_simp_chinese",
            Self::Japanese => "l_japanese",
            Self::Korean => "l_korean",
            Self::Turkish => "l_turkish",
            Self::Italian => "l_italian",
            Self::Default => "l_default",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GameProfile {
    pub id: GameId,
    pub display_name: String,
    pub is_jomini: bool,
    pub is_cwt_only: bool,
    pub localisation: LocalisationProfile,
    pub script_folders: Vec<String>,
    pub scope_family: Option<GameScopeFamily>,
    pub supported_languages: Vec<LocalisationLanguage>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct LocalisationProfile {
    pub format: LocalisationFormat,
    pub encoding: TextEncoding,
    pub extensions: Vec<String>,
    pub directories: Vec<String>,
    pub default_language: LocalisationLanguage,
}

fn yaml_profile(id: GameId, name: &str) -> GameProfile {
    GameProfile {
        id,
        display_name: name.to_owned(),
        is_jomini: id.is_jomini(),
        is_cwt_only: id.is_cwt_only(),
        localisation: LocalisationProfile {
            format: LocalisationFormat::Yaml,
            encoding: TextEncoding::Utf8Bom,
            extensions: vec!["yml".to_owned(), "yaml".to_owned()],
            directories: vec!["localisation".to_owned(), "localization".to_owned()],
            default_language: LocalisationLanguage::English,
        },
        script_folders: vec![
            "common".to_owned(),
            "events".to_owned(),
            "history".to_owned(),
            "decisions".to_owned(),
        ],
        scope_family: id.scope_family(),
        supported_languages: vec![
            LocalisationLanguage::English,
            LocalisationLanguage::French,
            LocalisationLanguage::German,
            LocalisationLanguage::Spanish,
            LocalisationLanguage::Russian,
        ],
    }
}

#[must_use]
pub fn game_profile(id: GameId) -> GameProfile {
    let mut profile = match id {
        GameId::Ck2 | GameId::Vic2 => GameProfile {
            localisation: LocalisationProfile {
                format: if id == GameId::Vic2 {
                    LocalisationFormat::Vic2Csv
                } else {
                    LocalisationFormat::CsvSemicolon
                },
                encoding: TextEncoding::Windows1252,
                extensions: vec!["csv".to_owned()],
                directories: vec!["localisation".to_owned(), "localization".to_owned()],
                default_language: LocalisationLanguage::English,
            },
            ..yaml_profile(
                id,
                if id == GameId::Ck2 {
                    "Crusader Kings II"
                } else {
                    "Victoria II"
                },
            )
        },
        GameId::CwtOnly => GameProfile {
            localisation: LocalisationProfile {
                format: LocalisationFormat::None,
                encoding: TextEncoding::Utf8,
                extensions: Vec::new(),
                directories: Vec::new(),
                default_language: LocalisationLanguage::Default,
            },
            script_folders: vec!["common".to_owned()],
            ..yaml_profile(id, "CWT rules")
        },
        GameId::Generic => yaml_profile(id, "Generic Paradox"),
        GameId::Custom => yaml_profile(id, "Custom"),
        GameId::Jomini => yaml_profile(id, "Jomini"),
        GameId::Ck3 => yaml_profile(id, "Crusader Kings III"),
        GameId::Eu4 => yaml_profile(id, "Europa Universalis IV"),
        GameId::Eu5 => yaml_profile(id, "Europa Universalis V"),
        GameId::Hoi4 => yaml_profile(id, "Hearts of Iron IV"),
        GameId::Imperator => yaml_profile(id, "Imperator: Rome"),
        GameId::Vic3 => yaml_profile(id, "Victoria 3"),
        GameId::Stellaris => yaml_profile(id, "Stellaris"),
    };
    if id == GameId::Stellaris {
        profile.script_folders.extend([
            "common/scripted_triggers".to_owned(),
            "common/scripted_effects".to_owned(),
        ]);
    }
    profile
}

#[must_use]
pub fn all_game_profiles() -> Vec<GameProfile> {
    [
        GameId::Generic,
        GameId::Custom,
        GameId::Jomini,
        GameId::Ck2,
        GameId::Ck3,
        GameId::Eu4,
        GameId::Eu5,
        GameId::Hoi4,
        GameId::Imperator,
        GameId::Vic2,
        GameId::Vic3,
        GameId::Stellaris,
        GameId::CwtOnly,
    ]
    .into_iter()
    .map(game_profile)
    .collect()
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct LocalisationEntry {
    pub key: String,
    pub value: String,
    pub language: LocalisationLanguage,
    pub path: String,
    pub line: usize,
    pub column: usize,
    pub version: Option<u8>,
    pub comment: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct LocalisationFile {
    pub path: String,
    pub language: LocalisationLanguage,
    pub encoding: TextEncoding,
    pub has_bom: bool,
    pub entries: Vec<LocalisationEntry>,
    pub errors: Vec<LocalisationDiagnostic>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct LocalisationDiagnostic {
    pub code: String,
    pub message: String,
    pub path: String,
    pub line: usize,
    pub column: usize,
    pub key: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct LocalisationIndex {
    pub files: Vec<LocalisationFile>,
    pub values: BTreeMap<String, String>,
    pub keys: BTreeSet<String>,
    pub duplicate_keys: BTreeMap<String, usize>,
    pub values_by_language: BTreeMap<(LocalisationLanguage, String), String>,
}

impl LocalisationIndex {
    #[must_use]
    pub fn empty() -> Self {
        Self {
            files: Vec::new(),
            values: BTreeMap::new(),
            keys: BTreeSet::new(),
            duplicate_keys: BTreeMap::new(),
            values_by_language: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn get(&self, language: LocalisationLanguage, key: &str) -> Option<&str> {
        self.values_by_language
            .get(&(language, key.to_owned()))
            .map(String::as_str)
    }

    pub fn add_file(&mut self, file: LocalisationFile) -> Result<(), SessionError> {
        if self.files.len() >= MAX_LOCALISATION_FILES {
            return Err(SessionError::LimitExceeded("localisation files"));
        }
        for entry in &file.entries {
            let identity = (entry.language, entry.key.clone());
            if self.values_by_language.contains_key(&identity) {
                *self
                    .duplicate_keys
                    .entry(format!("{}:{}", entry.language.tag(), entry.key))
                    .or_default() += 1;
            }
            self.values_by_language
                .insert(identity, entry.value.clone());
            self.keys.insert(entry.key.clone());
            self.values
                .entry(entry.key.clone())
                .or_insert_with(|| entry.value.clone());
            if self.keys.len() > MAX_LOCALISATION_ENTRIES {
                return Err(SessionError::LimitExceeded("localisation entries"));
            }
        }
        self.files.push(file);
        self.files.sort_by(|a, b| a.path.cmp(&b.path));
        Ok(())
    }
}

#[must_use]
pub fn parse_localisation(
    path: &str,
    text: &str,
    profile: &LocalisationProfile,
) -> LocalisationFile {
    match profile.format {
        LocalisationFormat::Yaml => parse_yaml_localisation(path, text),
        LocalisationFormat::CsvSemicolon => parse_csv_localisation(path, text, false),
        LocalisationFormat::Vic2Csv => parse_csv_localisation(path, text, true),
        LocalisationFormat::None => LocalisationFile {
            path: path.to_owned(),
            language: profile.default_language,
            encoding: profile.encoding,
            has_bom: text.starts_with('\u{feff}'),
            entries: Vec::new(),
            errors: Vec::new(),
        },
    }
}

/// Decodes localisation bytes using the profile encoding and validates required BOMs.
#[must_use]
pub fn parse_localisation_bytes(
    path: &str,
    bytes: &[u8],
    profile: &LocalisationProfile,
) -> LocalisationFile {
    let has_bom = bytes.starts_with(&[0xEF, 0xBB, 0xBF]);
    let payload = if has_bom { &bytes[3..] } else { bytes };
    let encoding = match profile.encoding {
        TextEncoding::Windows1252 => ScriptEncoding::Windows1252,
        TextEncoding::Utf8 | TextEncoding::Utf8Bom => ScriptEncoding::Utf8,
    };
    let decoded = decode_script_bytes(payload, encoding).unwrap_or_default();
    let text = if has_bom {
        format!("\u{feff}{decoded}")
    } else {
        decoded
    };
    let mut file = parse_localisation(path, &text, profile);
    if profile.encoding == TextEncoding::Utf8Bom && !has_bom {
        file.errors.insert(
            0,
            LocalisationDiagnostic {
                code: "WrongEncoding".to_owned(),
                message: "UTF-8 BOM is required for this localisation format".to_owned(),
                path: path.to_owned(),
                line: 1,
                column: 1,
                key: None,
            },
        );
    }
    file
}

fn language_from_tag(raw: &str) -> LocalisationLanguage {
    match raw
        .trim()
        .trim_start_matches('l')
        .trim_start_matches('_')
        .to_ascii_lowercase()
        .as_str()
    {
        "french" | "fr" => LocalisationLanguage::French,
        "german" | "de" => LocalisationLanguage::German,
        "spanish" | "es" => LocalisationLanguage::Spanish,
        "russian" | "ru" => LocalisationLanguage::Russian,
        "polish" | "pl" => LocalisationLanguage::Polish,
        "braz_por" | "portuguese" | "pt" => LocalisationLanguage::Portuguese,
        "simp_chinese" | "chinese" | "zh" => LocalisationLanguage::Chinese,
        "japanese" | "ja" => LocalisationLanguage::Japanese,
        "korean" | "ko" => LocalisationLanguage::Korean,
        "turkish" | "tr" => LocalisationLanguage::Turkish,
        "italian" | "it" => LocalisationLanguage::Italian,
        "default" => LocalisationLanguage::Default,
        _ => LocalisationLanguage::English,
    }
}

fn parse_yaml_localisation(path: &str, input: &str) -> LocalisationFile {
    let has_bom = input.starts_with('\u{feff}');
    let mut language = LocalisationLanguage::English;
    let mut entries = Vec::new();
    let mut errors = Vec::new();
    let mut current_comment = None;
    for (line_index, original) in input.trim_start_matches('\u{feff}').lines().enumerate() {
        let line = original.trim();
        let line_number = line_index + 1;
        if line.is_empty() {
            continue;
        }
        if let Some(comment) = line.strip_prefix('#') {
            current_comment = Some(comment.trim().to_owned());
            continue;
        }
        if line.starts_with("l_") && line.ends_with(':') {
            language = language_from_tag(line.trim_end_matches(':'));
            continue;
        }
        let Some((key_raw, value_raw)) = line.split_once(':') else {
            errors.push(LocalisationDiagnostic {
                code: "LOC001".to_owned(),
                message: "expected key: value".to_owned(),
                path: path.to_owned(),
                line: line_number,
                column: 1,
                key: None,
            });
            continue;
        };
        let key = key_raw.trim().to_owned();
        if key.is_empty() || key.contains(' ') {
            errors.push(LocalisationDiagnostic {
                code: "LOC002".to_owned(),
                message: "invalid localisation key".to_owned(),
                path: path.to_owned(),
                line: line_number,
                column: 1,
                key: Some(key),
            });
            continue;
        }
        let mut value = value_raw.trim().to_owned();
        if let Some(comment) = value.find(" #") {
            value.truncate(comment);
            value = value.trim_end().to_owned();
        }
        let version = value
            .chars()
            .next()
            .and_then(|character| character.to_digit(10))
            .map(|number| number as u8);
        if version.is_some() && value.len() > 1 {
            value.remove(0);
        }
        if value.starts_with('"') && !value.ends_with('"') {
            errors.push(LocalisationDiagnostic {
                code: "LOC003".to_owned(),
                message: "unterminated quoted localisation value".to_owned(),
                path: path.to_owned(),
                line: line_number,
                column: key_raw.len() + 2,
                key: Some(key.clone()),
            });
        }
        entries.push(LocalisationEntry {
            key,
            value: unescape_localisation_value(value.trim_matches('"')),
            language,
            path: path.to_owned(),
            line: line_number,
            column: 1,
            version,
            comment: current_comment.take(),
        });
    }
    LocalisationFile {
        path: path.to_owned(),
        language,
        encoding: TextEncoding::Utf8Bom,
        has_bom,
        entries,
        errors,
    }
}

fn unescape_localisation_value(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    let mut escaped = false;
    for ch in value.chars() {
        if escaped {
            out.push(match ch {
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                other => other,
            });
            escaped = false;
        } else if ch == '\\' {
            escaped = true;
        } else {
            out.push(ch);
        }
    }
    if escaped {
        out.push('\\');
    }
    out
}

fn parse_csv_localisation(path: &str, input: &str, vic2: bool) -> LocalisationFile {
    let mut entries = Vec::new();
    let mut errors = Vec::new();
    for (line_index, line) in input.lines().enumerate() {
        let line_number = line_index + 1;
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            continue;
        }
        let cells = split_csv_cells(line);
        if cells.len() < 2 {
            errors.push(LocalisationDiagnostic {
                code: "LOC010".to_owned(),
                message: "expected at least key and value".to_owned(),
                path: path.to_owned(),
                line: line_number,
                column: 1,
                key: None,
            });
            continue;
        }
        let key = cells[0].clone();
        if key.is_empty() {
            continue;
        }
        let languages = [
            LocalisationLanguage::English,
            LocalisationLanguage::French,
            LocalisationLanguage::German,
            LocalisationLanguage::Spanish,
            LocalisationLanguage::Italian,
            LocalisationLanguage::Polish,
        ];
        for (column, language) in languages.into_iter().enumerate() {
            let Some(value) = cells.get(column + 1).filter(|value| !value.is_empty()) else {
                continue;
            };
            entries.push(LocalisationEntry {
                key: key.clone(),
                value: value.clone(),
                language,
                path: path.to_owned(),
                line: line_number,
                column: column + 2,
                version: None,
                comment: vic2.then(|| "vic2".to_owned()),
            });
        }
    }
    LocalisationFile {
        path: path.to_owned(),
        language: LocalisationLanguage::English,
        encoding: TextEncoding::Windows1252,
        has_bom: false,
        entries,
        errors,
    }
}

fn split_csv_cells(line: &str) -> Vec<String> {
    let mut cells = Vec::new();
    let mut current = String::new();
    let mut quoted = false;
    let mut escaped = false;
    for character in line.chars() {
        if escaped {
            current.push(character);
            escaped = false;
            continue;
        }
        if character == '\\' && quoted {
            escaped = true;
            continue;
        }
        if character == '"' {
            quoted = !quoted;
            continue;
        }
        if character == ';' && !quoted {
            cells.push(current.trim().to_owned());
            current.clear();
        } else {
            current.push(character);
        }
    }
    cells.push(current.trim().to_owned());
    cells
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SessionError {
    LimitExceeded(&'static str),
    TooManySources,
    RuleDocumentParse(String),
    RulesCompile(String),
    Snapshot(String),
    Cache(String),
}

impl fmt::Display for SessionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LimitExceeded(kind) => write!(formatter, "{kind} limit exceeded"),
            Self::TooManySources => formatter.write_str("source limit exceeded"),
            Self::RuleDocumentParse(message) => {
                write!(formatter, "rule document parse failed: {message}")
            }
            Self::RulesCompile(message) => write!(formatter, "rules compile failed: {message}"),
            Self::Snapshot(message) => write!(formatter, "snapshot failed: {message}"),
            Self::Cache(message) => write!(formatter, "cache failed: {message}"),
        }
    }
}
impl std::error::Error for SessionError {}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct SourceInput {
    pub scope: String,
    pub path: String,
    pub logical_path: String,
    pub text: String,
    pub overwrite: Overwrite,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GameSessionConfig {
    pub game_id: GameId,
    pub rules_hash: Fingerprint,
    pub snapshot_limits: SnapshotLimits,
    pub max_diagnostics: usize,
    pub cache_path: Option<PathBuf>,
    pub cache_limits: cwtools_cache::CacheLimits,
}

impl Default for GameSessionConfig {
    fn default() -> Self {
        Self {
            game_id: GameId::Generic,
            rules_hash: Fingerprint::new(0),
            snapshot_limits: SnapshotLimits::default(),
            max_diagnostics: 100_000,
            cache_path: None,
            cache_limits: cwtools_cache::CacheLimits::default(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct SessionSnapshot {
    pub full: FullSnapshot,
    pub game_data: GameComputedData,
    pub localisation: LocalisationIndex,
    pub source_fingerprint: Fingerprint,
}

#[derive(Clone, Debug)]
pub struct GameSession {
    config: GameSessionConfig,
    profile: GameProfile,
    catalog: Option<RuleCatalog>,
    scopes: ValueScopeCatalog,
    sources: BTreeMap<String, SourceInput>,
    localisation: LocalisationIndex,
    snapshot: Option<SessionSnapshot>,
    cache: BoundedMemoryCache<Fingerprint, GameComputedData>,
    incremental: Option<IncrementalStore>,
}

impl GameSession {
    #[must_use]
    pub fn new(config: GameSessionConfig) -> Self {
        let profile = game_profile(config.game_id);
        Self {
            config,
            profile,
            catalog: None,
            scopes: ValueScopeCatalog::default(),
            sources: BTreeMap::new(),
            localisation: LocalisationIndex::empty(),
            snapshot: None,
            cache: BoundedMemoryCache::new(4),
            incremental: None,
        }
    }

    #[must_use]
    pub fn profile(&self) -> &GameProfile {
        &self.profile
    }
    #[must_use]
    pub fn game_id(&self) -> GameId {
        self.config.game_id
    }
    #[must_use]
    pub fn sources(&self) -> impl Iterator<Item = &SourceInput> {
        self.sources.values()
    }
    #[must_use]
    pub fn localisation(&self) -> &LocalisationIndex {
        &self.localisation
    }
    #[must_use]
    pub fn snapshot(&self) -> Option<&SessionSnapshot> {
        self.snapshot.as_ref()
    }
    #[must_use]
    pub fn rules_catalog(&self) -> Option<&RuleCatalog> {
        self.catalog.as_ref()
    }

    pub fn set_rules(
        &mut self,
        documents: &[Document],
        scope_names: impl IntoIterator<Item = String>,
    ) -> Result<(), SessionError> {
        if documents.len() > MAX_RULE_DOCUMENTS {
            return Err(SessionError::LimitExceeded("rule documents"));
        }
        let universe = ScopeUniverse::new(scope_names);
        self.catalog = Some(
            RuleCatalog::compile(documents, universe)
                .map_err(|error| SessionError::RulesCompile(format!("{error:?}")))?,
        );
        Ok(())
    }

    pub fn set_rule_catalog(&mut self, catalog: RuleCatalog) {
        self.catalog = Some(catalog);
    }

    pub fn install_cached_snapshot(
        &mut self,
        snapshot: SessionSnapshot,
    ) -> Result<(), SessionError> {
        if snapshot.source_fingerprint
            != fingerprint_sources(
                self.sources
                    .values()
                    .map(|source| (source.logical_path.as_str(), source.text.as_str())),
            )
        {
            return Err(SessionError::Cache(
                "cached snapshot source fingerprint mismatch".to_owned(),
            ));
        }
        let inputs = self
            .sources
            .values()
            .map(|source| SnapshotSource {
                scope: source.scope.clone(),
                path: source.path.clone(),
                logical_path: source.logical_path.clone(),
                text: source.text.clone(),
                overwrite: source.overwrite,
            })
            .collect::<Vec<_>>();
        self.incremental = Some(
            IncrementalStore::from_snapshot(
                inputs,
                snapshot.full.clone(),
                self.config.snapshot_limits,
            )
            .map_err(|error| SessionError::Snapshot(error.to_string()))?,
        );
        self.localisation = snapshot.localisation.clone();
        self.cache
            .insert(snapshot.source_fingerprint, snapshot.game_data.clone());
        self.snapshot = Some(snapshot);
        Ok(())
    }

    pub fn set_scope_catalog(&mut self, catalog: ValueScopeCatalog) {
        self.scopes = catalog;
    }

    /// Merges mod override sources on top of an installed cached vanilla snapshot
    /// in one batch, without reparsing or revalidating the vanilla sources.
    pub fn merge_sources(&mut self, project: &[SourceInput]) -> Result<(), SessionError> {
        let Some(snapshot) = self.snapshot.clone() else {
            for source in project {
                self.upsert_source(source.clone())?;
            }
            return Ok(());
        };
        for source in project {
            self.upsert_source(source.clone())?;
        }
        let mut by_logical: BTreeMap<String, SnapshotSource> = snapshot
            .full
            .sources
            .iter()
            .cloned()
            .map(|source| (source.logical_path.clone(), source))
            .collect();
        for source in project {
            by_logical.insert(
                source.logical_path.clone(),
                SnapshotSource {
                    scope: source.scope.clone(),
                    path: source.path.clone(),
                    logical_path: source.logical_path.clone(),
                    text: source.text.clone(),
                    overwrite: source.overwrite,
                },
            );
        }
        let mut inputs = by_logical.into_values().collect::<Vec<_>>();
        inputs.sort_by(|left, right| {
            (left.logical_path.clone(), left.path.clone())
                .cmp(&(right.logical_path.clone(), right.path.clone()))
        });
        let mut full = compute_full_snapshot(inputs.clone(), self.config.snapshot_limits)
            .map_err(|error| SessionError::Snapshot(error.to_string()))?;
        let source_fingerprint = fingerprint_sources(
            self.sources
                .values()
                .map(|source| (source.logical_path.as_str(), source.text.as_str())),
        );
        self.incremental = Some(
            IncrementalStore::from_snapshot(inputs, full.clone(), self.config.snapshot_limits)
                .map_err(|error| SessionError::Snapshot(error.to_string()))?,
        );
        let root_for = |source: &SnapshotSource| {
            Some(
                source
                    .logical_path
                    .split('/')
                    .next()
                    .unwrap_or("root")
                    .to_owned(),
            )
        };
        if let Some(catalog) = self.catalog.as_ref() {
            let game_data = compute_rule_game_data(&full, catalog, 100_000, root_for)
                .map_err(|error| SessionError::Snapshot(format!("{error:?}")))?;
            compute_snapshot_diagnostics(&mut full, catalog, self.config.max_diagnostics, root_for)
                .map_err(|error| SessionError::Snapshot(format!("{error:?}")))?;
            self.cache.insert(source_fingerprint, game_data.clone());
            self.snapshot = Some(SessionSnapshot {
                full,
                game_data,
                localisation: snapshot.localisation,
                source_fingerprint,
            });
        } else {
            self.cache
                .insert(source_fingerprint, GameComputedData::default());
            self.snapshot = Some(SessionSnapshot {
                full,
                game_data: GameComputedData::default(),
                localisation: snapshot.localisation,
                source_fingerprint,
            });
        }
        Ok(())
    }

    pub fn upsert_source(&mut self, source: SourceInput) -> Result<(), SessionError> {
        if self.sources.len() >= self.config.snapshot_limits.max_sources
            && !self.sources.contains_key(&source.path)
        {
            return Err(SessionError::TooManySources);
        }
        self.sources.insert(source.path.clone(), source);
        Ok(())
    }

    pub fn remove_source(&mut self, path: &str) -> bool {
        self.sources.remove(path).is_some()
    }

    pub fn add_localisation(&mut self, path: &str, text: &str) -> Result<(), SessionError> {
        let file = parse_localisation(path, text, &self.profile.localisation);
        self.localisation.add_file(file)
    }

    /// Full rebuild hook. All inputs are snapshotted in deterministic path order.
    pub fn refresh_full(&mut self) -> Result<&SessionSnapshot, SessionError> {
        let inputs = self
            .sources
            .values()
            .map(|source| SnapshotSource {
                scope: source.scope.clone(),
                path: source.path.clone(),
                logical_path: source.logical_path.clone(),
                text: source.text.clone(),
                overwrite: source.overwrite,
            })
            .collect::<Vec<_>>();
        let source_fingerprint = fingerprint_sources(
            self.sources
                .values()
                .map(|source| (source.logical_path.as_str(), source.text.as_str())),
        );
        let mut full = compute_full_snapshot(inputs.clone(), self.config.snapshot_limits)
            .map_err(|error| SessionError::Snapshot(error.to_string()))?;
        self.incremental = Some(
            IncrementalStore::new(inputs, self.config.snapshot_limits)
                .map_err(|error| SessionError::Snapshot(error.to_string()))?,
        );
        let root_for = |source: &SnapshotSource| {
            Some(
                source
                    .logical_path
                    .split('/')
                    .next()
                    .unwrap_or("root")
                    .to_owned(),
            )
        };
        let game_data = if let Some(catalog) = self.catalog.as_ref() {
            if let Some(cached) = self.cache.get(&source_fingerprint) {
                cached.clone()
            } else {
                let data = compute_rule_game_data(&full, catalog, 100_000, root_for)
                    .map_err(|error| SessionError::Snapshot(format!("{error:?}")))?;
                self.cache.insert(source_fingerprint, data.clone());
                data
            }
        } else {
            GameComputedData::default()
        };
        if let Some(catalog) = self.catalog.as_ref() {
            compute_snapshot_diagnostics(&mut full, catalog, self.config.max_diagnostics, root_for)
                .map_err(|error| SessionError::Snapshot(format!("{error:?}")))?;
        }
        self.snapshot = Some(SessionSnapshot {
            full,
            game_data,
            localisation: self.localisation.clone(),
            source_fingerprint,
        });
        Ok(self.snapshot.as_ref().expect("snapshot installed"))
    }

    /// Applies changed sources through the workspace prepare/commit transaction.
    pub fn refresh_incremental(
        &mut self,
        changed_paths: &[String],
    ) -> Result<&SessionSnapshot, SessionError> {
        if self.incremental.is_none() {
            self.refresh_full()?;
        }
        let store = self
            .incremental
            .as_ref()
            .expect("incremental store installed");
        let previous: BTreeMap<String, SnapshotSource> = store
            .snapshot()
            .sources
            .iter()
            .map(|source| (source.path.clone(), source.clone()))
            .collect();
        let current: BTreeMap<String, SnapshotSource> = self
            .sources
            .values()
            .map(|source| {
                (
                    source.path.clone(),
                    SnapshotSource {
                        scope: source.scope.clone(),
                        path: source.path.clone(),
                        logical_path: source.logical_path.clone(),
                        text: source.text.clone(),
                        overwrite: source.overwrite,
                    },
                )
            })
            .collect();
        let mut changes = Vec::new();
        for path in changed_paths {
            match (previous.get(path), current.get(path)) {
                (Some(_), Some(source)) => changes.push(Change::Edit {
                    path: path.clone(),
                    text: source.text.clone(),
                }),
                (Some(_), None) => changes.push(Change::Remove { path: path.clone() }),
                (None, Some(source)) => changes.push(Change::Add(source.clone())),
                (None, None) => {}
            }
        }
        if changes.is_empty() {
            return Ok(self.snapshot.as_ref().expect("snapshot installed"));
        }
        let cancelled = std::sync::atomic::AtomicBool::new(false);
        let prepared = store
            .prepare(store.epoch(), &changes, &cancelled)
            .map_err(|error| SessionError::Snapshot(error.to_string()))?;
        let store = self
            .incremental
            .as_mut()
            .expect("incremental store installed");
        store
            .commit(prepared)
            .map_err(|error| SessionError::Snapshot(error.to_string()))?;
        let mut full = store.snapshot().clone();
        let source_fingerprint = fingerprint_sources(
            self.sources
                .values()
                .map(|source| (source.logical_path.as_str(), source.text.as_str())),
        );
        let root_for = |source: &SnapshotSource| {
            Some(
                source
                    .logical_path
                    .split('/')
                    .next()
                    .unwrap_or("root")
                    .to_owned(),
            )
        };
        let game_data = if let Some(catalog) = self.catalog.as_ref() {
            compute_rule_game_data(&full, catalog, 100_000, root_for)
                .map_err(|error| SessionError::Snapshot(format!("{error:?}")))?
        } else {
            GameComputedData::default()
        };
        if let Some(catalog) = self.catalog.as_ref() {
            compute_snapshot_diagnostics(&mut full, catalog, self.config.max_diagnostics, root_for)
                .map_err(|error| SessionError::Snapshot(format!("{error:?}")))?;
        }
        self.snapshot = Some(SessionSnapshot {
            full,
            game_data,
            localisation: self.localisation.clone(),
            source_fingerprint,
        });
        Ok(self.snapshot.as_ref().expect("snapshot installed"))
    }

    pub fn validate_source(&self, path: &str) -> Option<cwtools_rules_engine::ValidationResult> {
        let source = self.sources.get(path)?;
        let catalog = self.catalog.as_ref()?;
        let root = source.logical_path.split('/').next().unwrap_or("root");
        Some(catalog.validate_source(root, &source.text))
    }

    #[must_use]
    pub fn change_scope(&self, context: &ScopeContext, key: &str) -> Option<ScopeContext> {
        self.config
            .game_id
            .scope_family()
            .and_then(|family| game::change_scope(family, context, key))
    }

    #[must_use]
    pub fn cache_key(
        &self,
        source_fingerprint: Fingerprint,
    ) -> Result<CacheKey, cwtools_cache::CacheError> {
        CacheKey::new(
            self.config.game_id.as_str(),
            self.config.rules_hash,
            source_fingerprint,
        )
    }

    pub fn save_cache(
        &self,
        snapshot: &SessionSnapshot,
    ) -> Result<Option<CacheMetadata>, SessionError> {
        let Some(path) = self.config.cache_path.as_ref() else {
            return Ok(None);
        };
        let key = self
            .cache_key(snapshot.source_fingerprint)
            .map_err(|error| SessionError::Cache(error.to_string()))?;
        let store = CacheStore::with_limits(path, self.config.cache_limits);
        let payload =
            serde_json::to_vec(snapshot).map_err(|error| SessionError::Cache(error.to_string()))?;
        store
            .write_bytes(&key, &payload)
            .map(Some)
            .map_err(|error| SessionError::Cache(error.to_string()))
    }

    #[must_use]
    pub fn load_cache(&self, source_fingerprint: Fingerprint) -> CacheRead<SessionSnapshot> {
        let Some(path) = self.config.cache_path.as_ref() else {
            return CacheRead::miss(cwtools_cache::CacheMissReason::NotFound);
        };
        let key = match self.cache_key(source_fingerprint) {
            Ok(key) => key,
            Err(_) => return CacheRead::miss(cwtools_cache::CacheMissReason::InvalidGameId),
        };
        CacheStore::with_limits(path, self.config.cache_limits).read_json(&key)
    }
}

/// Public adapter contract shared by all game-specific profiles.
pub trait GameModel {
    fn profile(&self) -> &GameProfile;
    fn refresh_full(&mut self) -> Result<&SessionSnapshot, SessionError>;
    fn refresh_incremental(
        &mut self,
        changed_paths: &[String],
    ) -> Result<&SessionSnapshot, SessionError>;
    fn validate_source(&self, path: &str) -> Option<cwtools_rules_engine::ValidationResult>;
    fn localisation(&self) -> &LocalisationIndex;
}

impl GameModel for GameSession {
    fn profile(&self) -> &GameProfile {
        self.profile()
    }
    fn refresh_full(&mut self) -> Result<&SessionSnapshot, SessionError> {
        self.refresh_full()
    }
    fn refresh_incremental(
        &mut self,
        changed_paths: &[String],
    ) -> Result<&SessionSnapshot, SessionError> {
        self.refresh_incremental(changed_paths)
    }
    fn validate_source(&self, path: &str) -> Option<cwtools_rules_engine::ValidationResult> {
        self.validate_source(path)
    }
    fn localisation(&self) -> &LocalisationIndex {
        self.localisation()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn profiles_cover_every_requested_game() {
        let profiles = all_game_profiles();
        assert_eq!(profiles.len(), 13);
        for id in [
            GameId::Generic,
            GameId::Custom,
            GameId::Jomini,
            GameId::Ck2,
            GameId::Ck3,
            GameId::Eu4,
            GameId::Eu5,
            GameId::Hoi4,
            GameId::Imperator,
            GameId::Vic2,
            GameId::Vic3,
            GameId::Stellaris,
            GameId::CwtOnly,
        ] {
            assert!(profiles.iter().any(|profile| profile.id == id));
        }
    }

    #[test]
    fn yaml_and_legacy_localisation_are_indexed_and_validated() {
        let mut index = LocalisationIndex::empty();
        index
            .add_file(parse_localisation(
                "a.yml",
                "\u{feff}l_english:\n hello: \"Hello\"",
                &game_profile(GameId::Stellaris).localisation,
            ))
            .unwrap();
        index
            .add_file(parse_localisation(
                "b.csv",
                "KEY;Value;;;",
                &game_profile(GameId::Ck2).localisation,
            ))
            .unwrap();
        assert!(index.keys.contains("hello"));
        assert!(index.keys.contains("KEY"));
    }

    #[test]
    fn session_full_and_incremental_hooks_are_deterministic() {
        let mut session = GameSession::new(GameSessionConfig {
            game_id: GameId::CwtOnly,
            ..GameSessionConfig::default()
        });
        session
            .upsert_source(SourceInput {
                scope: "mod".to_owned(),
                path: "a.txt".to_owned(),
                logical_path: "common/a.txt".to_owned(),
                text: "x = 1".to_owned(),
                overwrite: Overwrite::No,
            })
            .unwrap();
        let first = session.refresh_full().unwrap().source_fingerprint;
        let second = session
            .refresh_incremental(&["a.txt".to_owned()])
            .unwrap()
            .source_fingerprint;
        assert_eq!(first, second);
    }

    #[test]
    fn localisation_validation_rejects_invalid_key_and_missing_colon() {
        let file = parse_localisation(
            "a.yml",
            "l_english:\n bad key: value\n malformed",
            &game_profile(GameId::Stellaris).localisation,
        );
        assert!(file.errors.iter().any(|error| error.code == "LOC002"));
        assert!(file.errors.iter().any(|error| error.code == "LOC001"));
    }
}
