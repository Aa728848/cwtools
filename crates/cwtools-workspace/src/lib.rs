#![forbid(unsafe_code)]
//! Deterministic full-snapshot resource precedence for `CWTools` workspaces.

pub mod incremental;

use cwtools_rule_ir::{SkipRootKey, TypeDefinition};
use cwtools_rules_engine::{DynamicTypeReference, QueryError, RuleCatalog};
use cwtools_scopes::{ReferenceHint, ValueScopeCatalog, ValueScopeResolution};
use cwtools_script_syntax::{ByteRange, CstNode, ScriptEncoding, decode_script_bytes, parse};
use globset::{Glob, GlobSet, GlobSetBuilder};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use zip::ZipArchive;

pub const MAX_ARCHIVE_ENTRIES: usize = 100_000;
pub const MAX_ARCHIVE_ENTRY_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_ARCHIVE_TOTAL_BYTES: u64 = 512 * 1024 * 1024;
pub const MAX_DISCOVERED_FILES: usize = 1_000_000;
pub const MAX_DIRECTORY_DEPTH: usize = 256;
pub const MAX_TEXT_BYTES: usize = 64 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Overwrite {
    #[default]
    No,
    Overwrote,
    Overwritten,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Resource<T> {
    pub scope: String,
    pub file_path: String,
    pub logical_path: String,
    pub value: T,
    pub overwrite: Overwrite,
    pub validate: bool,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResourceSnapshot<T> {
    resources: Vec<Resource<T>>,
}

impl<T> ResourceSnapshot<T> {
    #[must_use]
    pub fn build(mut resources: Vec<Resource<T>>) -> Self {
        let mut groups: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for (index, resource) in resources.iter().enumerate() {
            groups
                .entry(resource.logical_path.clone())
                .or_default()
                .push(index);
        }
        for indices in groups.values_mut() {
            if indices.len() == 1 {
                resources[indices[0]].overwrite = Overwrite::No;
                continue;
            }
            indices.sort_by(|left, right| {
                precedence(&resources[*right].scope)
                    .cmp(precedence(&resources[*left].scope))
                    .then_with(|| resources[*left].file_path.cmp(&resources[*right].file_path))
            });
            for (position, index) in indices.iter().copied().enumerate() {
                resources[index].overwrite = if position == 0 {
                    Overwrite::Overwrote
                } else {
                    Overwrite::Overwritten
                };
            }
        }
        resources.sort_by(|left, right| {
            (&left.logical_path, &left.file_path).cmp(&(&right.logical_path, &right.file_path))
        });
        Self { resources }
    }

    #[must_use]
    pub fn resources(&self) -> &[Resource<T>] {
        &self.resources
    }

    pub fn active(&self) -> impl Iterator<Item = &Resource<T>> {
        self.resources
            .iter()
            .filter(|resource| resource.overwrite != Overwrite::Overwritten)
    }

    pub fn validated(&self) -> impl Iterator<Item = &Resource<T>> {
        self.active().filter(|resource| resource.validate)
    }
}

#[must_use]
pub fn logical_path(path: &str, workspace_roots: &[String], script_folders: &[String]) -> String {
    let mut result = path.replace('\\', "/");
    for root in workspace_roots {
        if let Some(index) = result.find(root) {
            result.drain(..index + root.len());
            break;
        }
    }
    if result.starts_with("gfx/") {
        return result;
    }
    let earliest = script_folders
        .iter()
        .filter_map(|folder| folder_index(&result, folder))
        .min();
    earliest.map_or(result.clone(), |index| result[index..].to_owned())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResourceKind {
    Entity,
    Content,
    File,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Admission {
    pub kind: ResourceKind,
    pub validate: bool,
}

#[must_use]
pub fn admit(
    logical_path: &str,
    file_path: &str,
    file_length: u64,
    max_file_size_mb: u64,
) -> Option<Admission> {
    let extension = file_path
        .rsplit_once('.')
        .map_or("", |(_, extension)| extension);
    let extensionless_inline = extension.is_empty()
        && logical_path
            .to_ascii_lowercase()
            .starts_with("common/inline_scripts/");
    let bounded_entity = extensionless_inline
        || matches!(extension, "txt" | "gui" | "gfx" | "sfx" | "asset" | "map");
    if bounded_entity {
        return (file_length <= max_file_size_mb.saturating_mul(1_000_000)).then_some(Admission {
            kind: ResourceKind::Entity,
            validate: true,
        });
    }
    match extension {
        "shader" | "fxh" | "yml" | "csv" => Some(Admission {
            kind: ResourceKind::Content,
            validate: true,
        }),
        "dds" | "tga" | "lua" | "png" | "mesh" | "ttf" | "otf" | "wav" => Some(Admission {
            kind: ResourceKind::File,
            validate: false,
        }),
        _ => None,
    }
}

#[derive(Debug)]
pub enum DiscoverError {
    Io(io::Error),
    InvalidGlob(String),
    TooManyFiles { limit: usize },
    TooDeep { limit: usize },
}

impl std::fmt::Display for DiscoverError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "filesystem discovery failed: {error}"),
            Self::InvalidGlob(pattern) => write!(formatter, "invalid ignore glob: {pattern}"),
            Self::TooManyFiles { limit } => {
                write!(formatter, "workspace exceeds {limit} discovered files")
            }
            Self::TooDeep { limit } => {
                write!(formatter, "workspace exceeds directory depth {limit}")
            }
        }
    }
}

impl std::error::Error for DiscoverError {}

impl From<io::Error> for DiscoverError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiscoveredFile {
    pub scope: String,
    pub path: PathBuf,
    pub logical_path: String,
    pub length: u64,
    pub admission: Admission,
}

#[derive(Clone, Debug)]
pub struct DiscoveryOptions {
    pub workspace_root: PathBuf,
    pub scope: String,
    pub script_folders: Vec<String>,
    pub ignore_globs: Vec<String>,
    pub max_file_size_mb: u64,
    pub max_files: usize,
    pub max_depth: usize,
}

impl DiscoveryOptions {
    #[must_use]
    pub fn bounded(workspace_root: PathBuf, scope: String, script_folders: Vec<String>) -> Self {
        Self {
            workspace_root,
            scope,
            script_folders,
            ignore_globs: Vec::new(),
            max_file_size_mb: 10,
            max_files: MAX_DISCOVERED_FILES,
            max_depth: MAX_DIRECTORY_DEPTH,
        }
    }
}

/// Recursively discovers admitted files with deterministic ordering and hard bounds.
///
/// # Errors
/// Returns an error for invalid ignore globs, filesystem failures, or exceeded file/depth limits.
pub fn discover(options: &DiscoveryOptions) -> Result<Vec<DiscoveredFile>, DiscoverError> {
    let ignores = compile_globs(&options.ignore_globs)?;
    let normalized_root = options.workspace_root.to_string_lossy().replace('\\', "/");
    let roots = [normalized_root];
    let mut stack = vec![(options.workspace_root.clone(), 0usize)];
    let mut seen = BTreeSet::new();
    let mut discovered = Vec::new();
    while let Some((directory, depth)) = stack.pop() {
        if depth > options.max_depth {
            return Err(DiscoverError::TooDeep {
                limit: options.max_depth,
            });
        }
        let mut entries = fs::read_dir(&directory)?.collect::<Result<Vec<_>, _>>()?;
        entries.sort_by_key(fs::DirEntry::path);
        for entry in entries.into_iter().rev() {
            let path = entry.path();
            let metadata = entry.metadata()?;
            if metadata.is_dir() {
                stack.push((path, depth + 1));
                continue;
            }
            if !metadata.is_file() {
                continue;
            }
            let normalized = path.to_string_lossy().replace('\\', "/");
            if ignores.is_match(&normalized) || !seen.insert(normalized.clone()) {
                continue;
            }
            if seen.len() > options.max_files {
                return Err(DiscoverError::TooManyFiles {
                    limit: options.max_files,
                });
            }
            let logical = logical_path(&normalized, &roots, &options.script_folders);
            let Some(admission) = admit(
                &logical,
                &normalized,
                metadata.len(),
                options.max_file_size_mb,
            ) else {
                continue;
            };
            discovered.push(DiscoveredFile {
                scope: options.scope.clone(),
                path,
                logical_path: logical,
                length: metadata.len(),
                admission,
            });
        }
    }
    discovered.sort_by(|left, right| left.path.cmp(&right.path));
    Ok(discovered)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TextEncoding {
    Utf8,
    Windows1252,
}

#[derive(Debug)]
pub enum ReadTextError {
    Io(io::Error),
    TooLarge {
        bytes: u64,
        limit: usize,
    },
    Decode {
        offset: usize,
        message: &'static str,
    },
    UnsupportedBom,
}

impl std::fmt::Display for ReadTextError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "resource read failed: {error}"),
            Self::TooLarge { bytes, limit } => {
                write!(formatter, "resource has {bytes} bytes; limit is {limit}")
            }
            Self::Decode { offset, message } => write!(
                formatter,
                "resource decode failed at byte {offset}: {message}"
            ),
            Self::UnsupportedBom => write!(formatter, "UTF-16/UTF-32 BOM is not supported"),
        }
    }
}

impl std::error::Error for ReadTextError {}

impl From<io::Error> for ReadTextError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

/// Reads one text resource without allocating beyond the configured byte bound.
///
/// UTF-8 BOM is stripped. UTF-16/UTF-32 BOMs fail closed because script ranges
/// and offsets are defined over UTF-8 source bytes in the Rust engine.
///
/// # Errors
/// Returns an error for I/O failures, oversized inputs, unsupported BOMs, or invalid UTF-8.
pub fn read_text(
    path: &PathBuf,
    encoding: TextEncoding,
    max_bytes: usize,
) -> Result<String, ReadTextError> {
    let metadata = fs::metadata(path)?;
    if metadata.len() > max_bytes as u64 {
        return Err(ReadTextError::TooLarge {
            bytes: metadata.len(),
            limit: max_bytes,
        });
    }
    let mut bytes = Vec::with_capacity(
        usize::try_from(metadata.len())
            .unwrap_or(max_bytes)
            .min(max_bytes),
    );
    fs::File::open(path)?
        .take((max_bytes + 1) as u64)
        .read_to_end(&mut bytes)?;
    if bytes.len() > max_bytes {
        return Err(ReadTextError::TooLarge {
            bytes: bytes.len() as u64,
            limit: max_bytes,
        });
    }
    if has_unsupported_bom(&bytes) {
        return Err(ReadTextError::UnsupportedBom);
    }
    let bytes = bytes.strip_prefix(&[0xEF, 0xBB, 0xBF]).unwrap_or(&bytes);
    let script_encoding = match encoding {
        TextEncoding::Utf8 => ScriptEncoding::Utf8,
        TextEncoding::Windows1252 => ScriptEncoding::Windows1252,
    };
    decode_script_bytes(bytes, script_encoding).map_err(|error| ReadTextError::Decode {
        offset: error.offset,
        message: error.message,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SnapshotSource {
    pub scope: String,
    pub path: String,
    pub logical_path: String,
    pub text: String,
    pub overwrite: Overwrite,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolOccurrence {
    pub name: String,
    pub path: String,
    pub logical_path: String,
    pub range: ByteRange,
    pub key_prefix: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SnapshotDiagnostic {
    pub path: String,
    pub logical_path: String,
    pub code: String,
    pub message_key: String,
    pub key: String,
    pub args: Vec<String>,
    pub range: ByteRange,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SnapshotParseError {
    pub path: String,
    pub code: String,
    pub message: String,
    pub offset: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ComputedBlock {
    pub key: String,
    pub path: String,
    pub logical_path: String,
    pub range: ByteRange,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScopedOccurrence {
    pub occurrence: SymbolOccurrence,
    pub scope: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SnapshotReferenceDetail {
    pub occurrence: SymbolOccurrence,
    pub type_name: String,
    pub is_outgoing: bool,
    pub reference_label: Option<String>,
    pub fuzzy: bool,
    pub associated_type: Option<String>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct GameComputedData {
    pub defined_variables: BTreeMap<String, Vec<SymbolOccurrence>>,
    pub saved_event_targets: Vec<ScopedOccurrence>,
    pub effect_blocks: Vec<ComputedBlock>,
    pub trigger_blocks: Vec<ComputedBlock>,
    pub scripted_effect_params: BTreeMap<String, Vec<String>>,
    pub script_value_params: BTreeMap<String, Vec<String>>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct GameComputedProfile {
    /// Assignment key to F# variable-set kind.
    pub variable_set_keys: BTreeMap<String, String>,
    pub saved_event_target_keys: BTreeSet<String>,
    pub effect_block_keys: BTreeSet<String>,
    pub trigger_block_keys: BTreeSet<String>,
    pub scripted_parameter_paths: BTreeSet<String>,
    pub script_value_paths: BTreeSet<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ComputedDataError {
    TooManyOccurrences { limit: usize },
}

impl std::fmt::Display for ComputedDataError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooManyOccurrences { limit } => {
                write!(formatter, "computed data exceeds {limit} occurrences")
            }
        }
    }
}

impl std::error::Error for ComputedDataError {}

#[must_use]
pub fn eu4_computed_profile() -> GameComputedProfile {
    GameComputedProfile {
        scripted_parameter_paths: [
            "common/scripted_effects".to_owned(),
            "common/scripted_triggers".to_owned(),
        ]
        .into_iter()
        .collect(),
        ..GameComputedProfile::default()
    }
}

#[must_use]
pub fn stellaris_computed_profile() -> GameComputedProfile {
    GameComputedProfile {
        scripted_parameter_paths: [
            "common/scripted_effects".to_owned(),
            "common/scripted_triggers".to_owned(),
        ]
        .into_iter()
        .collect(),
        script_value_paths: ["common/script_values".to_owned()].into_iter().collect(),
        ..GameComputedProfile::default()
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FullSnapshot {
    pub sources: Vec<SnapshotSource>,
    pub typed_definitions: BTreeMap<String, BTreeMap<String, Vec<SymbolOccurrence>>>,
    pub typed_subtypes: BTreeMap<String, BTreeMap<String, Vec<SymbolOccurrence>>>,
    pub typed_references: BTreeMap<String, BTreeMap<String, Vec<SymbolOccurrence>>>,
    pub reference_details: Vec<SnapshotReferenceDetail>,
    pub diagnostics: Vec<SnapshotDiagnostic>,
    pub definitions: BTreeMap<String, Vec<SymbolOccurrence>>,
    pub references: BTreeMap<String, Vec<SymbolOccurrence>>,
    pub variables: BTreeMap<String, Vec<SymbolOccurrence>>,
    pub parse_errors: Vec<SnapshotParseError>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SnapshotLimits {
    pub max_sources: usize,
    pub max_nodes: usize,
}

impl Default for SnapshotLimits {
    fn default() -> Self {
        Self {
            max_sources: MAX_DISCOVERED_FILES,
            max_nodes: 1_000_000,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SnapshotError {
    TooManySources { limit: usize },
    TooManyNodes { limit: usize },
}

impl std::fmt::Display for SnapshotError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooManySources { limit } => write!(formatter, "snapshot exceeds {limit} sources"),
            Self::TooManyNodes { limit } => {
                write!(formatter, "snapshot exceeds {limit} syntax nodes")
            }
        }
    }
}

impl std::error::Error for SnapshotError {}

/// Computes deterministic full-workspace syntax indexes from active resources.
///
/// Top-level assignment keys are definitions. Every assignment value scalar is
/// indexed as a reference, while `@` assignment keys are also indexed as variables.
/// Overwritten sources never enter the resulting snapshot.
///
/// # Errors
/// Returns an error when source or syntax-node hard limits are exceeded.
pub fn compute_full_snapshot(
    mut sources: Vec<SnapshotSource>,
    limits: SnapshotLimits,
) -> Result<FullSnapshot, SnapshotError> {
    sources.retain(|source| source.overwrite != Overwrite::Overwritten);
    sources.sort_by(|left, right| {
        (&left.logical_path, &left.path).cmp(&(&right.logical_path, &right.path))
    });
    if sources.len() > limits.max_sources {
        return Err(SnapshotError::TooManySources {
            limit: limits.max_sources,
        });
    }
    let mut snapshot = FullSnapshot {
        sources,
        ..FullSnapshot::default()
    };
    let mut indexes = SnapshotIndexes {
        node_count: 0,
        max_nodes: limits.max_nodes,
        definitions: &mut snapshot.definitions,
        references: &mut snapshot.references,
        variables: &mut snapshot.variables,
    };
    for source in &snapshot.sources {
        match parse(&source.text) {
            Ok(cst) => {
                for node in &cst.roots {
                    index_node(node, source, true, &mut indexes)?;
                }
            }
            Err(errors) => {
                snapshot
                    .parse_errors
                    .extend(errors.into_iter().map(|error| SnapshotParseError {
                        path: source.path.clone(),
                        code: error.code.to_owned(),
                        message: error.message,
                        offset: error.offset,
                    }));
            }
        }
    }
    sort_index(&mut snapshot.definitions);
    sort_index(&mut snapshot.references);
    sort_index(&mut snapshot.variables);
    snapshot.parse_errors.sort_by(|left, right| {
        (&left.path, left.offset, &left.code).cmp(&(&right.path, right.offset, &right.code))
    });
    Ok(snapshot)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypedIndexError {
    TooManyOccurrences { limit: usize },
}

impl std::fmt::Display for TypedIndexError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooManyOccurrences { limit } => {
                write!(formatter, "typed index exceeds {limit} occurrences")
            }
        }
    }
}

impl std::error::Error for TypedIndexError {}

/// Rebuilds metadata-driven type definitions and references atomically.
///
/// Type paths admit source files. Per-file types use the filename stem; other
/// types use top-level keys or their configured `name_field`. Generic scalar
/// references are promoted to a type only when they resolve to a known typed ID.
///
/// # Errors
/// Returns an error when the combined typed occurrence limit is exceeded.
#[allow(clippy::too_many_lines)]
pub fn compute_typed_indexes(
    snapshot: &mut FullSnapshot,
    types: &[TypeDefinition],
    max_occurrences: usize,
) -> Result<(), TypedIndexError> {
    let mut definitions: BTreeMap<String, BTreeMap<String, Vec<SymbolOccurrence>>> =
        BTreeMap::new();
    let mut subtypes: BTreeMap<String, BTreeMap<String, Vec<SymbolOccurrence>>> = BTreeMap::new();
    let mut count = 0usize;
    for source in &snapshot.sources {
        let Ok(cst) = parse(&source.text) else {
            continue;
        };
        for type_definition in types {
            let type_key_regex = compile_type_key_regex(type_definition);
            if type_definition.type_key_regex.is_some() && type_key_regex.is_none() {
                continue;
            }
            if !type_admits(type_definition, &source.logical_path) {
                continue;
            }
            let mut candidates = Vec::new();
            if type_definition.type_per_file {
                if type_definition.key_prefix.is_some() {
                    continue;
                }
                let id = source
                    .logical_path
                    .rsplit('/')
                    .next()
                    .unwrap_or(&source.logical_path)
                    .rsplit_once('.')
                    .map_or_else(|| source.logical_path.clone(), |(stem, _)| stem.to_owned());
                candidates.push((id, ByteRange { start: 0, end: 0 }, Vec::new(), None));
            } else {
                for node in typed_candidate_nodes(&cst.roots, &type_definition.skip_root_key) {
                    let CstNode::Assignment {
                        key_prefix,
                        key,
                        value,
                        ..
                    } = node
                    else {
                        continue;
                    };
                    let Some(key_name) = node_text(key) else {
                        continue;
                    };
                    if !type_key_prefix_matches(type_definition, key_prefix.as_deref()) {
                        continue;
                    }
                    let matched_subtypes = classify_subtypes(type_definition, &key_name, value);
                    let (id, id_range) = type_definition
                        .name_field
                        .as_deref()
                        .and_then(|field| clause_field(value, field))
                        .unwrap_or((key_name, node_range(key)));
                    candidates.push((
                        id,
                        id_range,
                        matched_subtypes,
                        key_prefix.as_ref().map(|token| token.value.clone()),
                    ));
                }
            }
            for (id, range, matched_subtypes, key_prefix) in candidates {
                let Some(id) = normalize_type_id(type_definition, id, type_key_regex.as_ref())
                else {
                    continue;
                };
                count = count.saturating_add(1);
                if count > max_occurrences {
                    return Err(TypedIndexError::TooManyOccurrences {
                        limit: max_occurrences,
                    });
                }
                definitions
                    .entry(type_definition.name.clone())
                    .or_default()
                    .entry(id.clone())
                    .or_default()
                    .push(occurrence_with_prefix(
                        id.clone(),
                        source,
                        range,
                        key_prefix.clone(),
                    ));
                for subtype in matched_subtypes {
                    count = count.saturating_add(1);
                    if count > max_occurrences {
                        return Err(TypedIndexError::TooManyOccurrences {
                            limit: max_occurrences,
                        });
                    }
                    subtypes
                        .entry(format!("{}.{}", type_definition.name, subtype))
                        .or_default()
                        .entry(id.clone())
                        .or_default()
                        .push(occurrence(id.clone(), source, range));
                }
            }
        }
    }
    let mut references: BTreeMap<String, BTreeMap<String, Vec<SymbolOccurrence>>> = BTreeMap::new();
    for (type_name, ids) in &definitions {
        for (id, generic_occurrences) in &snapshot.references {
            if let Some(canonical_id) = ids.keys().find(|known| known.eq_ignore_ascii_case(id)) {
                for generic in generic_occurrences {
                    if ids[canonical_id].iter().any(|definition| {
                        definition.path == generic.path && definition.range == generic.range
                    }) {
                        continue;
                    }
                    count = count.saturating_add(1);
                    if count > max_occurrences {
                        return Err(TypedIndexError::TooManyOccurrences {
                            limit: max_occurrences,
                        });
                    }
                    let mut occurrence = generic.clone();
                    occurrence.name.clone_from(canonical_id);
                    references
                        .entry(type_name.clone())
                        .or_default()
                        .entry(canonical_id.clone())
                        .or_default()
                        .push(occurrence);
                }
            }
        }
    }
    sort_typed_index(&mut definitions);
    sort_typed_index(&mut subtypes);
    sort_typed_index(&mut references);
    snapshot.typed_definitions = definitions;
    snapshot.typed_subtypes = subtypes;
    snapshot.typed_references = references;
    Ok(())
}

/// Rebuilds subtype indexes with the full `RuleCatalog` validator.
///
/// This replaces the metadata-only structural probe with the same selector,
/// cardinality, value, shape, alias/type and `only_if_not` semantics used by validation.
/// Results replace the prior subtype index only after the bounded pass completes.
///
/// # Errors
/// Returns an error when the subtype occurrence limit is exceeded.
pub fn compute_rule_typed_subtypes(
    snapshot: &mut FullSnapshot,
    catalog: &RuleCatalog,
    types: &[TypeDefinition],
    max_occurrences: usize,
) -> Result<(), TypedIndexError> {
    let mut subtypes: BTreeMap<String, BTreeMap<String, Vec<SymbolOccurrence>>> = BTreeMap::new();
    let mut count = 0usize;
    for source in &snapshot.sources {
        let Ok(cst) = parse(&source.text) else {
            continue;
        };
        for type_definition in types {
            if !type_admits(type_definition, &source.logical_path) {
                continue;
            }
            let mut candidates = Vec::new();
            if type_definition.type_per_file {
                if type_definition.key_prefix.is_some() {
                    continue;
                }
                let id = source
                    .logical_path
                    .rsplit('/')
                    .next()
                    .unwrap_or(&source.logical_path)
                    .rsplit_once('.')
                    .map_or_else(|| source.logical_path.clone(), |(stem, _)| stem.to_owned());
                candidates.push((id, ByteRange { start: 0, end: 0 }, source.text.as_str()));
            } else {
                for node in typed_candidate_nodes(&cst.roots, &type_definition.skip_root_key) {
                    let CstNode::Assignment {
                        key_prefix,
                        key,
                        value,
                        ..
                    } = node
                    else {
                        continue;
                    };
                    let Some(key_name) = node_text(key) else {
                        continue;
                    };
                    if !type_key_prefix_matches(type_definition, key_prefix.as_deref()) {
                        continue;
                    }
                    let (id, range) = type_definition
                        .name_field
                        .as_deref()
                        .and_then(|field| clause_field(value, field))
                        .unwrap_or((key_name.clone(), node_range(key)));
                    candidates.push((id, range, clause_body(&source.text, value)));
                }
            }
            for (id, range, body) in candidates {
                let matched = catalog
                    .apply_type_subtypes(type_definition, &id, body)
                    .unwrap_or_default();
                for subtype in matched.names {
                    count = count.saturating_add(1);
                    if count > max_occurrences {
                        return Err(TypedIndexError::TooManyOccurrences {
                            limit: max_occurrences,
                        });
                    }
                    subtypes
                        .entry(format!("{}.{}", type_definition.name, subtype))
                        .or_default()
                        .entry(id.clone())
                        .or_default()
                        .push(occurrence(id.clone(), source, range));
                }
            }
        }
    }
    sort_typed_index(&mut subtypes);
    snapshot.typed_subtypes = subtypes;
    Ok(())
}

fn clause_body<'a>(source: &'a str, value: &CstNode) -> &'a str {
    let range = match value {
        CstNode::Clause { open, close, .. } => ByteRange {
            start: open.range.end,
            end: close
                .as_ref()
                .map_or(node_range(value).end, |token| token.range.start),
        },
        _ => node_range(value),
    };
    source.get(range.start..range.end).unwrap_or("").trim()
}

fn classify_subtypes(type_definition: &TypeDefinition, key: &str, value: &CstNode) -> Vec<String> {
    let mut matches = type_definition
        .subtypes
        .iter()
        .filter(|subtype| {
            let field_match = subtype
                .type_key_field
                .as_deref()
                .is_none_or(|field| key.eq_ignore_ascii_case(field));
            let starts_match = subtype.starts_with.as_deref().is_none_or(|prefix| {
                key.to_ascii_lowercase()
                    .starts_with(&prefix.to_ascii_lowercase())
            });
            let regex_match = subtype.type_key_regex.as_deref().is_none_or(|pattern| {
                regex::RegexBuilder::new(pattern)
                    .case_insensitive(true)
                    .build()
                    .is_ok_and(|regex| regex.is_match(key))
            });
            field_match && starts_match && regex_match && subtype_rules_match(&subtype.rules, value)
        })
        .map(|subtype| subtype.name.clone())
        .collect::<Vec<_>>();
    let all = matches.clone();
    matches.retain(|name| {
        type_definition
            .subtypes
            .iter()
            .find(|subtype| subtype.name == *name)
            .is_some_and(|subtype| {
                !subtype
                    .only_if_not
                    .iter()
                    .any(|excluded| all.iter().any(|matched| matched == excluded))
            })
    });
    matches
}

fn subtype_rules_match(rules: &[cwtools_rule_ir::NewRule], value: &CstNode) -> bool {
    let CstNode::Clause { children, .. } = value else {
        return rules.is_empty();
    };
    rules.iter().all(|rule| match &rule.kind {
        cwtools_rule_ir::RuleKind::Leaf {
            left: cwtools_rule_ir::NewField::Specific(required),
            right,
        } => children.iter().any(|child| {
            let CstNode::Assignment { key, value, .. } = child else {
                return false;
            };
            node_text(key).is_some_and(|key| key.eq_ignore_ascii_case(required))
                && field_matches(right, value)
        }),
        cwtools_rule_ir::RuleKind::Node {
            left: cwtools_rule_ir::NewField::Specific(required),
            ..
        } => children.iter().any(|child| {
            let CstNode::Assignment { key, value, .. } = child else {
                return false;
            };
            node_text(key).is_some_and(|key| key.eq_ignore_ascii_case(required))
                && matches!(value.as_ref(), CstNode::Clause { .. })
        }),
        _ => true,
    })
}

fn field_matches(field: &cwtools_rule_ir::NewField, value: &CstNode) -> bool {
    let Some(value) = node_text(value) else {
        return false;
    };
    match field {
        cwtools_rule_ir::NewField::Specific(expected) => value.eq_ignore_ascii_case(expected),
        cwtools_rule_ir::NewField::Value(cwtools_rule_ir::ValueType::Bool) => matches!(
            value.to_ascii_lowercase().as_str(),
            "yes" | "no" | "true" | "false"
        ),
        _ => true,
    }
}

fn type_key_prefix_matches(
    type_definition: &TypeDefinition,
    key_prefix: Option<&cwtools_script_syntax::Token>,
) -> bool {
    match (&type_definition.key_prefix, key_prefix) {
        (Some(expected), Some(actual)) => expected.eq_ignore_ascii_case(&actual.value),
        (None, None) => true,
        _ => false,
    }
}

fn compile_type_key_regex(type_definition: &TypeDefinition) -> Option<regex::Regex> {
    type_definition
        .type_key_regex
        .as_deref()
        .and_then(|pattern| {
            regex::RegexBuilder::new(pattern)
                .case_insensitive(true)
                .build()
                .ok()
        })
}

fn type_admits(type_definition: &TypeDefinition, logical_path: &str) -> bool {
    let logical = logical_path.trim_start_matches('/');
    let path_match = type_definition.path.as_deref().is_none_or(|path| {
        let path = path.trim_matches('/');
        logical == path || logical.starts_with(&format!("{path}/"))
    });
    let file_match = type_definition.path_file.as_deref().is_none_or(|path| {
        let path = path.trim_start_matches('/');
        logical == path || logical.ends_with(&format!("/{path}"))
    });
    path_match && file_match
}

fn typed_candidate_nodes<'a>(roots: &'a [CstNode], skip: &[SkipRootKey]) -> Vec<&'a CstNode> {
    if skip.is_empty() {
        return roots.iter().collect();
    }
    skip_nodes(roots, skip)
}

fn skip_nodes<'a>(nodes: &'a [CstNode], skip: &[SkipRootKey]) -> Vec<&'a CstNode> {
    let Some((head, tail)) = skip.split_first() else {
        return nodes.iter().collect();
    };
    nodes
        .iter()
        .flat_map(|node| {
            let CstNode::Assignment { key, value, .. } = node else {
                return Vec::new();
            };
            let Some(child_key) = node_text(key) else {
                return Vec::new();
            };
            let matches = match head {
                SkipRootKey::Specific(key) => child_key.eq_ignore_ascii_case(key),
                SkipRootKey::Any => true,
                SkipRootKey::Multiple { keys, should_match } => {
                    keys.iter().any(|key| child_key.eq_ignore_ascii_case(key)) == *should_match
                }
            };
            if !matches {
                return Vec::new();
            }
            let CstNode::Clause { children, .. } = value.as_ref() else {
                return Vec::new();
            };
            if tail.is_empty() {
                children.iter().collect()
            } else {
                skip_nodes(children, tail)
            }
        })
        .collect()
}

fn normalize_type_id(
    type_definition: &TypeDefinition,
    id: String,
    type_key_regex: Option<&regex::Regex>,
) -> Option<String> {
    if let Some(starts_with) = &type_definition.starts_with
        && !id
            .to_ascii_lowercase()
            .starts_with(&starts_with.to_ascii_lowercase())
    {
        return None;
    }
    if let Some(pattern) = type_key_regex
        && !pattern.is_match(&id)
    {
        return None;
    }
    if let Some((keys, negate)) = &type_definition.type_key_filter {
        let present = keys.iter().any(|key| key.eq_ignore_ascii_case(&id));
        if present == *negate {
            return None;
        }
    }
    Some(id)
}

fn clause_field(node: &CstNode, field: &str) -> Option<(String, ByteRange)> {
    let CstNode::Clause { children, .. } = node else {
        return None;
    };
    children.iter().find_map(|child| {
        let CstNode::Assignment { key, value, .. } = child else {
            return None;
        };
        node_text(key)
            .filter(|key| key.eq_ignore_ascii_case(field))
            .and_then(|_| node_text(value).map(|value_text| (value_text, node_range(value))))
    })
}

fn sort_typed_index(index: &mut BTreeMap<String, BTreeMap<String, Vec<SymbolOccurrence>>>) {
    for ids in index.values_mut() {
        for occurrences in ids.values_mut() {
            occurrences.sort_by(|left, right| {
                (&left.logical_path, &left.path, left.range.start).cmp(&(
                    &right.logical_path,
                    &right.path,
                    right.range.start,
                ))
            });
        }
    }
}

/// Computes game data from exact active `RuleCatalog` paths.
///
/// Variable sets and effect/trigger blocks come from the matched rule IR rather
/// than assignment-name heuristics. Results are returned only after the entire pass.
///
/// # Errors
/// Returns an error when the shared computed occurrence limit is exceeded.
pub fn compute_rule_game_data<F>(
    snapshot: &FullSnapshot,
    catalog: &RuleCatalog,
    max_occurrences: usize,
    mut root_for: F,
) -> Result<GameComputedData, ComputedDataError>
where
    F: FnMut(&SnapshotSource) -> Option<String>,
{
    let mut data = GameComputedData::default();
    let mut count = 0usize;
    for source in &snapshot.sources {
        let Some(root) = root_for(source) else {
            continue;
        };
        let extracted =
            match catalog.computed_data(&root, &source.text, max_occurrences.saturating_sub(count))
            {
                Ok(extracted) => extracted,
                Err(QueryError::TooManyResults) => {
                    return Err(ComputedDataError::TooManyOccurrences {
                        limit: max_occurrences,
                    });
                }
                Err(QueryError::ParseFailed | QueryError::InvalidOffset) => continue,
            };
        for variable in extracted.variable_sets {
            bump_computed_count(&mut count, max_occurrences)?;
            let name = normalize_variable_name(&variable.kind, &variable.value);
            if matches!(
                variable.kind.as_str(),
                "event_target" | "global_event_target"
            ) {
                data.saved_event_targets.push(ScopedOccurrence {
                    occurrence: occurrence(name, source, variable.range),
                    scope: variable.scope,
                });
            } else {
                data.defined_variables
                    .entry(variable.kind)
                    .or_default()
                    .push(occurrence(name, source, variable.range));
            }
        }
        for range in extracted.effect_blocks {
            bump_computed_count(&mut count, max_occurrences)?;
            data.effect_blocks
                .push(computed_block("effect".to_owned(), source, range));
        }
        for range in extracted.trigger_blocks {
            bump_computed_count(&mut count, max_occurrences)?;
            data.trigger_blocks
                .push(computed_block("trigger".to_owned(), source, range));
        }
    }
    sort_index(&mut data.defined_variables);
    sort_scoped_occurrences(&mut data.saved_event_targets);
    sort_blocks(&mut data.effect_blocks);
    sort_blocks(&mut data.trigger_blocks);
    Ok(data)
}

/// Computes bounded game-neutral data used by per-game `ComputedData` layers.
///
/// The profile maps stable game keys to variable kinds and effect/trigger block
/// categories. Malformed sources are skipped consistently with other snapshot indexes.
///
/// # Errors
/// Returns an error when the shared computed occurrence limit is exceeded.
pub fn compute_game_data(
    snapshot: &FullSnapshot,
    profile: &GameComputedProfile,
    max_occurrences: usize,
) -> Result<GameComputedData, ComputedDataError> {
    let mut data = GameComputedData::default();
    let mut count = 0usize;
    for source in &snapshot.sources {
        let Ok(cst) = parse(&source.text) else {
            continue;
        };
        collect_game_data_nodes(
            &cst.roots,
            source,
            profile,
            &mut data,
            &mut count,
            max_occurrences,
        )?;
        let logical = source.logical_path.to_ascii_lowercase();
        if path_matches_any(&logical, &profile.scripted_parameter_paths) {
            let params = extract_script_parameters(&cst.roots, &mut count, max_occurrences)?;
            data.scripted_effect_params
                .insert(source.path.clone(), params);
        }
        if path_matches_any(&logical, &profile.script_value_paths) {
            let params = extract_script_parameters(&cst.roots, &mut count, max_occurrences)?;
            data.script_value_params.insert(source.path.clone(), params);
        }
    }
    sort_index(&mut data.defined_variables);
    data.saved_event_targets.sort_by(|left, right| {
        (
            &left.occurrence.logical_path,
            &left.occurrence.path,
            left.occurrence.range.start,
            &left.occurrence.name,
            &left.scope,
        )
            .cmp(&(
                &right.occurrence.logical_path,
                &right.occurrence.path,
                right.occurrence.range.start,
                &right.occurrence.name,
                &right.scope,
            ))
    });
    sort_blocks(&mut data.effect_blocks);
    sort_blocks(&mut data.trigger_blocks);
    Ok(data)
}

fn path_matches_any(logical_path: &str, paths: &BTreeSet<String>) -> bool {
    paths
        .iter()
        .any(|path| logical_path.starts_with(&path.to_ascii_lowercase()))
}

fn extract_script_parameters(
    nodes: &[CstNode],
    count: &mut usize,
    limit: usize,
) -> Result<Vec<String>, ComputedDataError> {
    let mut params = Vec::new();
    collect_script_parameters(nodes, &mut params, count, limit)?;
    params.sort();
    params.dedup();
    Ok(params)
}

fn collect_script_parameters(
    nodes: &[CstNode],
    params: &mut Vec<String>,
    count: &mut usize,
    limit: usize,
) -> Result<(), ComputedDataError> {
    for node in nodes {
        match node {
            CstNode::Assignment {
                key_prefix,
                key,
                value,
                ..
            } => {
                if let Some(prefix) = key_prefix {
                    scan_parameter_text(&prefix.value, params, count, limit)?;
                }
                scan_node_parameter_text(key, params, count, limit)?;
                scan_node_parameter_text(value, params, count, limit)?;
                if let CstNode::Clause { children, .. } = value.as_ref() {
                    collect_script_parameters(children, params, count, limit)?;
                }
            }
            CstNode::Clause { children, .. } => {
                collect_script_parameters(children, params, count, limit)?;
            }
            _ => scan_node_parameter_text(node, params, count, limit)?,
        }
    }
    Ok(())
}

fn scan_node_parameter_text(
    node: &CstNode,
    params: &mut Vec<String>,
    count: &mut usize,
    limit: usize,
) -> Result<(), ComputedDataError> {
    match node {
        CstNode::Bare { token } | CstNode::Error { token } => {
            scan_parameter_text(&token.value, params, count, limit)
        }
        CstNode::ColourLiteral { raw, .. } => scan_parameter_text(raw, params, count, limit),
        CstNode::Comment { .. }
        | CstNode::Trivia { .. }
        | CstNode::Clause { .. }
        | CstNode::Assignment { .. } => Ok(()),
    }
}

fn scan_parameter_text(
    text: &str,
    params: &mut Vec<String>,
    count: &mut usize,
    limit: usize,
) -> Result<(), ComputedDataError> {
    for (index, part) in text.split('$').enumerate() {
        if index % 2 == 1 {
            let name = part.split('|').next().unwrap_or(part);
            if !name.is_empty() {
                bump_computed_count(count, limit)?;
                params.push(name.to_owned());
            }
        }
    }
    let mut rest = text;
    while let Some(index) = rest.find("[[") {
        let mut inner = rest[index + 2..].trim_start();
        inner = inner.strip_prefix('!').unwrap_or(inner).trim_start();
        let end = inner
            .find([']', ' ', '\t', '\r', '\n'])
            .unwrap_or(inner.len());
        let name = inner[..end].trim();
        if name
            .chars()
            .next()
            .is_some_and(|ch| ch.is_alphanumeric() || ch == '_')
        {
            bump_computed_count(count, limit)?;
            params.push(name.to_owned());
        }
        rest = &rest[index + 2..];
    }
    Ok(())
}

fn collect_game_data_nodes(
    nodes: &[CstNode],
    source: &SnapshotSource,
    profile: &GameComputedProfile,
    data: &mut GameComputedData,
    count: &mut usize,
    limit: usize,
) -> Result<(), ComputedDataError> {
    for node in nodes {
        let CstNode::Assignment {
            key, value, range, ..
        } = node
        else {
            continue;
        };
        let Some(key_name) = node_text(key) else {
            continue;
        };
        if let Some(kind) = profile
            .variable_set_keys
            .get(&key_name.to_ascii_lowercase())
            && let Some(name) = node_text(value)
        {
            bump_computed_count(count, limit)?;
            data.defined_variables
                .entry(kind.clone())
                .or_default()
                .push(occurrence(
                    normalize_variable_name(kind, &name),
                    source,
                    node_range(value),
                ));
        }
        if profile
            .saved_event_target_keys
            .contains(&key_name.to_ascii_lowercase())
            && let Some(name) = node_text(value)
        {
            bump_computed_count(count, limit)?;
            data.saved_event_targets.push(ScopedOccurrence {
                occurrence: occurrence(name, source, node_range(value)),
                scope: None,
            });
        }
        if let CstNode::Clause { children, .. } = value.as_ref() {
            if profile
                .effect_block_keys
                .contains(&key_name.to_ascii_lowercase())
            {
                bump_computed_count(count, limit)?;
                data.effect_blocks
                    .push(computed_block(key_name.clone(), source, *range));
            }
            if profile
                .trigger_block_keys
                .contains(&key_name.to_ascii_lowercase())
            {
                bump_computed_count(count, limit)?;
                data.trigger_blocks
                    .push(computed_block(key_name, source, *range));
            }
            collect_game_data_nodes(children, source, profile, data, count, limit)?;
        }
    }
    Ok(())
}

fn bump_computed_count(count: &mut usize, limit: usize) -> Result<(), ComputedDataError> {
    *count = count.saturating_add(1);
    if *count > limit {
        return Err(ComputedDataError::TooManyOccurrences { limit });
    }
    Ok(())
}

fn normalize_variable_name(kind: &str, name: &str) -> String {
    let name = name.split_once('@').map_or(name, |(_, suffix)| suffix);
    if kind.eq_ignore_ascii_case("variable") {
        name.rsplit('.')
            .next()
            .unwrap_or(name)
            .split_once('?')
            .map_or(name, |(value, _)| value)
            .to_owned()
    } else {
        name.to_owned()
    }
}

fn computed_block(key: String, source: &SnapshotSource, range: ByteRange) -> ComputedBlock {
    ComputedBlock {
        key,
        path: source.path.clone(),
        logical_path: source.logical_path.clone(),
        range,
    }
}

fn sort_scoped_occurrences(occurrences: &mut [ScopedOccurrence]) {
    occurrences.sort_by(|left, right| {
        (
            &left.occurrence.logical_path,
            &left.occurrence.path,
            left.occurrence.range.start,
            &left.occurrence.name,
            &left.scope,
        )
            .cmp(&(
                &right.occurrence.logical_path,
                &right.occurrence.path,
                right.occurrence.range.start,
                &right.occurrence.name,
                &right.scope,
            ))
    });
}

fn sort_blocks(blocks: &mut [ComputedBlock]) {
    blocks.sort_by(|left, right| {
        (&left.logical_path, &left.path, left.range.start, &left.key).cmp(&(
            &right.logical_path,
            &right.path,
            right.range.start,
            &right.key,
        ))
    });
}

/// Rebuilds typed references from the exact active `RuleCatalog` path.
///
/// References are admitted only when the selected rule RHS is a simple or
/// complex type and the value resolves to an existing typed definition.
/// Results replace the prior index only after the complete bounded pass.
///
/// # Errors
/// Returns an error when the reference limit is exceeded.
pub fn compute_rule_typed_references<F>(
    snapshot: &mut FullSnapshot,
    catalog: &RuleCatalog,
    max_references: usize,
    root_for: F,
) -> Result<(), TypedIndexError>
where
    F: FnMut(&SnapshotSource) -> Option<String>,
{
    compute_rule_typed_references_with(snapshot, catalog, max_references, root_for, |_, _| None)
}

/// Rebuilds precise references using a complete game `ValueScope` catalog.
///
/// # Errors
/// Returns an error when the shared reference limit is exceeded.
pub fn compute_catalog_typed_references<F>(
    snapshot: &mut FullSnapshot,
    catalog: &RuleCatalog,
    value_scope_catalog: &ValueScopeCatalog,
    max_references: usize,
    root_for: F,
) -> Result<(), TypedIndexError>
where
    F: FnMut(&SnapshotSource) -> Option<String>,
{
    compute_rule_typed_references_with_scope(
        snapshot,
        catalog,
        max_references,
        root_for,
        |_, value, scope| match value_scope_catalog.resolve(value, scope) {
            ValueScopeResolution::Reference(ReferenceHint::Type { type_name, value }) => {
                Some(DynamicTypeReference { type_name, value })
            }
            _ => None,
        },
    )
}

/// Rebuilds precise references, including caller-resolved value-scope references.
///
/// # Errors
/// Returns an error when the shared reference limit is exceeded.
pub fn compute_rule_typed_references_with<F, R>(
    snapshot: &mut FullSnapshot,
    catalog: &RuleCatalog,
    max_references: usize,
    root_for: F,
    mut resolve_value_scope: R,
) -> Result<(), TypedIndexError>
where
    F: FnMut(&SnapshotSource) -> Option<String>,
    R: FnMut(&SnapshotSource, &str) -> Option<DynamicTypeReference>,
{
    compute_rule_typed_references_with_scope(
        snapshot,
        catalog,
        max_references,
        root_for,
        |source, value, _| resolve_value_scope(source, value),
    )
}

/// Rebuilds precise references with caller-resolved value-scope and current scope.
///
/// # Errors
/// Returns an error when the shared reference limit is exceeded.
pub fn compute_rule_typed_references_with_scope<F, R>(
    snapshot: &mut FullSnapshot,
    catalog: &RuleCatalog,
    max_references: usize,
    mut root_for: F,
    mut resolve_value_scope: R,
) -> Result<(), TypedIndexError>
where
    F: FnMut(&SnapshotSource) -> Option<String>,
    R: FnMut(&SnapshotSource, &str, Option<&str>) -> Option<DynamicTypeReference>,
{
    let mut references: BTreeMap<String, BTreeMap<String, Vec<SymbolOccurrence>>> = BTreeMap::new();
    let mut details = Vec::new();
    let mut count = 0usize;
    for source in &snapshot.sources {
        let Some(root) = root_for(source) else {
            continue;
        };
        let extracted = match catalog.typed_references_with(
            &root,
            &source.text,
            max_references.saturating_sub(count),
            |value, scope| resolve_value_scope(source, value, scope),
        ) {
            Ok(extracted) => extracted,
            Err(QueryError::TooManyResults) => {
                return Err(TypedIndexError::TooManyOccurrences {
                    limit: max_references,
                });
            }
            Err(QueryError::ParseFailed | QueryError::InvalidOffset) => continue,
        };
        for reference in extracted {
            let Some(ids) = snapshot.typed_definitions.get(&reference.type_name) else {
                continue;
            };
            let Some(canonical) = ids
                .keys()
                .find(|id| id.eq_ignore_ascii_case(&reference.value))
            else {
                continue;
            };
            count = count.saturating_add(1);
            if count > max_references {
                return Err(TypedIndexError::TooManyOccurrences {
                    limit: max_references,
                });
            }
            let occurrence = occurrence(canonical.clone(), source, reference.range);
            references
                .entry(reference.type_name.clone())
                .or_default()
                .entry(canonical.clone())
                .or_default()
                .push(occurrence.clone());
            details.push(SnapshotReferenceDetail {
                occurrence,
                type_name: reference.type_name,
                is_outgoing: reference.is_outgoing,
                reference_label: reference.reference_label,
                fuzzy: reference.fuzzy,
                associated_type: reference.associated_type,
            });
        }
    }
    sort_typed_index(&mut references);
    details.sort_by(|left, right| {
        (
            &left.occurrence.logical_path,
            &left.occurrence.path,
            left.occurrence.range.start,
            &left.type_name,
            left.is_outgoing,
            &left.reference_label,
            left.fuzzy,
            &left.associated_type,
        )
            .cmp(&(
                &right.occurrence.logical_path,
                &right.occurrence.path,
                right.occurrence.range.start,
                &right.type_name,
                right.is_outgoing,
                &right.reference_label,
                right.fuzzy,
                &right.associated_type,
            ))
    });
    snapshot.typed_references = references;
    snapshot.reference_details = details;
    Ok(())
}

/// Rebuilds the snapshot diagnostic index using an immutable compiled rule catalog.
///
/// The resolver maps each source to a validation root. Returning `None` skips a
/// source. Results are replaced atomically only after the complete bounded pass.
///
/// # Errors
/// Returns an error when the diagnostic hard limit is exceeded.
pub fn compute_snapshot_diagnostics<F>(
    snapshot: &mut FullSnapshot,
    catalog: &RuleCatalog,
    max_diagnostics: usize,
    mut root_for: F,
) -> Result<(), SnapshotDiagnosticError>
where
    F: FnMut(&SnapshotSource) -> Option<String>,
{
    let mut diagnostics = Vec::new();
    for source in &snapshot.sources {
        let Some(root) = root_for(source) else {
            continue;
        };
        for diagnostic in catalog.validate_source(&root, &source.text).diagnostics {
            if diagnostics.len() >= max_diagnostics {
                return Err(SnapshotDiagnosticError::TooManyDiagnostics {
                    limit: max_diagnostics,
                });
            }
            diagnostics.push(SnapshotDiagnostic {
                path: source.path.clone(),
                logical_path: source.logical_path.clone(),
                code: diagnostic.code,
                message_key: diagnostic.message_key,
                key: diagnostic.key,
                args: diagnostic.args,
                range: diagnostic.range,
            });
        }
    }
    diagnostics.sort_by(|left, right| {
        (
            &left.logical_path,
            &left.path,
            left.range.start,
            left.range.end,
            &left.code,
            &left.key,
            &left.args,
        )
            .cmp(&(
                &right.logical_path,
                &right.path,
                right.range.start,
                right.range.end,
                &right.code,
                &right.key,
                &right.args,
            ))
    });
    snapshot.diagnostics = diagnostics;
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SnapshotDiagnosticError {
    TooManyDiagnostics { limit: usize },
}

impl std::fmt::Display for SnapshotDiagnosticError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooManyDiagnostics { limit } => {
                write!(formatter, "snapshot exceeds {limit} diagnostics")
            }
        }
    }
}

impl std::error::Error for SnapshotDiagnosticError {}

struct SnapshotIndexes<'a> {
    node_count: usize,
    max_nodes: usize,
    definitions: &'a mut BTreeMap<String, Vec<SymbolOccurrence>>,
    references: &'a mut BTreeMap<String, Vec<SymbolOccurrence>>,
    variables: &'a mut BTreeMap<String, Vec<SymbolOccurrence>>,
}

fn index_node(
    node: &CstNode,
    source: &SnapshotSource,
    top_level: bool,
    indexes: &mut SnapshotIndexes<'_>,
) -> Result<(), SnapshotError> {
    indexes.node_count = indexes.node_count.saturating_add(1);
    if indexes.node_count > indexes.max_nodes {
        return Err(SnapshotError::TooManyNodes {
            limit: indexes.max_nodes,
        });
    }
    if let CstNode::Assignment {
        key, value, range, ..
    } = node
    {
        if let Some(name) = node_text(key) {
            let occurrence = occurrence(name.clone(), source, *range);
            if top_level {
                indexes
                    .definitions
                    .entry(name.clone())
                    .or_default()
                    .push(occurrence.clone());
            }
            if name.starts_with('@') && !name.starts_with("@[") && !name.starts_with("@\\[") {
                indexes.variables.entry(name).or_default().push(occurrence);
            }
        }
        if let Some(name) = node_text(value) {
            indexes
                .references
                .entry(name.clone())
                .or_default()
                .push(occurrence(name, source, node_range(value)));
        }
        if let CstNode::Clause { children, .. } = value.as_ref() {
            for child in children {
                index_node(child, source, false, indexes)?;
            }
        }
    }
    Ok(())
}

fn occurrence(name: String, source: &SnapshotSource, range: ByteRange) -> SymbolOccurrence {
    occurrence_with_prefix(name, source, range, None)
}

fn occurrence_with_prefix(
    name: String,
    source: &SnapshotSource,
    range: ByteRange,
    key_prefix: Option<String>,
) -> SymbolOccurrence {
    SymbolOccurrence {
        name,
        path: source.path.clone(),
        logical_path: source.logical_path.clone(),
        range,
        key_prefix,
    }
}

fn node_text(node: &CstNode) -> Option<String> {
    match node {
        CstNode::Bare { token } => Some(token.value.clone()),
        CstNode::ColourLiteral { raw, .. } => Some(raw.clone()),
        _ => None,
    }
}

fn node_range(node: &CstNode) -> ByteRange {
    match node {
        CstNode::Bare { token }
        | CstNode::Comment { token }
        | CstNode::Trivia { token }
        | CstNode::Error { token } => token.range,
        CstNode::Assignment { range, .. }
        | CstNode::Clause { range, .. }
        | CstNode::ColourLiteral { range, .. } => *range,
    }
}

fn sort_index(index: &mut BTreeMap<String, Vec<SymbolOccurrence>>) {
    for occurrences in index.values_mut() {
        occurrences.sort_by(|left, right| {
            (&left.logical_path, &left.path, left.range.start).cmp(&(
                &right.logical_path,
                &right.path,
                right.range.start,
            ))
        });
    }
}

fn has_unsupported_bom(bytes: &[u8]) -> bool {
    bytes.starts_with(&[0xFF, 0xFE])
        || bytes.starts_with(&[0xFE, 0xFF])
        || bytes.starts_with(&[0x00, 0x00, 0xFE, 0xFF])
        || bytes.starts_with(&[0xFF, 0xFE, 0x00, 0x00])
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DlcInput {
    Archive { path: PathBuf, scope: String },
    Directory { path: PathBuf, scope: String },
}

#[derive(Debug)]
pub enum DlcError {
    Io(io::Error),
    TooManyDirectories { limit: usize },
}

impl std::fmt::Display for DlcError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "DLC discovery failed: {error}"),
            Self::TooManyDirectories { limit } => {
                write!(formatter, "DLC root exceeds {limit} directories")
            }
        }
    }
}

impl std::error::Error for DlcError {}

impl From<io::Error> for DlcError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

/// Selects one ZIP per immediate DLC directory, otherwise falls back to the directory.
///
/// Directory and file enumeration are sorted before selection so output does not depend
/// on platform enumeration order. ZIP extension matching is ASCII case-insensitive.
///
/// # Errors
/// Returns an error for filesystem failures or exceeded immediate-directory bounds.
pub fn discover_dlc_inputs(
    workspace_root: &Path,
    dlc_directory: &str,
    max_directories: usize,
) -> Result<Vec<DlcInput>, DlcError> {
    let root = workspace_root.join(dlc_directory);
    if !workspace_root.is_dir() || !root.is_dir() {
        return Ok(Vec::new());
    }
    let mut directories = Vec::new();
    for entry in fs::read_dir(&root)? {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            directories.push(entry.path());
        }
    }
    directories.sort();
    if directories.len() > max_directories {
        return Err(DlcError::TooManyDirectories {
            limit: max_directories,
        });
    }
    let fallback_scope = root.to_string_lossy().into_owned();
    let mut inputs = Vec::with_capacity(directories.len());
    for directory in directories {
        let mut files = Vec::new();
        for entry in fs::read_dir(&directory)? {
            let entry = entry?;
            if entry.file_type()?.is_file() {
                files.push(entry.path());
            }
        }
        files.sort();
        if let Some(archive) = files.into_iter().find(|path| {
            path.extension()
                .and_then(|extension| extension.to_str())
                .is_some_and(|extension| extension.eq_ignore_ascii_case("zip"))
        }) {
            let scope = archive
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("archive.zip")
                .to_owned();
            inputs.push(DlcInput::Archive {
                path: archive,
                scope,
            });
        } else {
            inputs.push(DlcInput::Directory {
                path: directory,
                scope: fallback_scope.clone(),
            });
        }
    }
    Ok(inputs)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArchiveResource {
    pub scope: String,
    pub uri: String,
    pub logical_path: String,
    pub text: Option<String>,
    pub admission: Admission,
}

#[derive(Debug)]
pub enum ArchiveError {
    Io(io::Error),
    Zip(zip::result::ZipError),
    TooManyEntries {
        limit: usize,
    },
    EntryTooLarge {
        entry: String,
        bytes: u64,
        limit: usize,
    },
    TotalTooLarge {
        bytes: u64,
        limit: u64,
    },
    UnsafePath(String),
    Decode {
        entry: String,
        offset: usize,
        message: &'static str,
    },
}

impl std::fmt::Display for ArchiveError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "archive I/O failed: {error}"),
            Self::Zip(error) => write!(formatter, "invalid ZIP archive: {error}"),
            Self::TooManyEntries { limit } => write!(formatter, "archive exceeds {limit} entries"),
            Self::EntryTooLarge {
                entry,
                bytes,
                limit,
            } => write!(
                formatter,
                "archive entry {entry} has {bytes} bytes; limit is {limit}"
            ),
            Self::TotalTooLarge { bytes, limit } => write!(
                formatter,
                "archive expands to {bytes} bytes; limit is {limit}"
            ),
            Self::UnsafePath(entry) => write!(formatter, "archive entry has unsafe path: {entry}"),
            Self::Decode {
                entry,
                offset,
                message,
            } => write!(
                formatter,
                "archive entry {entry} decode failed at byte {offset}: {message}"
            ),
        }
    }
}

impl std::error::Error for ArchiveError {}

impl From<io::Error> for ArchiveError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

impl From<zip::result::ZipError> for ArchiveError {
    fn from(error: zip::result::ZipError) -> Self {
        Self::Zip(error)
    }
}

/// Discovers admitted text resources from one DLC ZIP without extracting to disk.
///
/// # Errors
/// Returns an error for malformed archives, unsafe entry names, bounds, I/O, or decode failures.
pub fn discover_zip(
    archive_path: &Path,
    scope: &str,
    script_folders: &[String],
    encoding: TextEncoding,
    max_file_size_mb: u64,
) -> Result<Vec<ArchiveResource>, ArchiveError> {
    let archive_file = fs::File::open(archive_path)?;
    let mut archive = ZipArchive::new(archive_file)?;
    if archive.len() > MAX_ARCHIVE_ENTRIES {
        return Err(ArchiveError::TooManyEntries {
            limit: MAX_ARCHIVE_ENTRIES,
        });
    }
    let archive_root = archive_path
        .to_string_lossy()
        .replace('\\', "/")
        .trim_start_matches('.')
        .to_owned();
    let roots = [archive_root.clone()];
    let mut total = 0u64;
    let mut resources = Vec::new();
    for index in 0..archive.len() {
        let entry = archive.by_index(index)?;
        if entry.is_dir() {
            continue;
        }
        let entry_name = entry.name().replace('\\', "/");
        if unsafe_archive_path(&entry_name) {
            return Err(ArchiveError::UnsafePath(entry_name));
        }
        let bytes = entry.size();
        if bytes > MAX_ARCHIVE_ENTRY_BYTES as u64 {
            return Err(ArchiveError::EntryTooLarge {
                entry: entry_name,
                bytes,
                limit: MAX_ARCHIVE_ENTRY_BYTES,
            });
        }
        total = total.saturating_add(bytes);
        if total > MAX_ARCHIVE_TOTAL_BYTES {
            return Err(ArchiveError::TotalTooLarge {
                bytes: total,
                limit: MAX_ARCHIVE_TOTAL_BYTES,
            });
        }
        let uri = format!("uri:/{archive_root}/{entry_name}");
        let logical = logical_path(&uri, &roots, script_folders);
        let Some(admission) = admit(&logical, &entry_name, bytes, max_file_size_mb) else {
            continue;
        };
        if admission.kind == ResourceKind::File {
            resources.push(ArchiveResource {
                scope: scope.to_owned(),
                uri,
                logical_path: logical,
                text: None,
                admission,
            });
            continue;
        }
        let mut content =
            Vec::with_capacity(usize::try_from(bytes).unwrap_or(MAX_ARCHIVE_ENTRY_BYTES));
        entry
            .take((MAX_ARCHIVE_ENTRY_BYTES + 1) as u64)
            .read_to_end(&mut content)?;
        if content.len() > MAX_ARCHIVE_ENTRY_BYTES {
            return Err(ArchiveError::EntryTooLarge {
                entry: entry_name,
                bytes: content.len() as u64,
                limit: MAX_ARCHIVE_ENTRY_BYTES,
            });
        }
        if has_unsupported_bom(&content) {
            return Err(ArchiveError::Decode {
                entry: entry_name,
                offset: 0,
                message: "UTF-16/UTF-32 BOM is not supported",
            });
        }
        let content = content
            .strip_prefix(&[0xEF, 0xBB, 0xBF])
            .unwrap_or(&content);
        let script_encoding = match encoding {
            TextEncoding::Utf8 => ScriptEncoding::Utf8,
            TextEncoding::Windows1252 => ScriptEncoding::Windows1252,
        };
        let text = decode_script_bytes(content, script_encoding).map_err(|error| {
            ArchiveError::Decode {
                entry: entry_name.clone(),
                offset: error.offset,
                message: error.message,
            }
        })?;
        resources.push(ArchiveResource {
            scope: scope.to_owned(),
            uri,
            logical_path: logical,
            text: Some(text),
            admission,
        });
    }
    resources.sort_by(|left, right| left.uri.cmp(&right.uri));
    Ok(resources)
}

fn unsafe_archive_path(name: &str) -> bool {
    name.starts_with('/')
        || name.split('/').any(|segment| segment == "..")
        || name.as_bytes().get(1) == Some(&b':')
}

fn compile_globs(patterns: &[String]) -> Result<GlobSet, DiscoverError> {
    let mut builder = GlobSetBuilder::new();
    for pattern in patterns {
        let glob = Glob::new(pattern).map_err(|_| DiscoverError::InvalidGlob(pattern.clone()))?;
        builder.add(glob);
    }
    builder
        .build()
        .map_err(|_| DiscoverError::InvalidGlob("<set>".to_owned()))
}

fn folder_index(path: &str, folder: &str) -> Option<usize> {
    let folder = folder.replace('\\', "/");
    let prefix = format!("{folder}/");
    if path.starts_with(&prefix) {
        return Some(0);
    }
    path.find(&format!("/{prefix}")).map(|index| index + 1)
}

fn precedence(scope: &str) -> &str {
    if scope == "embedded" {
        ""
    } else if scope.is_empty() {
        "ZZZZZZZZ"
    } else {
        scope
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cwtools_rule_ir::parse_document;
    use cwtools_rules_engine::{RuleCatalog, ScopeUniverse};
    use std::path::Path;

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new(name: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "cwtools-workspace-{name}-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            fs::create_dir_all(&path).unwrap();
            Self(path)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn write(root: &Path, relative: &str, contents: &[u8]) {
        let path = root.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn discovery(root: &Path) -> DiscoveryOptions {
        DiscoveryOptions::bounded(
            root.to_owned(),
            "mod".to_owned(),
            vec![
                "events".to_owned(),
                "gfx".to_owned(),
                "common/inline_scripts".to_owned(),
            ],
        )
    }

    fn create_zip(path: &Path, entries: &[(&str, &[u8])]) {
        let file = fs::File::create(path).unwrap();
        let mut writer = zip::ZipWriter::new(file);
        for (name, content) in entries {
            writer
                .start_file(*name, zip::write::SimpleFileOptions::default())
                .unwrap();
            std::io::Write::write_all(&mut writer, content).unwrap();
        }
        writer.finish().unwrap();
    }

    fn resource(
        scope: &str,
        file: &'static str,
        logical: &str,
        validate: bool,
    ) -> Resource<&'static str> {
        Resource {
            scope: scope.into(),
            file_path: file.into(),
            logical_path: logical.into(),
            value: file,
            overwrite: Overwrite::Overwritten,
            validate,
        }
    }

    fn source(path: &str, logical: &str, text: &str, overwrite: Overwrite) -> SnapshotSource {
        SnapshotSource {
            scope: "mod".to_owned(),
            path: path.to_owned(),
            logical_path: logical.to_owned(),
            text: text.to_owned(),
            overwrite,
        }
    }

    #[test]
    fn full_snapshot_is_sorted_and_excludes_overwritten_sources() {
        let snapshot = compute_full_snapshot(
            vec![
                source("z.txt", "events/z.txt", "z = target", Overwrite::No),
                source(
                    "old.txt",
                    "events/a.txt",
                    "old = ignored",
                    Overwrite::Overwritten,
                ),
                source("a.txt", "events/a.txt", "a = target", Overwrite::Overwrote),
            ],
            SnapshotLimits::default(),
        )
        .unwrap();
        assert_eq!(
            snapshot
                .sources
                .iter()
                .map(|source| source.path.as_str())
                .collect::<Vec<_>>(),
            ["a.txt", "z.txt"]
        );
        assert_eq!(
            snapshot
                .definitions
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            ["a", "z"]
        );
        assert_eq!(snapshot.references["target"].len(), 2);
        assert!(!snapshot.definitions.contains_key("old"));
    }

    #[test]
    fn full_snapshot_indexes_variables_nested_references_and_parse_errors() {
        let snapshot = compute_full_snapshot(
            vec![
                source(
                    "vars.txt",
                    "common/scripted_variables/vars.txt",
                    "@foo = 1\nroot = { nested = @foo }",
                    Overwrite::No,
                ),
                source("bad.txt", "events/bad.txt", "bad = {", Overwrite::No),
            ],
            SnapshotLimits::default(),
        )
        .unwrap();
        assert_eq!(snapshot.variables["@foo"].len(), 1);
        assert_eq!(snapshot.references["@foo"].len(), 1);
        assert_eq!(snapshot.references["1"].len(), 1);
        assert_eq!(snapshot.parse_errors.len(), 1);
        assert_eq!(snapshot.parse_errors[0].path, "bad.txt");
    }

    #[test]
    fn snapshot_diagnostics_are_sorted_replace_atomically_and_keep_wire_fields() {
        let document = parse_document("rules.cwt", "root = { known = bool }").unwrap();
        let catalog = RuleCatalog::compile(&[document], ScopeUniverse::default()).unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![
                source("b.txt", "events/b.txt", "unknown = x", Overwrite::No),
                source("a.txt", "events/a.txt", "known = maybe", Overwrite::No),
            ],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_snapshot_diagnostics(&mut snapshot, &catalog, 10, |_| Some("root".to_owned()))
            .unwrap();
        assert_eq!(snapshot.diagnostics.len(), 3);
        assert_eq!(snapshot.diagnostics[0].path, "a.txt");
        assert_eq!(snapshot.diagnostics[0].code, "RULE120");
        assert_eq!(snapshot.diagnostics[0].message_key, "rules.invalid_value");
        assert!(
            snapshot.diagnostics[1..]
                .iter()
                .all(|diagnostic| diagnostic.path == "b.txt")
        );
        assert!(
            snapshot
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "RULE101")
        );
        assert!(
            snapshot
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "RULE110")
        );
        let before = snapshot.diagnostics.clone();
        assert!(matches!(
            compute_snapshot_diagnostics(&mut snapshot, &catalog, 1, |_| Some("root".to_owned())),
            Err(SnapshotDiagnosticError::TooManyDiagnostics { limit: 1 })
        ));
        assert_eq!(snapshot.diagnostics, before);
    }

    #[test]
    fn snapshot_diagnostics_resolver_can_skip_sources() {
        let document = parse_document("rules.cwt", "root = { known = bool }").unwrap();
        let catalog = RuleCatalog::compile(&[document], ScopeUniverse::default()).unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![source(
                "a.txt",
                "events/a.txt",
                "unknown = x",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_snapshot_diagnostics(&mut snapshot, &catalog, 10, |_| None).unwrap();
        assert!(snapshot.diagnostics.is_empty());
    }

    fn computed_profile() -> GameComputedProfile {
        GameComputedProfile {
            variable_set_keys: BTreeMap::from([
                ("set_variable".to_owned(), "variable".to_owned()),
                ("set_flag".to_owned(), "flag".to_owned()),
            ]),
            saved_event_target_keys: BTreeSet::from(["save_event_target_as".to_owned()]),
            effect_block_keys: BTreeSet::from(["effects".to_owned()]),
            trigger_block_keys: BTreeSet::from(["triggers".to_owned()]),
            ..GameComputedProfile::default()
        }
    }

    #[test]
    fn rule_game_data_replaces_assignment_heuristics() {
        let rules = parse_document(
            "rules.cwt",
            "alias[effect:do_effect] = scalar alias[trigger:has_flag] = scalar root = { variable = value_set[variable] ## push_scope = country\n nested = { target = value_set[event_target] } effects = { alias[effect] = scalar } triggers = { alias[trigger] = scalar } scalar = scalar }",
        ).unwrap();
        let catalog =
            RuleCatalog::compile(std::slice::from_ref(&rules), ScopeUniverse::default()).unwrap();
        let snapshot = compute_full_snapshot(
            vec![source(
                "a.txt",
                "events/a.txt",
                "variable = scope@foo.bar?x nested = { target = target_a } effects = { do_effect = yes } triggers = { has_flag = yes } scalar = looks_like_variable",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        ).unwrap();
        let data =
            compute_rule_game_data(&snapshot, &catalog, 10, |_| Some("root".to_owned())).unwrap();
        assert_eq!(data.defined_variables["variable"][0].name, "bar");
        assert_eq!(data.saved_event_targets[0].occurrence.name, "target_a");
        assert_eq!(
            data.saved_event_targets[0].scope.as_deref(),
            Some("country")
        );
        assert_eq!(data.effect_blocks.len(), 1);
        assert_eq!(data.trigger_blocks.len(), 1);
        assert_eq!(data.effect_blocks[0].key, "effect");
    }

    #[test]
    fn rule_game_data_is_bounded_before_result_publication() {
        let rules = parse_document(
            "rules.cwt",
            "root = { variable = value_set[variable] flag = value_set[flag] }",
        )
        .unwrap();
        let catalog =
            RuleCatalog::compile(std::slice::from_ref(&rules), ScopeUniverse::default()).unwrap();
        let snapshot = compute_full_snapshot(
            vec![source(
                "a.txt",
                "events/a.txt",
                "variable = one flag = two",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        )
        .unwrap();
        assert!(matches!(
            compute_rule_game_data(&snapshot, &catalog, 1, |_| Some("root".to_owned())),
            Err(ComputedDataError::TooManyOccurrences { limit: 1 })
        ));
    }

    #[test]
    fn game_computed_data_is_recursive_sorted_and_normalized() {
        let snapshot = compute_full_snapshot(
            vec![
                source("b.txt", "events/b.txt", "effects = { set_flag = beta }", Overwrite::No),
                source(
                    "a.txt",
                    "events/a.txt",
                    "set_variable = scope@foo.bar?value save_event_target_as = target_a triggers = { nested = { set_flag = alpha } }",
                    Overwrite::No,
                ),
            ],
            SnapshotLimits::default(),
        ).unwrap();
        let data = compute_game_data(&snapshot, &computed_profile(), 20).unwrap();
        assert_eq!(
            data.defined_variables["variable"]
                .iter()
                .map(|item| item.name.as_str())
                .collect::<Vec<_>>(),
            ["bar"]
        );
        assert_eq!(
            data.defined_variables["flag"]
                .iter()
                .map(|item| item.name.as_str())
                .collect::<Vec<_>>(),
            ["alpha", "beta"]
        );
        assert_eq!(data.saved_event_targets[0].occurrence.name, "target_a");
        assert_eq!(data.effect_blocks[0].path, "b.txt");
        assert_eq!(data.trigger_blocks[0].path, "a.txt");
    }

    #[test]
    fn eu4_and_stellaris_profiles_extract_path_scoped_parameters() {
        let snapshot = compute_full_snapshot(
            vec![
                source(
                    "effects.txt",
                    "COMMON/SCRIPTED_EFFECTS/effects.txt",
                    "not_event scripted = { key = $FIRST|fallback$ nested = [[SECOND]yes }",
                    Overwrite::No,
                ),
                source(
                    "values.txt",
                    "common/script_values/values.txt",
                    "value_a = { amount = $VALUE$ guard = [[CHECK] }",
                    Overwrite::No,
                ),
                source(
                    "events.txt",
                    "events/ignored.txt",
                    "event = { value = $IGNORED$ }",
                    Overwrite::No,
                ),
            ],
            SnapshotLimits::default(),
        )
        .unwrap();
        assert!(
            snapshot.parse_errors.is_empty(),
            "{:?}",
            snapshot.parse_errors
        );
        let eu4 = compute_game_data(&snapshot, &eu4_computed_profile(), 20).unwrap();
        assert_eq!(
            eu4.scripted_effect_params["effects.txt"],
            ["FIRST", "SECOND"]
        );
        assert!(eu4.script_value_params.is_empty());
        let stellaris = compute_game_data(&snapshot, &stellaris_computed_profile(), 20).unwrap();
        assert_eq!(
            stellaris.scripted_effect_params["effects.txt"],
            ["FIRST", "SECOND"]
        );
        assert_eq!(
            stellaris.script_value_params["values.txt"],
            ["CHECK", "VALUE"]
        );
        assert!(!stellaris.scripted_effect_params.contains_key("events.txt"));
    }

    #[test]
    fn game_specific_parameter_extraction_shares_hard_bound() {
        let snapshot = compute_full_snapshot(
            vec![source(
                "effects.txt",
                "common/scripted_effects/effects.txt",
                "effect = { one = $A$ two = [[B] }",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        )
        .unwrap();
        assert!(matches!(
            compute_game_data(&snapshot, &eu4_computed_profile(), 1),
            Err(ComputedDataError::TooManyOccurrences { limit: 1 })
        ));
    }

    #[test]
    fn game_computed_data_is_bounded_without_partial_result() {
        let snapshot = compute_full_snapshot(
            vec![source(
                "a.txt",
                "events/a.txt",
                "set_flag = one save_event_target_as = two",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        )
        .unwrap();
        assert!(matches!(
            compute_game_data(&snapshot, &computed_profile(), 1),
            Err(ComputedDataError::TooManyOccurrences { limit: 1 })
        ));
    }

    #[test]
    fn rule_typed_references_replace_generic_false_positives() {
        let rules = parse_document(
            "rules.cwt",
            "types = { type[event] = { path = events } type[technology] = { path = common/technology } } root = { ## incomingReferenceLabel = source\n target = <event> nested = { technology = pre<technology>suf scalar = scalar } }",
        ).unwrap();
        let catalog =
            RuleCatalog::compile(std::slice::from_ref(&rules), ScopeUniverse::default()).unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![
                source("event.txt", "events/a.txt", "event_a = { }", Overwrite::No),
                source(
                    "tech.txt",
                    "common/technology/a.txt",
                    "tech_a = { }",
                    Overwrite::No,
                ),
                source(
                    "use.txt",
                    "script/use.txt",
                    "target = event_a nested = { technology = pretech_asuf scalar = event_a }",
                    Overwrite::No,
                ),
            ],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_typed_indexes(&mut snapshot, &rules.types, 100).unwrap();
        assert_eq!(snapshot.typed_references["event"]["event_a"].len(), 2);
        compute_rule_typed_references(&mut snapshot, &catalog, 10, |source| {
            (source.path == "use.txt").then(|| "root".to_owned())
        })
        .unwrap();
        assert_eq!(snapshot.typed_references["event"]["event_a"].len(), 1);
        assert_eq!(snapshot.typed_references["technology"]["tech_a"].len(), 1);
        assert_eq!(snapshot.reference_details.len(), 2);
        assert!(!snapshot.reference_details[0].is_outgoing);
        assert_eq!(
            snapshot.reference_details[0].reference_label.as_deref(),
            Some("source")
        );
        assert!(!snapshot.reference_details[0].fuzzy);
        assert!(snapshot.reference_details[1].fuzzy);
    }

    #[test]
    fn rule_typed_references_accept_value_scope_resolver() {
        let rules = parse_document(
            "rules.cwt",
            "types = { type[script_value] = { path = common/script_values } } root = { amount = value_field }",
        )
        .unwrap();
        let catalog =
            RuleCatalog::compile(std::slice::from_ref(&rules), ScopeUniverse::default()).unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![
                source(
                    "definition.txt",
                    "common/script_values/a.txt",
                    "value_a = { }",
                    Overwrite::No,
                ),
                source(
                    "use.txt",
                    "script/use.txt",
                    "amount = value_a|fallback",
                    Overwrite::No,
                ),
            ],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_typed_indexes(&mut snapshot, &rules.types, 100).unwrap();
        compute_rule_typed_references_with(
            &mut snapshot,
            &catalog,
            10,
            |source| (source.path == "use.txt").then(|| "root".to_owned()),
            |source, value| {
                (source.path == "use.txt" && value == "value_a").then(|| DynamicTypeReference {
                    type_name: "script_value".into(),
                    value: value.into(),
                })
            },
        )
        .unwrap();
        assert_eq!(
            snapshot.typed_references["script_value"]["value_a"].len(),
            1
        );
        assert_eq!(snapshot.reference_details[0].type_name, "script_value");
        assert_eq!(snapshot.reference_details[0].associated_type, None);
    }

    #[test]
    fn catalog_typed_references_resolve_with_rule_scope() {
        let rules = parse_document(
            "rules.cwt",
            "types = { type[script_value] = { path = common/script_values } }
## push_scope = country
root = { amount = value_field }",
        )
        .unwrap();
        let catalog =
            RuleCatalog::compile(std::slice::from_ref(&rules), ScopeUniverse::default()).unwrap();
        let value_scopes = ValueScopeCatalog::build(
            cwtools_scopes::ValueScopeCatalogInput {
                value_triggers: vec![cwtools_scopes::ValueScopeEntry {
                    name: "value_a".into(),
                    scopes: vec!["country".into()],
                    target_scope: None,
                    reference_hint: Some(ReferenceHint::Type {
                        type_name: "script_value".into(),
                        value: "value_a".into(),
                    }),
                }],
                ..cwtools_scopes::ValueScopeCatalogInput::default()
            },
            10,
        )
        .unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![
                source(
                    "definition.txt",
                    "common/script_values/a.txt",
                    "value_a = { }",
                    Overwrite::No,
                ),
                source(
                    "use.txt",
                    "script/use.txt",
                    "amount = value_a|fallback",
                    Overwrite::No,
                ),
            ],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_typed_indexes(&mut snapshot, &rules.types, 100).unwrap();
        compute_catalog_typed_references(&mut snapshot, &catalog, &value_scopes, 10, |source| {
            (source.path == "use.txt").then(|| "root".to_owned())
        })
        .unwrap();
        assert_eq!(
            snapshot.typed_references["script_value"]["value_a"].len(),
            1
        );
    }

    #[test]
    fn rule_typed_references_are_atomic_and_bounded() {
        let rules = parse_document(
            "rules.cwt",
            "types = { type[event] = { path = events } } root = { target = <event> }",
        )
        .unwrap();
        let catalog =
            RuleCatalog::compile(std::slice::from_ref(&rules), ScopeUniverse::default()).unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![
                source("event.txt", "events/a.txt", "event_a = { }", Overwrite::No),
                source(
                    "use.txt",
                    "script/use.txt",
                    "target = event_a",
                    Overwrite::No,
                ),
            ],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_typed_indexes(&mut snapshot, &rules.types, 100).unwrap();
        let before = snapshot.typed_references.clone();
        assert!(matches!(
            compute_rule_typed_references(&mut snapshot, &catalog, 0, |_| Some("root".to_owned())),
            Err(TypedIndexError::TooManyOccurrences { limit: 0 })
        ));
        assert_eq!(snapshot.typed_references, before);
    }

    #[test]
    fn typed_indexes_use_paths_name_fields_and_known_ids() {
        let rules = parse_document(
            "types.cwt",
            "types = { type[event] = { path = \"events\" name_field = id } type[technology] = { path = \"common/technology\" } }",
        ).unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![
                source(
                    "events.txt",
                    "events/a.txt",
                    "wrapper = { id = event_a target = tech_a }",
                    Overwrite::No,
                ),
                source(
                    "tech.txt",
                    "common/technology/t.txt",
                    "tech_a = { target = event_a }",
                    Overwrite::No,
                ),
                source(
                    "other.txt",
                    "common/other/o.txt",
                    "ignored = event_a",
                    Overwrite::No,
                ),
            ],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_typed_indexes(&mut snapshot, &rules.types, 20).unwrap();
        assert!(snapshot.typed_definitions["event"].contains_key("event_a"));
        assert!(snapshot.typed_definitions["technology"].contains_key("tech_a"));
        assert_eq!(snapshot.typed_references["event"]["event_a"].len(), 2);
        assert_eq!(snapshot.typed_references["technology"]["tech_a"].len(), 1);
    }

    #[test]
    fn typed_indexes_match_jomini_key_prefix_exactly() {
        let rules = parse_document(
            "types.cwt",
            "types = { type[prefixed] = { path = events type_key_prefix = not_event } type[plain] = { path = events } }",
        )
        .unwrap();
        assert_eq!(rules.types[0].key_prefix.as_deref(), Some("not_event"));
        let mut snapshot = compute_full_snapshot(
            vec![source(
                "events.txt",
                "events/a.txt",
                "not_event country_event = { } country_event = { } other country_event = { }",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_typed_indexes(&mut snapshot, &rules.types, 20).unwrap();
        assert_eq!(
            snapshot.typed_definitions["prefixed"]["country_event"].len(),
            1
        );
        assert_eq!(
            snapshot.typed_definitions["prefixed"]["country_event"][0]
                .key_prefix
                .as_deref(),
            Some("not_event")
        );
        assert_eq!(
            snapshot.typed_definitions["plain"]["country_event"].len(),
            1
        );
    }

    #[test]
    fn typed_indexes_support_per_file_filters_and_atomic_limits() {
        let rules = parse_document(
            "types.cwt",
            "types = { type[ship] = { path = \"ships\" type_per_file = yes starts_with = PRE_ALLOWED } }",
        ).unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![
                source(
                    "allowed",
                    "ships/pre_allowed_one.txt",
                    "x = yes",
                    Overwrite::No,
                ),
                source("blocked", "ships/pre_blocked.txt", "x = yes", Overwrite::No),
            ],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_typed_indexes(&mut snapshot, &rules.types, 10).unwrap();
        assert!(snapshot.typed_definitions["ship"].contains_key("pre_allowed_one"));
        assert!(!snapshot.typed_definitions["ship"].contains_key("blocked"));
        let before = snapshot.typed_definitions.clone();
        assert!(matches!(
            compute_typed_indexes(&mut snapshot, &rules.types, 0),
            Err(TypedIndexError::TooManyOccurrences { limit: 0 })
        ));
        assert_eq!(snapshot.typed_definitions, before);
    }

    #[test]
    fn typed_indexes_apply_case_insensitive_regex_and_skip_root_paths() {
        let rules = parse_document(
            "types.cwt",
            "types = { type[event] = { path = events skip_root_key = { wrapper inner } type_key_regex = \"^event_[0-9]+$\" } }",
        ).unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![source(
                "events.txt",
                "events/a.txt",
                "wrapper = { inner = { EVENT_1 = yes other = no } ignored = { event_2 = yes } }",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_typed_indexes(&mut snapshot, &rules.types, 10).unwrap();
        assert!(snapshot.typed_definitions["event"].contains_key("EVENT_1"));
        assert!(!snapshot.typed_definitions["event"].contains_key("other"));
        assert!(!snapshot.typed_definitions["event"].contains_key("event_2"));
    }

    #[test]
    fn typed_indexes_support_any_and_negated_multiple_skip_root() {
        let rules = parse_document(
            "types.cwt",
            "types = { type[any_type] = { path = events skip_root_key = { any } } type[negated] = { path = events skip_root_key != blocked skip_root_key != ignored } }",
        ).unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![source(
                "events.txt",
                "events/a.txt",
                "open = { first = yes } blocked = { bad = yes } allowed = { good = yes }",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_typed_indexes(&mut snapshot, &rules.types, 20).unwrap();
        assert!(snapshot.typed_definitions["any_type"].contains_key("first"));
        assert!(snapshot.typed_definitions["any_type"].contains_key("bad"));
        assert!(snapshot.typed_definitions["negated"].contains_key("first"));
        assert!(snapshot.typed_definitions["negated"].contains_key("good"));
        assert!(!snapshot.typed_definitions["negated"].contains_key("bad"));
    }

    #[test]
    fn invalid_type_key_regex_matches_nothing_without_partial_publication() {
        let rules = parse_document(
            "types.cwt",
            "types = { type[broken] = { path = events type_key_regex = \"[\" } }",
        )
        .unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![source(
                "events.txt",
                "events/a.txt",
                "event = yes",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_typed_indexes(&mut snapshot, &rules.types, 10).unwrap();
        assert!(!snapshot.typed_definitions.contains_key("broken"));
    }

    #[test]
    fn rule_typed_subtypes_use_full_validation_and_publish_atomically() {
        let rules = parse_document(
            "types.cwt",
            "types = { type[event] = { path = events subtype[valid] = { marker = scalar } subtype[invalid] = { marker = bool } } }",
        )
        .unwrap();
        let catalog =
            RuleCatalog::compile(std::slice::from_ref(&rules), ScopeUniverse::default()).unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![source(
                "events.txt",
                "events/a.txt",
                "event_a = { marker = maybe }",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_rule_typed_subtypes(&mut snapshot, &catalog, &rules.types, 10).unwrap();
        assert!(snapshot.typed_subtypes["event.valid"].contains_key("event_a"));
        assert!(!snapshot.typed_subtypes.contains_key("event.invalid"));
        let before = snapshot.typed_subtypes.clone();
        assert!(matches!(
            compute_rule_typed_subtypes(&mut snapshot, &catalog, &rules.types, 0),
            Err(TypedIndexError::TooManyOccurrences { limit: 0 })
        ));
        assert_eq!(snapshot.typed_subtypes, before);
    }

    #[test]
    fn typed_subtypes_apply_selectors_rules_and_only_if_not() {
        let rules = parse_document(
            "types.cwt",
            "types = {\n type[event] = {\n  path = events\n  ## type_key_field = country_event\n  ## type_key_regex = ^country_\n  ## starts_with = country_\n  subtype[country] = { kind = country }\n  ## type_key_regex = ^country_\n  ## only_if_not = country\n  subtype[fallback] = { kind = country }\n }\n}",
        ).unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![source(
                "events.txt",
                "events/a.txt",
                "country_event = { id = event_a kind = country } country_other = { kind = ship } fleet_event = { kind = country }",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        ).unwrap();
        assert_eq!(
            rules.types[0].subtypes[0].type_key_field.as_deref(),
            Some("country_event")
        );
        assert_eq!(
            rules.types[0].subtypes[0].type_key_regex.as_deref(),
            Some("^country_")
        );
        compute_typed_indexes(&mut snapshot, &rules.types, 20).unwrap();
        assert!(snapshot.typed_subtypes["event.country"].contains_key("country_event"));
        assert!(!snapshot.typed_subtypes.contains_key("event.fallback"));
    }

    #[test]
    fn typed_subtypes_publish_atomically_under_shared_limit() {
        let rules = parse_document(
            "types.cwt",
            "types = { type[event] = { path = events subtype[all] = { } } }",
        )
        .unwrap();
        let mut snapshot = compute_full_snapshot(
            vec![source(
                "events.txt",
                "events/a.txt",
                "event_a = { }",
                Overwrite::No,
            )],
            SnapshotLimits::default(),
        )
        .unwrap();
        compute_typed_indexes(&mut snapshot, &rules.types, 2).unwrap();
        let before_definitions = snapshot.typed_definitions.clone();
        let before_subtypes = snapshot.typed_subtypes.clone();
        assert!(matches!(
            compute_typed_indexes(&mut snapshot, &rules.types, 1),
            Err(TypedIndexError::TooManyOccurrences { limit: 1 })
        ));
        assert_eq!(snapshot.typed_definitions, before_definitions);
        assert_eq!(snapshot.typed_subtypes, before_subtypes);
    }

    #[test]
    fn full_snapshot_enforces_source_and_node_bounds() {
        let sources = vec![
            source("a", "a", "a = 1", Overwrite::No),
            source("b", "b", "b = 2", Overwrite::No),
        ];
        assert!(matches!(
            compute_full_snapshot(
                sources.clone(),
                SnapshotLimits {
                    max_sources: 1,
                    max_nodes: 10
                }
            ),
            Err(SnapshotError::TooManySources { limit: 1 })
        ));
        assert!(matches!(
            compute_full_snapshot(
                sources,
                SnapshotLimits {
                    max_sources: 10,
                    max_nodes: 1
                }
            ),
            Err(SnapshotError::TooManyNodes { limit: 1 })
        ));
    }

    #[test]
    fn dlc_selector_prefers_sorted_case_insensitive_zip_and_falls_back() {
        let root = TestDirectory::new("dlc-inputs");
        fs::create_dir_all(root.path().join("dlc/dlc_a")).unwrap();
        fs::create_dir_all(root.path().join("dlc/dlc_b/events")).unwrap();
        create_zip(
            &root.path().join("dlc/dlc_a/z.ZIP"),
            &[("events/z.txt", b"z")],
        );
        create_zip(
            &root.path().join("dlc/dlc_a/a.zip"),
            &[("events/a.txt", b"a")],
        );
        write(root.path(), "dlc/dlc_b/events/b.txt", b"b");
        let inputs = discover_dlc_inputs(root.path(), "dlc", 10).unwrap();
        assert_eq!(inputs.len(), 2);
        match &inputs[0] {
            DlcInput::Archive { path, scope } => {
                assert!(path.ends_with("a.zip"));
                assert_eq!(scope, "a.zip");
            }
            DlcInput::Directory { .. } => panic!("expected archive"),
        }
        match &inputs[1] {
            DlcInput::Directory { path, scope } => {
                assert!(path.ends_with("dlc_b"));
                assert_eq!(scope, &root.path().join("dlc").to_string_lossy());
            }
            DlcInput::Archive { .. } => panic!("expected directory fallback"),
        }
    }

    #[test]
    fn dlc_selector_handles_missing_roots_and_directory_bound() {
        let root = TestDirectory::new("dlc-bounds");
        assert!(
            discover_dlc_inputs(root.path(), "missing", 1)
                .unwrap()
                .is_empty()
        );
        fs::create_dir_all(root.path().join("dlc/a")).unwrap();
        fs::create_dir_all(root.path().join("dlc/b")).unwrap();
        assert!(matches!(
            discover_dlc_inputs(root.path(), "dlc", 1),
            Err(DlcError::TooManyDirectories { limit: 1 })
        ));
    }

    #[test]
    fn zip_discovery_is_sorted_admitted_and_decoded() {
        let root = TestDirectory::new("zip");
        let archive = root.path().join("dlc.zip");
        create_zip(
            &archive,
            &[
                ("events/z.txt", b"z = yes"),
                ("events/a.txt", b"\xEF\xBB\xBFa = yes"),
                ("gfx/a.dds", b"binary"),
                ("events/skip.bin", b"skip"),
            ],
        );
        let resources = discover_zip(
            &archive,
            "dlc.zip",
            &["events".to_owned(), "gfx".to_owned()],
            TextEncoding::Utf8,
            1,
        )
        .unwrap();
        assert_eq!(
            resources
                .iter()
                .map(|resource| resource.logical_path.as_str())
                .collect::<Vec<_>>(),
            ["events/a.txt", "events/z.txt", "gfx/a.dds"]
        );
        assert_eq!(resources[0].text.as_deref(), Some("a = yes"));
        assert_eq!(resources[2].text, None);
        assert!(resources.iter().all(|resource| resource.scope == "dlc.zip"));
    }

    #[test]
    fn zip_discovery_rejects_unsafe_paths_and_invalid_utf8() {
        let root = TestDirectory::new("zip-errors");
        let unsafe_zip = root.path().join("unsafe.zip");
        create_zip(&unsafe_zip, &[("../events/a.txt", b"a")]);
        assert!(matches!(
            discover_zip(
                &unsafe_zip,
                "unsafe.zip",
                &["events".to_owned()],
                TextEncoding::Utf8,
                1
            ),
            Err(ArchiveError::UnsafePath(_))
        ));
        let invalid_zip = root.path().join("invalid.zip");
        create_zip(&invalid_zip, &[("events/a.txt", &[0xFF])]);
        assert!(matches!(
            discover_zip(
                &invalid_zip,
                "invalid.zip",
                &["events".to_owned()],
                TextEncoding::Utf8,
                1
            ),
            Err(ArchiveError::Decode { offset: 0, .. })
        ));
    }

    #[test]
    fn text_reader_strips_utf8_bom_and_decodes_cp1252() {
        let root = TestDirectory::new("encoding");
        write(root.path(), "utf8.txt", b"\xEF\xBB\xBFname = snow");
        write(root.path(), "cp1252.txt", &[b'x', b' ', b'=', b' ', 0x80]);
        assert_eq!(
            read_text(&root.path().join("utf8.txt"), TextEncoding::Utf8, 100).unwrap(),
            "name = snow"
        );
        assert_eq!(
            read_text(
                &root.path().join("cp1252.txt"),
                TextEncoding::Windows1252,
                100
            )
            .unwrap(),
            "x = €"
        );
    }

    #[test]
    fn text_reader_rejects_invalid_utf8_unsupported_bom_and_oversize() {
        let root = TestDirectory::new("encoding-errors");
        write(root.path(), "invalid.txt", &[0xFF]);
        write(root.path(), "utf16.txt", &[0xFF, 0xFE, b'x', 0]);
        write(root.path(), "large.txt", b"1234");
        assert!(matches!(
            read_text(&root.path().join("invalid.txt"), TextEncoding::Utf8, 10),
            Err(ReadTextError::Decode { offset: 0, .. })
        ));
        assert!(matches!(
            read_text(
                &root.path().join("utf16.txt"),
                TextEncoding::Windows1252,
                10
            ),
            Err(ReadTextError::UnsupportedBom)
        ));
        assert!(matches!(
            read_text(&root.path().join("large.txt"), TextEncoding::Utf8, 3),
            Err(ReadTextError::TooLarge { bytes: 4, limit: 3 })
        ));
    }

    #[test]
    fn text_reader_handles_empty_file() {
        let root = TestDirectory::new("empty");
        write(root.path(), "empty.txt", b"");
        assert_eq!(
            read_text(
                &root.path().join("empty.txt"),
                TextEncoding::Utf8,
                MAX_TEXT_BYTES
            )
            .unwrap(),
            ""
        );
    }

    #[test]
    fn discovery_is_sorted_filters_globs_and_admits_known_files() {
        let root = TestDirectory::new("discover");
        write(root.path(), "events/z.txt", b"z");
        write(root.path(), "events/a.txt", b"a");
        write(root.path(), "events/ignored/skip.txt", b"skip");
        write(root.path(), "events/unknown.bin", b"bin");
        write(root.path(), "gfx/a.dds", b"dds");
        let mut options = discovery(root.path());
        options.ignore_globs = vec!["**/ignored/**".to_owned()];
        let files = discover(&options).unwrap();
        assert_eq!(
            files
                .iter()
                .map(|file| file.logical_path.as_str())
                .collect::<Vec<_>>(),
            ["events/a.txt", "events/z.txt", "gfx/a.dds"]
        );
        assert_eq!(files[2].admission.kind, ResourceKind::File);
    }

    #[test]
    fn discovery_enforces_file_and_depth_bounds() {
        let root = TestDirectory::new("bounds");
        write(root.path(), "events/a.txt", b"a");
        write(root.path(), "events/b.txt", b"b");
        let mut options = discovery(root.path());
        options.max_files = 1;
        assert!(matches!(
            discover(&options),
            Err(DiscoverError::TooManyFiles { limit: 1 })
        ));
        options.max_files = 10;
        options.max_depth = 0;
        assert!(matches!(
            discover(&options),
            Err(DiscoverError::TooDeep { limit: 0 })
        ));
    }

    #[test]
    fn discovery_rejects_invalid_globs() {
        let root = TestDirectory::new("glob");
        let mut options = discovery(root.path());
        options.ignore_globs = vec!["[".to_owned()];
        assert!(matches!(
            discover(&options),
            Err(DiscoverError::InvalidGlob(_))
        ));
    }

    #[test]
    fn logical_path_normalizes_and_uses_earliest_script_folder() {
        assert_eq!(
            logical_path(
                r"C:\mods\x\common\inline_scripts\events\a",
                &["C:/mods/x".into()],
                &["events".into(), "common/inline_scripts".into()],
            ),
            "common/inline_scripts/events/a"
        );
        assert_eq!(
            logical_path(
                "/root/mod/gfx/models/a.mesh",
                &["/root/mod/".into()],
                &["gfx".into()],
            ),
            "gfx/models/a.mesh"
        );
    }

    #[test]
    fn admission_matches_extension_categories_and_bounds() {
        assert_eq!(
            admit("events/a.txt", "a.txt", 10, 1),
            Some(Admission {
                kind: ResourceKind::Entity,
                validate: true
            })
        );
        assert_eq!(admit("events/a.txt", "a.txt", 1_000_001, 1), None);
        assert_eq!(
            admit("common/inline_scripts/a", "a", 10, 1),
            Some(Admission {
                kind: ResourceKind::Entity,
                validate: true
            })
        );
        assert_eq!(
            admit("gfx/a.shader", "a.shader", u64::MAX, 1),
            Some(Admission {
                kind: ResourceKind::Content,
                validate: true
            })
        );
        assert_eq!(
            admit("gfx/a.dds", "a.dds", u64::MAX, 1),
            Some(Admission {
                kind: ResourceKind::File,
                validate: false
            })
        );
        assert_eq!(admit("gfx/a.exe", "a.exe", 1, 1), None);
        assert_eq!(admit("events/A.TXT", "A.TXT", 1, 1), None);
    }

    #[test]
    fn extensionless_files_outside_inline_scripts_are_rejected() {
        assert_eq!(admit("events/a", "a", 1, 1), None);
    }

    #[test]
    fn singleton_is_not_an_override() {
        let snapshot = ResourceSnapshot::build(vec![resource("mod", "m/a.txt", "a.txt", true)]);
        assert_eq!(snapshot.resources()[0].overwrite, Overwrite::No);
    }

    #[test]
    fn blank_scope_wins_and_embedded_loses() {
        let snapshot = ResourceSnapshot::build(vec![
            resource("embedded", "e/a.txt", "a.txt", true),
            resource("MOD", "m/a.txt", "a.txt", true),
            resource("", "u/a.txt", "a.txt", true),
        ]);
        let active: Vec<_> = snapshot
            .active()
            .map(|resource| resource.file_path.as_str())
            .collect();
        assert_eq!(active, ["u/a.txt"]);
        assert_eq!(
            snapshot
                .resources()
                .iter()
                .filter(|resource| resource.overwrite == Overwrite::Overwritten)
                .count(),
            2
        );
    }

    #[test]
    fn lexical_scope_precedence_matches_reference() {
        let snapshot = ResourceSnapshot::build(vec![
            resource("base", "b/a.txt", "a.txt", true),
            resource("z_mod", "z/a.txt", "a.txt", true),
            resource("a_mod", "a/a.txt", "a.txt", true),
        ]);
        assert_eq!(snapshot.active().next().unwrap().scope, "z_mod");
    }

    #[test]
    fn validated_filters_inactive_and_non_validating_resources() {
        let snapshot = ResourceSnapshot::build(vec![
            resource("a", "a/a.txt", "a.txt", true),
            resource("b", "b/a.txt", "a.txt", false),
            resource("c", "c/b.txt", "b.txt", true),
        ]);
        assert_eq!(
            snapshot
                .validated()
                .map(|resource| resource.file_path.as_str())
                .collect::<Vec<_>>(),
            ["c/b.txt"]
        );
    }

    #[test]
    fn output_order_is_deterministic() {
        let snapshot = ResourceSnapshot::build(vec![
            resource("b", "z.txt", "b.txt", true),
            resource("a", "a.txt", "a.txt", true),
        ]);
        assert_eq!(
            snapshot
                .resources()
                .iter()
                .map(|resource| resource.logical_path.as_str())
                .collect::<Vec<_>>(),
            ["a.txt", "b.txt"]
        );
    }
}
