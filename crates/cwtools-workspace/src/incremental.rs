//! Bounded prepare/epoch-checked commit transactions for workspace snapshots.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

#[cfg(test)]
use crate::Overwrite;
use crate::{
    FullSnapshot, SnapshotError, SnapshotLimits, SnapshotSource, compute_full_snapshot,
    compute_full_snapshot_cancellable,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Change {
    Add(SnapshotSource),
    Edit {
        path: String,
        text: String,
    },
    Remove {
        path: String,
    },
    Rename {
        from: String,
        to: String,
        logical_path: String,
    },
    OpenOverlay {
        path: String,
        text: String,
    },
    SaveOverlay {
        path: String,
    },
    CloseOverlay {
        path: String,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IncrementalError {
    Cancelled,
    Stale { expected: u64, actual: u64 },
    DuplicatePath(String),
    MissingPath(String),
    OverlayAlreadyOpen(String),
    OverlayNotOpen(String),
    EpochExhausted,
    Snapshot(SnapshotError),
}

impl std::fmt::Display for IncrementalError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}
impl std::error::Error for IncrementalError {}
impl From<SnapshotError> for IncrementalError {
    fn from(value: SnapshotError) -> Self {
        if value == SnapshotError::Cancelled {
            Self::Cancelled
        } else {
            Self::Snapshot(value)
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedSnapshot {
    base_epoch: u64,
    disk: BTreeMap<String, SnapshotSource>,
    overlays: BTreeMap<String, String>,
    snapshot: FullSnapshot,
    fingerprint: u64,
}

impl PreparedSnapshot {
    #[must_use]
    pub const fn base_epoch(&self) -> u64 {
        self.base_epoch
    }
    #[must_use]
    pub const fn fingerprint(&self) -> u64 {
        self.fingerprint
    }
    #[must_use]
    pub fn snapshot(&self) -> &FullSnapshot {
        &self.snapshot
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IncrementalStore {
    epoch: u64,
    disk: BTreeMap<String, SnapshotSource>,
    overlays: BTreeMap<String, String>,
    snapshot: FullSnapshot,
    fingerprint: u64,
    limits: SnapshotLimits,
}

impl IncrementalStore {
    /// Creates a deterministic store from unique disk sources.
    ///
    /// # Errors
    /// Returns an error for duplicate paths or full-snapshot bounds.
    pub fn new(
        sources: Vec<SnapshotSource>,
        limits: SnapshotLimits,
    ) -> Result<Self, IncrementalError> {
        let disk = map_sources(sources)?;
        let snapshot = compute_full_snapshot(effective_sources(&disk, &BTreeMap::new()), limits)?;
        let fingerprint = semantic_fingerprint(&snapshot);
        Ok(Self {
            epoch: 0,
            disk,
            overlays: BTreeMap::new(),
            snapshot,
            fingerprint,
            limits,
        })
    }
    #[must_use]
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }
    #[must_use]
    pub const fn fingerprint(&self) -> u64 {
        self.fingerprint
    }
    #[must_use]
    pub fn snapshot(&self) -> &FullSnapshot {
        &self.snapshot
    }
    #[must_use]
    pub fn overlays(&self) -> usize {
        self.overlays.len()
    }

    /// Computes a complete candidate without publishing partial state.
    ///
    /// # Errors
    /// Returns an error for stale epochs, cancellation, invalid changes, or snapshot bounds.
    pub fn prepare(
        &self,
        base_epoch: u64,
        changes: &[Change],
        cancelled: &AtomicBool,
    ) -> Result<PreparedSnapshot, IncrementalError> {
        self.prepare_with(base_epoch, changes, cancelled, |_| Ok(()))
    }

    /// Computes a candidate and lets the caller populate owned semantic indexes before commit.
    ///
    /// The callback operates only on the private candidate, so diagnostic or typed-index errors
    /// cannot mutate the published snapshot.
    ///
    /// # Errors
    /// Returns an error from change application, snapshot computation, cancellation, or `enrich`.
    pub fn prepare_with<F>(
        &self,
        base_epoch: u64,
        changes: &[Change],
        cancelled: &AtomicBool,
        mut enrich: F,
    ) -> Result<PreparedSnapshot, IncrementalError>
    where
        F: FnMut(&mut FullSnapshot) -> Result<(), IncrementalError>,
    {
        if base_epoch != self.epoch {
            return Err(IncrementalError::Stale {
                expected: self.epoch,
                actual: base_epoch,
            });
        }
        if cancelled.load(Ordering::Relaxed) {
            return Err(IncrementalError::Cancelled);
        }
        let mut disk = self.disk.clone();
        let mut overlays = self.overlays.clone();
        for change in changes {
            if cancelled.load(Ordering::Relaxed) {
                return Err(IncrementalError::Cancelled);
            }
            apply_change(&mut disk, &mut overlays, change)?;
        }
        let sources = effective_sources(&disk, &overlays);
        let mut snapshot = compute_full_snapshot_cancellable(sources, self.limits, || {
            cancelled.load(Ordering::Relaxed)
        })?;
        if cancelled.load(Ordering::Relaxed) {
            return Err(IncrementalError::Cancelled);
        }
        enrich(&mut snapshot)?;
        if cancelled.load(Ordering::Relaxed) {
            return Err(IncrementalError::Cancelled);
        }
        let fingerprint = semantic_fingerprint(&snapshot);
        Ok(PreparedSnapshot {
            base_epoch,
            disk,
            overlays,
            snapshot,
            fingerprint,
        })
    }

    /// Atomically publishes a prepared snapshot when its base epoch is current.
    ///
    /// # Errors
    /// Returns [`IncrementalError::Stale`] when another commit won the race.
    pub fn commit(&mut self, prepared: PreparedSnapshot) -> Result<u64, IncrementalError> {
        if prepared.base_epoch != self.epoch {
            return Err(IncrementalError::Stale {
                expected: self.epoch,
                actual: prepared.base_epoch,
            });
        }
        let next_epoch = self
            .epoch
            .checked_add(1)
            .ok_or(IncrementalError::EpochExhausted)?;
        self.disk = prepared.disk;
        self.overlays = prepared.overlays;
        self.snapshot = prepared.snapshot;
        self.fingerprint = prepared.fingerprint;
        self.epoch = next_epoch;
        Ok(next_epoch)
    }
}

fn map_sources(
    sources: Vec<SnapshotSource>,
) -> Result<BTreeMap<String, SnapshotSource>, IncrementalError> {
    let mut map = BTreeMap::new();
    for source in sources {
        if map.insert(source.path.clone(), source).is_some() {
            return Err(IncrementalError::DuplicatePath(
                map.keys().next_back().cloned().unwrap_or_default(),
            ));
        }
    }
    Ok(map)
}

fn effective_sources(
    disk: &BTreeMap<String, SnapshotSource>,
    overlays: &BTreeMap<String, String>,
) -> Vec<SnapshotSource> {
    let resources = disk
        .values()
        .map(|source| {
            let mut effective = source.clone();
            if let Some(text) = overlays.get(&source.path) {
                effective.text.clone_from(text);
            }
            crate::Resource {
                scope: source.scope.clone(),
                file_path: source.path.clone(),
                logical_path: source.logical_path.clone(),
                value: effective,
                overwrite: crate::Overwrite::No,
                validate: true,
            }
        })
        .collect();
    crate::ResourceSnapshot::build(resources)
        .resources()
        .iter()
        .map(|resource| {
            let mut source = resource.value.clone();
            source.overwrite = resource.overwrite;
            source
        })
        .collect()
}

fn apply_change(
    disk: &mut BTreeMap<String, SnapshotSource>,
    overlays: &mut BTreeMap<String, String>,
    change: &Change,
) -> Result<(), IncrementalError> {
    match change {
        Change::Add(source) => {
            if disk.contains_key(&source.path) {
                return Err(IncrementalError::DuplicatePath(source.path.clone()));
            }
            disk.insert(source.path.clone(), source.clone());
        }
        Change::Edit { path, text } => disk
            .get_mut(path)
            .ok_or_else(|| IncrementalError::MissingPath(path.clone()))?
            .text
            .clone_from(text),
        Change::Remove { path } => {
            if disk.remove(path).is_none() {
                return Err(IncrementalError::MissingPath(path.clone()));
            }
            overlays.remove(path);
        }
        Change::Rename {
            from,
            to,
            logical_path,
        } => {
            if disk.contains_key(to) {
                return Err(IncrementalError::DuplicatePath(to.clone()));
            }
            let mut source = disk
                .remove(from)
                .ok_or_else(|| IncrementalError::MissingPath(from.clone()))?;
            source.path.clone_from(to);
            source.logical_path.clone_from(logical_path);
            disk.insert(to.clone(), source);
            if let Some(text) = overlays.remove(from) {
                overlays.insert(to.clone(), text);
            }
        }
        Change::OpenOverlay { path, text } => {
            if !disk.contains_key(path) {
                return Err(IncrementalError::MissingPath(path.clone()));
            }
            if overlays.contains_key(path) {
                return Err(IncrementalError::OverlayAlreadyOpen(path.clone()));
            }
            overlays.insert(path.clone(), text.clone());
        }
        Change::SaveOverlay { path } => {
            let text = overlays
                .get(path)
                .ok_or_else(|| IncrementalError::OverlayNotOpen(path.clone()))?
                .clone();
            disk.get_mut(path)
                .ok_or_else(|| IncrementalError::MissingPath(path.clone()))?
                .text = text;
        }
        Change::CloseOverlay { path } => {
            if overlays.remove(path).is_none() {
                return Err(IncrementalError::OverlayNotOpen(path.clone()));
            }
        }
    }
    Ok(())
}

/// Computes a stable identity for semantic content, ignoring source formatting and ranges.
#[must_use]
pub fn semantic_fingerprint(snapshot: &FullSnapshot) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64;
    for source in &snapshot.sources {
        hash_part(&mut hash, &source.scope);
        hash_part(&mut hash, &source.path);
        hash_part(&mut hash, &source.logical_path);
        hash_part(&mut hash, overwrite_tag(source.overwrite));
    }
    hash_occurrence_index(&mut hash, "definition", &snapshot.definitions);
    hash_occurrence_index(&mut hash, "reference", &snapshot.references);
    hash_occurrence_index(&mut hash, "variable", &snapshot.variables);
    for error in &snapshot.parse_errors {
        hash_part(&mut hash, "parse-error");
        hash_part(&mut hash, &error.path);
        hash_part(&mut hash, &error.code);
    }
    for diagnostic in &snapshot.diagnostics {
        hash_part(&mut hash, "diagnostic");
        hash_part(&mut hash, &diagnostic.path);
        hash_part(&mut hash, &diagnostic.code);
        hash_part(&mut hash, &diagnostic.message_key);
        hash_part(&mut hash, &diagnostic.key);
        for argument in &diagnostic.args {
            hash_part(&mut hash, argument);
        }
    }
    hash
}

const fn overwrite_tag(overwrite: crate::Overwrite) -> &'static str {
    match overwrite {
        crate::Overwrite::No => "no",
        crate::Overwrite::Overwrote => "overwrote",
        crate::Overwrite::Overwritten => "overwritten",
    }
}

fn hash_occurrence_index(
    hash: &mut u64,
    kind: &str,
    index: &BTreeMap<String, Vec<crate::SymbolOccurrence>>,
) {
    for (name, occurrences) in index {
        for occurrence in occurrences {
            hash_part(hash, kind);
            hash_part(hash, name);
            hash_part(hash, &occurrence.path);
            hash_part(hash, &occurrence.logical_path);
            if let Some(prefix) = &occurrence.key_prefix {
                hash_part(hash, prefix);
            }
        }
    }
}

fn hash_part(hash: &mut u64, value: &str) {
    for byte in value.as_bytes() {
        *hash ^= u64::from(*byte);
        *hash = hash.wrapping_mul(0x0100_0000_01b3);
    }
    *hash ^= 0xff;
    *hash = hash.wrapping_mul(0x0100_0000_01b3);
}

#[cfg(test)]
mod tests {
    use super::*;
    fn source(path: &str, text: &str) -> SnapshotSource {
        SnapshotSource {
            scope: "mod".into(),
            path: path.into(),
            logical_path: path.into(),
            text: text.into(),
            overwrite: Overwrite::No,
        }
    }
    fn clean(store: &IncrementalStore) -> FullSnapshot {
        compute_full_snapshot(
            effective_sources(&store.disk, &store.overlays),
            store.limits,
        )
        .unwrap()
    }
    fn apply(store: &mut IncrementalStore, changes: &[Change]) {
        let prepared = store
            .prepare(store.epoch(), changes, &AtomicBool::new(false))
            .unwrap();
        store.commit(prepared).unwrap();
        assert_eq!(store.snapshot(), &clean(store));
    }
    #[test]
    fn every_change_matches_clean_rebuild() {
        let mut store =
            IncrementalStore::new(vec![source("a.txt", "a = 1")], SnapshotLimits::default())
                .unwrap();
        apply(&mut store, &[Change::Add(source("b.txt", "b = 2"))]);
        apply(
            &mut store,
            &[Change::Edit {
                path: "a.txt".into(),
                text: "aa = 3".into(),
            }],
        );
        apply(
            &mut store,
            &[Change::Rename {
                from: "b.txt".into(),
                to: "c.txt".into(),
                logical_path: "common/c.txt".into(),
            }],
        );
        apply(
            &mut store,
            &[Change::OpenOverlay {
                path: "a.txt".into(),
                text: "overlay = 4".into(),
            }],
        );
        apply(
            &mut store,
            &[Change::SaveOverlay {
                path: "a.txt".into(),
            }],
        );
        apply(
            &mut store,
            &[Change::CloseOverlay {
                path: "a.txt".into(),
            }],
        );
        apply(
            &mut store,
            &[Change::Remove {
                path: "c.txt".into(),
            }],
        );
    }
    #[test]
    fn close_unsaved_overlay_restores_disk() {
        let mut store =
            IncrementalStore::new(vec![source("a.txt", "disk = 1")], SnapshotLimits::default())
                .unwrap();
        apply(
            &mut store,
            &[Change::OpenOverlay {
                path: "a.txt".into(),
                text: "overlay = 2".into(),
            }],
        );
        assert!(store.snapshot().definitions.contains_key("overlay"));
        apply(
            &mut store,
            &[Change::CloseOverlay {
                path: "a.txt".into(),
            }],
        );
        assert!(store.snapshot().definitions.contains_key("disk"));
    }
    #[test]
    fn cancellation_and_stale_commit_never_publish() {
        let mut store =
            IncrementalStore::new(vec![source("a.txt", "a = 1")], SnapshotLimits::default())
                .unwrap();
        let before = store.clone();
        let cancelled = AtomicBool::new(true);
        assert_eq!(
            store.prepare(
                0,
                &[Change::Edit {
                    path: "a.txt".into(),
                    text: "b = 2".into()
                }],
                &cancelled
            ),
            Err(IncrementalError::Cancelled)
        );
        assert_eq!(store, before);
        let prepared = store
            .prepare(
                0,
                &[Change::Edit {
                    path: "a.txt".into(),
                    text: "b = 2".into(),
                }],
                &AtomicBool::new(false),
            )
            .unwrap();
        apply(
            &mut store,
            &[Change::Edit {
                path: "a.txt".into(),
                text: "c = 3".into(),
            }],
        );
        assert!(matches!(
            store.commit(prepared),
            Err(IncrementalError::Stale { .. })
        ));
        assert!(store.snapshot().definitions.contains_key("c"));
    }

    #[test]
    fn cancellation_during_indexing_never_produces_a_candidate() {
        let sources = vec![source(
            "large.txt",
            &format!("root = {{ {} }}", "item = value ".repeat(64)),
        )];
        let mut polls = 0usize;
        assert_eq!(
            compute_full_snapshot_cancellable(sources, SnapshotLimits::default(), || {
                polls += 1;
                polls > 8
            }),
            Err(SnapshotError::Cancelled)
        );
    }

    #[test]
    fn failed_batch_and_duplicate_overlay_do_not_publish() {
        let store =
            IncrementalStore::new(vec![source("a.txt", "a = 1")], SnapshotLimits::default())
                .unwrap();
        let before = store.clone();
        assert!(matches!(
            store.prepare(
                store.epoch(),
                &[
                    Change::Edit {
                        path: "a.txt".into(),
                        text: "changed = 2".into(),
                    },
                    Change::Remove {
                        path: "missing.txt".into(),
                    },
                ],
                &AtomicBool::new(false),
            ),
            Err(IncrementalError::MissingPath(_))
        ));
        assert_eq!(store, before);

        let mut opened = store;
        apply(
            &mut opened,
            &[Change::OpenOverlay {
                path: "a.txt".into(),
                text: "overlay = 3".into(),
            }],
        );
        let opened_before = opened.clone();
        assert!(matches!(
            opened.prepare(
                opened.epoch(),
                &[Change::OpenOverlay {
                    path: "a.txt".into(),
                    text: "replacement = 4".into(),
                }],
                &AtomicBool::new(false),
            ),
            Err(IncrementalError::OverlayAlreadyOpen(_))
        ));
        assert_eq!(opened, opened_before);

        assert_eq!(
            opened.prepare_with(opened.epoch(), &[], &AtomicBool::new(false), |_| Err(
                IncrementalError::Cancelled
            ),),
            Err(IncrementalError::Cancelled)
        );
        assert_eq!(opened, opened_before);
    }

    #[test]
    fn semantic_fingerprint_ignores_formatting_but_tracks_meaning() {
        let compact = compute_full_snapshot(
            vec![source("a.txt", "a={ b=value }")],
            SnapshotLimits::default(),
        )
        .unwrap();
        let formatted = compute_full_snapshot(
            vec![source("a.txt", "a = {\n    b = value\n}")],
            SnapshotLimits::default(),
        )
        .unwrap();
        let changed = compute_full_snapshot(
            vec![source("a.txt", "different = { b = value }")],
            SnapshotLimits::default(),
        )
        .unwrap();
        assert_eq!(
            semantic_fingerprint(&compact),
            semantic_fingerprint(&formatted)
        );
        assert_ne!(
            semantic_fingerprint(&compact),
            semantic_fingerprint(&changed)
        );
    }
}
