use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

#[cfg(test)]
use crate::Overwrite;
use crate::{FullSnapshot, SnapshotError, SnapshotLimits, SnapshotSource, compute_full_snapshot};

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
    OverlayNotOpen(String),
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
        Self::Snapshot(value)
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
        let snapshot = compute_full_snapshot(disk.values().cloned().collect(), limits)?;
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
        let snapshot = compute_full_snapshot(sources, self.limits)?;
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
        self.disk = prepared.disk;
        self.overlays = prepared.overlays;
        self.snapshot = prepared.snapshot;
        self.fingerprint = prepared.fingerprint;
        self.epoch = self.epoch.saturating_add(1);
        Ok(self.epoch)
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
    disk.values()
        .map(|source| {
            let mut effective = source.clone();
            if let Some(text) = overlays.get(&source.path) {
                effective.text.clone_from(text);
            }
            effective
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

#[must_use]
pub fn semantic_fingerprint(snapshot: &FullSnapshot) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64;
    for source in &snapshot.sources {
        for bytes in [
            source.scope.as_bytes(),
            source.path.as_bytes(),
            source.logical_path.as_bytes(),
            source.text.as_bytes(),
        ] {
            for byte in bytes {
                hash ^= u64::from(*byte);
                hash = hash.wrapping_mul(0x0100_0000_01b3);
            }
            hash ^= 0xff;
            hash = hash.wrapping_mul(0x0100_0000_01b3);
        }
    }
    hash
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
}
