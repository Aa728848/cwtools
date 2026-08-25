#![forbid(unsafe_code)]
//! Stable all-game facade for `CWTools` sessions, localisation, and caches.

pub use cwtools_cache::{
    BoundedMemoryCache, CACHE_MAGIC, CACHE_SCHEMA_VERSION, CacheError, CacheKey, CacheLimits,
    CacheMetadata, CacheMissReason, CacheRead, CacheStore, CompressionKind, Fingerprint,
    fingerprint_bytes, fingerprint_sources, fingerprint_text,
};
pub use cwtools_game_core::{
    GameId, GameModel, GameProfile, GameSession, GameSessionConfig, LocalisationDiagnostic,
    LocalisationEntry, LocalisationFile, LocalisationFormat, LocalisationIndex,
    LocalisationLanguage, LocalisationProfile, SessionError, SessionSnapshot, SourceInput,
    TextEncoding, all_game_profiles, game_profile, parse_localisation,
};
pub use cwtools_workspace::{Overwrite, SnapshotLimits};

use std::path::PathBuf;

#[derive(Clone, Debug)]
pub struct GameSessionBuilder {
    config: GameSessionConfig,
}

impl GameSessionBuilder {
    #[must_use]
    pub fn new(game_id: GameId) -> Self {
        Self {
            config: GameSessionConfig {
                game_id,
                ..GameSessionConfig::default()
            },
        }
    }
    #[must_use]
    pub fn rules_hash(mut self, rules_hash: Fingerprint) -> Self {
        self.config.rules_hash = rules_hash;
        self
    }
    #[must_use]
    pub fn snapshot_limits(mut self, limits: SnapshotLimits) -> Self {
        self.config.snapshot_limits = limits;
        self
    }
    #[must_use]
    pub fn max_diagnostics(mut self, limit: usize) -> Self {
        self.config.max_diagnostics = limit;
        self
    }
    #[must_use]
    pub fn cache(mut self, path: impl Into<PathBuf>, limits: CacheLimits) -> Self {
        self.config.cache_path = Some(path.into());
        self.config.cache_limits = limits;
        self
    }
    #[must_use]
    pub fn build(self) -> GameSession {
        GameSession::new(self.config)
    }
}

macro_rules! constructor {
    ($name:ident, $id:expr) => {
        #[must_use]
        pub fn $name() -> GameSession {
            GameSessionBuilder::new($id).build()
        }
    };
}
constructor!(generic, GameId::Generic);
constructor!(custom, GameId::Custom);
constructor!(jomini, GameId::Jomini);
constructor!(ck2, GameId::Ck2);
constructor!(ck3, GameId::Ck3);
constructor!(eu4, GameId::Eu4);
constructor!(eu5, GameId::Eu5);
constructor!(hoi4, GameId::Hoi4);
constructor!(imperator, GameId::Imperator);
constructor!(vic2, GameId::Vic2);
constructor!(vic3, GameId::Vic3);
constructor!(stellaris, GameId::Stellaris);
constructor!(cwt_only, GameId::CwtOnly);

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temporary_cache(name: &str) -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos();
        std::env::temp_dir().join(format!("cwtools-game-{name}-{nonce}.cache"))
    }

    #[test]
    fn constructors_cover_every_profile() {
        let sessions = vec![
            generic(),
            custom(),
            jomini(),
            ck2(),
            ck3(),
            eu4(),
            eu5(),
            hoi4(),
            imperator(),
            vic2(),
            vic3(),
            stellaris(),
            cwt_only(),
        ];
        let ids = sessions
            .into_iter()
            .map(|session| session.game_id())
            .collect::<Vec<_>>();
        assert_eq!(ids.len(), 13);
        for profile in all_game_profiles() {
            assert!(ids.contains(&profile.id), "missing {}", profile.id);
        }
    }

    #[test]
    fn bounded_builder_creates_refreshable_session() {
        let mut session = GameSessionBuilder::new(GameId::Stellaris)
            .rules_hash(fingerprint_text("rules-v1"))
            .snapshot_limits(SnapshotLimits {
                max_sources: 2,
                max_nodes: 100,
            })
            .max_diagnostics(8)
            .build();
        session
            .upsert_source(SourceInput {
                scope: "mod".to_owned(),
                path: "common/a.txt".to_owned(),
                logical_path: "common/a.txt".to_owned(),
                text: "value = yes".to_owned(),
                overwrite: Overwrite::No,
            })
            .expect("source");
        assert!(session.refresh_full().is_ok());
        assert!(
            session
                .refresh_incremental(&["common/a.txt".to_owned()])
                .is_ok()
        );
    }

    #[test]
    fn localisation_covers_yaml_bom_and_legacy_csv() {
        let yaml = parse_localisation(
            "a.yml",
            "\u{feff}l_english:\n key:0 \"Value\"",
            &game_profile(GameId::Stellaris).localisation,
        );
        let csv = parse_localisation(
            "a.csv",
            "KEY;English;French;German;Spanish;;;",
            &game_profile(GameId::Ck2).localisation,
        );
        assert!(yaml.has_bom);
        assert!(yaml.entries.iter().any(|entry| entry.key == "key"));
        assert!(csv.entries.iter().any(|entry| entry.key == "KEY"));
    }

    #[test]
    fn cache_round_trips_and_checks_identity() {
        let path = temporary_cache("roundtrip");
        let store = CacheStore::new(&path);
        let source = fingerprint_text("source");
        let key = CacheKey::new("stellaris", fingerprint_text("rules"), source).expect("key");
        let value = vec!["one".to_owned(), "two".to_owned()];
        store.write_json(&key, &value).expect("write");
        assert_eq!(store.read_json::<Vec<String>>(&key).value, Some(value));
        let wrong = CacheKey::new("ck3", fingerprint_text("rules"), source).expect("wrong");
        assert!(matches!(
            store.read_json::<Vec<String>>(&wrong).miss,
            Some(CacheMissReason::GameMismatch { .. })
        ));
        let _ = fs::remove_file(path);
    }

    #[test]
    fn corrupt_cache_falls_back_safely() {
        let path = temporary_cache("corrupt");
        fs::write(&path, b"not a cache").expect("fixture");
        assert!(!CacheStore::new(&path).inspect().is_hit());
        let _ = fs::remove_file(path);
    }
}
