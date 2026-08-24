#![forbid(unsafe_code)]
#![allow(
    clippy::module_name_repetitions,
    clippy::must_use_candidate,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::single_match_else,
    clippy::semicolon_if_nothing_returned
)]

use cwtools_cwt_service::{DiagnosticSeverity, DocumentModel, SymbolKind, analyze_document};
use cwtools_rule_ir::{Document as RuleDocument, parse_document};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

pub const DEFAULT_MAX_FILES: usize = 2000;
pub const DEFAULT_MAX_SIZE: u64 = 5 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: String,
    pub message: String,
    pub message_key: String,
    pub phase: String,
    pub file: String,
    pub error: bool,
    pub blocking: bool,
}
#[derive(Clone, Debug, PartialEq)]
pub struct ProjectDocument {
    pub path: String,
    pub source: String,
    pub model: DocumentModel,
    pub parsed: Option<RuleDocument>,
    pub content_hash: u64,
    pub partial: bool,
    pub skipped: bool,
    pub parse_failed: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolIndex {
    pub by_kind_name: BTreeMap<(SymbolKind, String), Vec<String>>,
    pub references: BTreeSet<(SymbolKind, String)>,
}
#[derive(Clone, Debug, PartialEq)]
pub struct ProjectSnapshot {
    pub version: u64,
    pub root: String,
    pub documents: Vec<ProjectDocument>,
    pub symbols: SymbolIndex,
    pub diagnostics: Vec<Diagnostic>,
    pub semantic_diagnostics: Vec<Diagnostic>,
    pub partial: bool,
    pub skipped: Vec<String>,
    pub parse_failed: Vec<String>,
    pub content_hash: u64,
}

pub fn normalize_path(path: &str) -> String {
    let p = path.replace('\\', "/");
    if cfg!(windows) { p.to_lowercase() } else { p }
}
pub fn safe_inject_resolution(root: &Path, base: &Path, inject: &str) -> Option<PathBuf> {
    let candidate = Path::new(inject);
    if candidate.is_absolute() || inject.split(['/', '\\']).any(|x| x == "..") {
        return None;
    }
    let base = if base.is_absolute() {
        base.to_path_buf()
    } else {
        root.join(base)
    };
    let joined = base.join(candidate);
    let clean = normalize_path(&joined.to_string_lossy());
    let rn = normalize_path(&root.to_string_lossy());
    (clean == rn || clean.starts_with(&(rn + "/"))).then_some(joined)
}
pub fn fnv1a(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |h, b| {
        (h ^ u64::from(*b)).wrapping_mul(0x0100_0000_01b3)
    })
}
pub fn ordered_content_hash(docs: &[ProjectDocument]) -> u64 {
    docs.iter().fold(0xcbf2_9ce4_8422_2325, |h, d| {
        let mut x = h;
        for b in normalize_path(&d.path).bytes().chain(d.source.bytes()) {
            x = (x ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
        }
        x
    })
}
fn message_key(code: &str) -> &'static str {
    match code {
        "CWT001" => "cwt.syntaxError",
        "CWT301" => "cwt.undefinedReference",
        "CWT302" => "cwt.duplicateType",
        "CWT401" => "cwt.injectCycle",
        _ => "cwt.unknown",
    }
}
fn diag(file: &str, code: &str, message: String, error: bool, blocking: bool) -> Diagnostic {
    Diagnostic {
        code: code.into(),
        message,
        message_key: message_key(code).into(),
        phase: "project".into(),
        file: file.into(),
        error,
        blocking,
    }
}
fn service_diag(file: &str, d: &cwtools_cwt_service::Diagnostic) -> Diagnostic {
    let error = d.severity == DiagnosticSeverity::Error;
    Diagnostic {
        code: d.code.clone(),
        message: format!("{} {:?}", d.message_key, d.args),
        message_key: d.message_key.clone(),
        phase: d.phase.clone(),
        file: file.into(),
        error,
        blocking: error || d.code == "CWT101",
    }
}

/// Build a project snapshot directly from in-memory path/text pairs.
#[must_use]
pub fn build_snapshot_from_texts(entries: &[(String, String)], root: &Path) -> ProjectSnapshot {
    let mut docs = entries
        .iter()
        .map(|(path, source)| {
            let key = normalize_path(path);
            let result = analyze_document(source);
            let failed = result.diagnostics.iter().any(|d| d.code == "CWT001");
            ProjectDocument {
                path: key.clone(),
                source: source.clone(),
                model: result.model,
                parsed: if failed {
                    None
                } else {
                    parse_document(&key, source).ok()
                },
                content_hash: fnv1a(source.as_bytes()),
                partial: false,
                skipped: false,
                parse_failed: failed,
            }
        })
        .collect::<Vec<_>>();
    docs.sort_by(|a, b| a.path.cmp(&b.path));
    let mut by_kind_name = BTreeMap::new();
    let mut references = BTreeSet::new();
    let mut diagnostics = Vec::new();
    let mut parse_failed = Vec::new();
    for d in &docs {
        let result = analyze_document(&d.source);
        diagnostics.extend(result.diagnostics.iter().map(|x| service_diag(&d.path, x)));
        if d.parse_failed {
            parse_failed.push(d.path.clone());
        }
        for s in &d.model.symbols {
            by_kind_name
                .entry((s.kind, s.name.clone()))
                .or_insert_with(Vec::new)
                .push(d.path.clone());
        }
        for r in &d.model.references {
            references.insert((r.kind, r.name.clone()));
        }
    }
    for files in by_kind_name.values_mut() {
        files.sort();
        files.dedup();
    }
    let symbols = SymbolIndex {
        by_kind_name,
        references,
    };
    let semantic_diagnostics = assemble_semantic(&docs, &symbols, root);
    let content_hash = ordered_content_hash(&docs);
    ProjectSnapshot {
        version: content_hash,
        root: normalize_path(&root.to_string_lossy()),
        documents: docs,
        symbols,
        diagnostics,
        semantic_diagnostics,
        partial: false,
        skipped: Vec::new(),
        parse_failed,
        content_hash,
    }
}

fn assemble_semantic(
    docs: &[ProjectDocument],
    symbols: &SymbolIndex,
    root: &Path,
) -> Vec<Diagnostic> {
    let mut semantic = Vec::new();
    let defined_kinds: BTreeSet<SymbolKind> =
        symbols.by_kind_name.keys().map(|(kind, _)| *kind).collect();
    for document in docs {
        let mut type_counts = BTreeMap::<String, usize>::new();
        for symbol in &document.model.symbols {
            if symbol.kind == SymbolKind::Type {
                *type_counts.entry(symbol.name.clone()).or_default() += 1;
            }
        }
        for (name, count) in type_counts {
            if count > 1 {
                for _ in 0..count {
                    semantic.push(diag(
                        &document.path,
                        "CWT302",
                        format!("duplicate Type {name}"),
                        true,
                        true,
                    ));
                }
            }
        }
        for reference in &document.model.references {
            let builtin = (reference.kind == SymbolKind::Type
                && matches!(reference.name.as_str(), "target" | "modifier"))
                || (reference.kind == SymbolKind::ModifierCategory && reference.name == "modifier");
            let enum_defined = reference.kind == SymbolKind::Enum
                && (symbols
                    .by_kind_name
                    .contains_key(&(SymbolKind::Enum, reference.name.clone()))
                    || symbols
                        .by_kind_name
                        .contains_key(&(SymbolKind::Complex, reference.name.clone())));
            let project_kind = defined_kinds.contains(&reference.kind)
                || (reference.kind == SymbolKind::Enum
                    && symbols
                        .by_kind_name
                        .keys()
                        .any(|(kind, _)| *kind == SymbolKind::Complex));
            if !builtin
                && project_kind
                && !enum_defined
                && !symbols
                    .by_kind_name
                    .contains_key(&(reference.kind, reference.name.clone()))
            {
                semantic.push(diag(
                    &document.path,
                    "CWT301",
                    format!("undefined {:?} {}", reference.kind, reference.name),
                    true,
                    true,
                ));
            }
        }
    }
    let mut edges = BTreeMap::<String, Vec<String>>::new();
    let document_keys = docs
        .iter()
        .map(|d| normalize_path(&d.path))
        .collect::<BTreeSet<_>>();
    for document in docs {
        for inject in &document.model.injects {
            let base = Path::new(&document.path).parent().unwrap_or(Path::new("."));
            if let Some(path) = safe_inject_resolution(root, base, inject) {
                let absolute = normalize_path(&path.to_string_lossy());
                let relative = normalize_path(&root.join(&path).to_string_lossy());
                let target = if document_keys.contains(&absolute) {
                    absolute
                } else if document_keys.contains(&relative) {
                    relative
                } else if document_keys.contains(&normalize_path(inject)) {
                    normalize_path(inject)
                } else {
                    continue;
                };
                edges
                    .entry(normalize_path(&document.path))
                    .or_default()
                    .push(target);
            }
        }
    }
    fn visit(
        n: &str,
        edges: &BTreeMap<String, Vec<String>>,
        state: &mut BTreeMap<String, u8>,
        depth: usize,
    ) -> bool {
        if depth > 2048 {
            return true;
        }
        match state.get(n).copied().unwrap_or(0) {
            1 => true,
            2 => false,
            _ => {
                state.insert(n.into(), 1);
                let hit = edges
                    .get(n)
                    .is_some_and(|next| next.iter().any(|x| visit(x, edges, state, depth + 1)));
                state.insert(n.into(), 2);
                hit
            }
        }
    }
    let mut state = BTreeMap::new();
    for node in edges.keys() {
        if visit(node, &edges, &mut state, 0) {
            semantic.push(diag(node, "CWT401", "inject cycle".into(), true, true));
        }
    }
    semantic
}

pub fn build_snapshot(
    files: &[PathBuf],
    max_files: Option<usize>,
    max_size: Option<u64>,
    root: &Path,
) -> ProjectSnapshot {
    let limit = max_files.unwrap_or(DEFAULT_MAX_FILES);
    let size_limit = max_size.unwrap_or(DEFAULT_MAX_SIZE);
    let mut paths = files.to_vec();
    paths.sort_by_key(|p| normalize_path(&p.to_string_lossy()));
    let mut docs = Vec::new();
    let mut skipped = Vec::new();
    let mut parse_failed = Vec::new();
    let mut partial = false;
    for (i, path) in paths.iter().enumerate() {
        let key = normalize_path(&path.to_string_lossy());
        let size = fs::metadata(path).map_or(0, |m| m.len());
        if i >= limit {
            skipped.push(key);
            partial = true;
            continue;
        }
        if size > size_limit {
            skipped.push(key);
            partial = true;
            continue;
        }
        match fs::read_to_string(path) {
            Ok(source) => {
                let hash = fnv1a(source.as_bytes());
                let result = analyze_document(&source);
                let failed = result.diagnostics.iter().any(|d| d.code == "CWT001");
                let parsed = if failed {
                    None
                } else {
                    parse_document(&key, &source).ok()
                };
                if failed {
                    parse_failed.push(key.clone());
                }
                docs.push(ProjectDocument {
                    path: key,
                    source,
                    model: result.model,
                    parsed,
                    content_hash: hash,
                    partial: false,
                    skipped: false,
                    parse_failed: failed,
                });
            }
            Err(_) => {
                skipped.push(key);
                partial = true
            }
        }
    }
    let mut symbols = SymbolIndex {
        by_kind_name: BTreeMap::new(),
        references: BTreeSet::new(),
    };
    let mut diagnostics = Vec::new();
    for d in &docs {
        let result = analyze_document(&d.source);
        for x in &result.diagnostics {
            diagnostics.push(service_diag(&d.path, x));
        }
        for s in &d.model.symbols {
            symbols
                .by_kind_name
                .entry((s.kind, s.name.clone()))
                .or_default()
                .push(d.path.clone());
        }
        for r in &d.model.references {
            symbols.references.insert((r.kind, r.name.clone()));
        }
    }
    for p in &parse_failed {
        diagnostics.push(diag(p, "CWT001", "parse failed".into(), true, true));
    }
    let semantic = assemble_semantic(&docs, &symbols, root);
    docs.sort_by(|a, b| a.path.cmp(&b.path));
    for v in symbols.by_kind_name.values_mut() {
        v.sort();
        v.dedup();
    }
    let hash = ordered_content_hash(&docs);
    ProjectSnapshot {
        version: hash,
        root: normalize_path(&root.to_string_lossy()),
        documents: docs,
        symbols,
        diagnostics,
        semantic_diagnostics: semantic,
        partial,
        skipped,
        parse_failed,
        content_hash: hash,
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActiveRules {
    pub generation: u64,
    pub hash: u64,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    Activate,
    Rejected,
    NoChange,
}
pub fn candidate_decision(active: &ActiveRules, s: &ProjectSnapshot) -> Decision {
    if s.partial
        || s.diagnostics
            .iter()
            .chain(s.semantic_diagnostics.iter())
            .any(|d| d.error || d.blocking)
    {
        Decision::Rejected
    } else if active.hash == s.content_hash {
        Decision::NoChange
    } else {
        Decision::Activate
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActivationState {
    pub active: ActiveRules,
    pub success_epoch: u64,
}
impl Default for ActivationState {
    fn default() -> Self {
        Self::new()
    }
}
impl ActivationState {
    pub fn new() -> Self {
        Self {
            active: ActiveRules {
                generation: 0,
                hash: 0,
            },
            success_epoch: 0,
        }
    }
    pub fn commit(&mut self, s: &ProjectSnapshot) -> Decision {
        let d = candidate_decision(&self.active, s);
        if d == Decision::Activate {
            self.active = ActiveRules {
                generation: self.active.generation + 1,
                hash: s.content_hash,
            };
            self.success_epoch += 1;
        }
        d
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        path::Path,
        sync::atomic::{AtomicU64, Ordering},
    };

    static NEXT: AtomicU64 = AtomicU64::new(0);

    fn temp_root() -> PathBuf {
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let p = std::env::temp_dir().join(format!("cwtools-cwt-project-{n}"));
        fs::create_dir_all(&p).unwrap();
        p
    }

    fn files(root: &Path, entries: &[(&str, &str)]) -> Vec<PathBuf> {
        entries
            .iter()
            .map(|(name, source)| {
                let p = root.join(name);
                if let Some(parent) = p.parent() {
                    fs::create_dir_all(parent).unwrap();
                }
                fs::write(&p, source).unwrap();
                p
            })
            .collect()
    }

    fn snapshot(entries: &[(&str, &str)]) -> ProjectSnapshot {
        let root = temp_root();
        let paths = files(&root, entries);
        let s = build_snapshot(&paths, None, None, &root);
        fs::remove_dir_all(root).unwrap();
        s
    }

    fn empty_snapshot(hash: u64) -> ProjectSnapshot {
        ProjectSnapshot {
            version: hash,
            root: String::new(),
            documents: vec![],
            symbols: SymbolIndex {
                by_kind_name: BTreeMap::new(),
                references: BTreeSet::new(),
            },
            diagnostics: vec![],
            semantic_diagnostics: vec![],
            partial: false,
            skipped: vec![],
            parse_failed: vec![],
            content_hash: hash,
        }
    }

    #[test]
    fn normalize_forward_slashes() {
        let got = normalize_path(r"A\B/C");
        if cfg!(windows) {
            assert_eq!(got, "a/b/c");
        } else {
            assert_eq!(got, "A/B/C");
        }
    }
    #[test]
    fn normalize_case_policy_is_platform_specific() {
        let got = normalize_path(r"A\B");
        if cfg!(windows) {
            assert_eq!(got, "a/b");
        } else {
            assert_eq!(got, "A/B");
        }
    }
    #[test]
    fn safe_inject_accepts_in_root_relative() {
        let r = Path::new("/r");
        assert_eq!(
            safe_inject_resolution(r, r, "sub/x.cwt"),
            Some(r.join("sub/x.cwt"))
        );
    }
    #[test]
    fn safe_inject_rejects_absolute() {
        assert!(safe_inject_resolution(Path::new("/r"), Path::new("/r"), "/x").is_none());
    }
    #[test]
    fn safe_inject_rejects_traversal() {
        assert!(safe_inject_resolution(Path::new("/r"), Path::new("/r"), "a/../x").is_none());
    }
    #[test]
    fn safe_inject_rejects_out_of_root_base() {
        assert!(safe_inject_resolution(Path::new("/r"), Path::new("/other"), "x").is_none());
    }
    #[test]
    fn fnv_is_deterministic() {
        assert_eq!(fnv1a(b"abc"), fnv1a(b"abc"));
        assert_ne!(fnv1a(b"abc"), fnv1a(b"abd"));
    }
    #[test]
    fn fnv_is_order_sensitive() {
        assert_ne!(fnv1a(b"ab"), fnv1a(b"ba"));
    }
    #[test]
    fn ordered_hash_is_deterministic() {
        let d = |p: &str| ProjectDocument {
            path: p.into(),
            source: "x".into(),
            model: DocumentModel::default(),
            parsed: None,
            content_hash: 0,
            partial: false,
            skipped: false,
            parse_failed: false,
        };
        assert_eq!(
            ordered_content_hash(&[d("a")]),
            ordered_content_hash(&[d("a")])
        );
    }
    #[test]
    fn ordered_hash_preserves_document_order() {
        let d = |p: &str| ProjectDocument {
            path: p.into(),
            source: "x".into(),
            model: DocumentModel::default(),
            parsed: None,
            content_hash: 0,
            partial: false,
            skipped: false,
            parse_failed: false,
        };
        assert_ne!(
            ordered_content_hash(&[d("a"), d("b")]),
            ordered_content_hash(&[d("b"), d("a")])
        );
    }
    #[test]
    fn max_files_marks_partial_and_skips() {
        let s = snapshot(&[("b.cwt", "x = y"), ("a.cwt", "x = y")]);
        let root = PathBuf::from(&s.root);
        let _ = root;
        assert_eq!(s.documents.len(), 2);
    }
    #[test]
    fn max_files_limit_is_enforced() {
        let root = temp_root();
        let ps = files(&root, &[("b.cwt", "x = y"), ("a.cwt", "x = z")]);
        let s = build_snapshot(&ps, Some(1), None, &root);
        fs::remove_dir_all(root).unwrap();
        assert!(s.partial);
        assert_eq!(s.documents.len(), 1);
        assert_eq!(s.skipped.len(), 1);
    }
    #[test]
    fn per_file_size_limit_is_enforced() {
        let root = temp_root();
        let ps = files(&root, &[("a.cwt", "123456")]);
        let s = build_snapshot(&ps, None, Some(3), &root);
        fs::remove_dir_all(root).unwrap();
        assert!(s.partial);
        assert!(s.documents.is_empty());
    }
    #[test]
    fn documents_are_deterministically_sorted() {
        let s = snapshot(&[("z.cwt", "x = z"), ("a.cwt", "x = a")]);
        assert!(s.documents[0].path < s.documents[1].path);
    }
    #[test]
    fn parse_failed_is_recorded_and_blocking() {
        let s = snapshot(&[("bad.cwt", "a = {")]);
        assert!(!s.parse_failed.is_empty());
        assert!(
            s.diagnostics
                .iter()
                .any(|d| d.code == "CWT001" && d.blocking)
        );
    }
    #[test]
    fn indexes_type_enum_subtype_symbols() {
        let s = snapshot(&[(
            "a.cwt",
            "type[thing] = { subtype[child] = {} }
enum[color] = { red }",
        )]);
        assert!(
            s.symbols
                .by_kind_name
                .contains_key(&(SymbolKind::Type, "thing".into()))
        );
        assert!(
            s.symbols
                .by_kind_name
                .contains_key(&(SymbolKind::Enum, "color".into()))
        );
        assert!(
            s.symbols
                .by_kind_name
                .contains_key(&(SymbolKind::Subtype, "child".into()))
        );
    }
    #[test]
    fn indexes_complex_enum_clause_as_enum() {
        let s = snapshot(&[("a.cwt", "complex_enum[red] = { name = { x = scalar } }")]);
        assert!(
            s.symbols
                .by_kind_name
                .contains_key(&(SymbolKind::Complex, "red".into()))
        );
    }
    #[test]
    fn cwt301_does_not_report_value_without_project_definitions() {
        let s = snapshot(&[("a.cwt", "rule = value[missing]")]);
        assert!(!s.semantic_diagnostics.iter().any(|d| d.code == "CWT301"));
    }
    #[test]
    fn cwt301_defined_reference_is_clean() {
        let s = snapshot(&[(
            "a.cwt",
            "value[known] = { one }
rule = value[known]",
        )]);
        assert!(!s.semantic_diagnostics.iter().any(|d| d.code == "CWT301"));
    }
    #[test]
    fn cwt301_builtin_scope_is_allowed() {
        let s = snapshot(&[("a.cwt", "rule = scope[root]")]);
        assert!(!s.semantic_diagnostics.iter().any(|d| d.code == "CWT301"));
    }
    #[test]
    fn cwt301_complex_enum_reference_is_defined() {
        let s = snapshot(&[(
            "a.cwt",
            "complex_enum[red] = { name = { x = scalar } }\nrule = enum[red]",
        )]);
        assert!(!s.semantic_diagnostics.iter().any(|d| d.code == "CWT301"));
    }
    #[test]
    fn cwt302_same_file_duplicate_reports_each_declaration() {
        let s = snapshot(&[(
            "a.cwt",
            "type[same] = {}
type[same] = {}",
        )]);
        assert_eq!(
            s.semantic_diagnostics
                .iter()
                .filter(|d| d.code == "CWT302")
                .count(),
            2
        );
    }
    #[test]
    fn cwt302_cross_file_duplicate_is_allowed() {
        let s = snapshot(&[("a.cwt", "type[same] = {}"), ("b.cwt", "type[same] = {}")]);
        assert!(!s.semantic_diagnostics.iter().any(|d| d.code == "CWT302"));
    }
    #[test]
    fn cwt401_self_cycle_reports() {
        let s = snapshot(&[("a.cwt", "inject = a.cwt")]);
        assert!(s.semantic_diagnostics.iter().any(|d| d.code == "CWT401"));
    }
    #[test]
    fn cwt401_two_node_cycle_reports() {
        let s = snapshot(&[("a.cwt", "inject = b.cwt"), ("b.cwt", "inject = a.cwt")]);
        assert!(s.semantic_diagnostics.iter().any(|d| d.code == "CWT401"));
    }
    #[test]
    fn cwt401_acyclic_injects_are_clean() {
        let s = snapshot(&[("a.cwt", "inject = b.cwt"), ("b.cwt", "x = y")]);
        assert!(!s.semantic_diagnostics.iter().any(|d| d.code == "CWT401"));
    }
    #[test]
    fn cwt401_traversal_inject_is_ignored() {
        let s = snapshot(&[("a.cwt", "inject = ../b.cwt")]);
        assert!(!s.semantic_diagnostics.iter().any(|d| d.code == "CWT401"));
    }
    #[test]
    fn all_errors_block() {
        let mut s = empty_snapshot(2);
        s.diagnostics.push(diag("x", "X", "x".into(), true, false));
        assert_eq!(
            candidate_decision(
                &ActiveRules {
                    generation: 1,
                    hash: 1
                },
                &s
            ),
            Decision::Rejected
        );
    }
    #[test]
    fn listed_warning_blocks() {
        let mut s = empty_snapshot(2);
        s.diagnostics
            .push(diag("x", "CWT101", "x".into(), false, true));
        assert_eq!(
            candidate_decision(
                &ActiveRules {
                    generation: 1,
                    hash: 1
                },
                &s
            ),
            Decision::Rejected
        );
    }
    #[test]
    fn partial_blocks() {
        let mut s = empty_snapshot(2);
        s.partial = true;
        assert_eq!(
            candidate_decision(
                &ActiveRules {
                    generation: 1,
                    hash: 1
                },
                &s
            ),
            Decision::Rejected
        );
    }
    #[test]
    fn no_change_for_same_hash() {
        let s = empty_snapshot(7);
        assert_eq!(
            candidate_decision(
                &ActiveRules {
                    generation: 2,
                    hash: 7
                },
                &s
            ),
            Decision::NoChange
        );
    }
    #[test]
    fn rejected_preserves_activation_state() {
        let mut a = ActivationState {
            active: ActiveRules {
                generation: 3,
                hash: 4,
            },
            success_epoch: 9,
        };
        let mut s = empty_snapshot(8);
        s.partial = true;
        assert_eq!(a.commit(&s), Decision::Rejected);
        assert_eq!(
            a,
            ActivationState {
                active: ActiveRules {
                    generation: 3,
                    hash: 4
                },
                success_epoch: 9
            }
        );
    }
    #[test]
    fn activate_increments_generation_and_epoch() {
        let mut a = ActivationState::new();
        let s = empty_snapshot(8);
        assert_eq!(a.commit(&s), Decision::Activate);
        assert_eq!(a.active.generation, 1);
        assert_eq!(a.success_epoch, 1);
    }
    #[test]
    fn repair_upgrades_after_rejection() {
        let mut a = ActivationState {
            active: ActiveRules {
                generation: 2,
                hash: 1,
            },
            success_epoch: 4,
        };
        let mut bad = empty_snapshot(2);
        bad.partial = true;
        assert_eq!(a.commit(&bad), Decision::Rejected);
        let good = empty_snapshot(2);
        assert_eq!(a.commit(&good), Decision::Activate);
        assert_eq!(a.active.generation, 3);
        assert_eq!(a.success_epoch, 5);
    }
}
