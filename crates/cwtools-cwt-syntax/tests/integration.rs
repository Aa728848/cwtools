use std::fs;
use std::path::{Path, PathBuf};

use cwtools_cwt_syntax::{CWT001, MAX_INPUT_BYTES, parse_cwt};

const BROKEN_FIXTURES: &[(&str, &[(&str, usize)])] = &[];

fn collect_cwt_files(root: &Path, files: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(root) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_cwt_files(&path, files);
        } else if path
            .extension()
            .is_some_and(|extension| extension.eq_ignore_ascii_case("cwt"))
        {
            files.push(path);
        }
    }
}

#[test]
fn all_cwt_fixtures_parse() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures");
    let mut files = Vec::new();
    collect_cwt_files(&root, &mut files);
    files.sort();
    files.truncate(5000);
    let mut failures = Vec::new();
    for path in files {
        let relative = path
            .strip_prefix(&root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        let source =
            fs::read_to_string(&path).unwrap_or_else(|error| panic!("{relative}: {error}"));
        match BROKEN_FIXTURES
            .iter()
            .find(|(fixture, _)| *fixture == relative)
        {
            Some((_, expected)) => {
                let errors = parse_cwt(&source).expect_err(&relative);
                assert_eq!(errors.len(), expected.len(), "{relative}");
                for (error, (message, offset)) in errors.iter().zip(*expected) {
                    assert_eq!(error.code, CWT001, "{relative}");
                    assert_eq!(error.message, *message, "{relative}");
                    assert_eq!(error.offset, *offset, "{relative}");
                }
            }
            None => {
                if let Err(errors) = parse_cwt(&source) {
                    failures.push(format!("{relative}: {errors:?}"));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "unexpected fixture failures:\n{}",
        failures.join("\n")
    );
}

#[test]
fn malformed_inputs_have_stable_single_diagnostics() {
    let cases = [
        "a = {",
        "a =",
        "}",
        "a = { b =",
        "a = { b = {",
        "a = \"",
        "😀 = {",
        "a ?=",
        "a = { c =",
        "a = { d = { e =",
    ];
    for source in cases {
        let first = parse_cwt(source).expect_err(source);
        let second = parse_cwt(source).expect_err(source);
        assert!(!first.is_empty(), "{source}");
        assert_eq!(first, second, "{source}");
        for error in first {
            assert_eq!(error.code, CWT001, "{source}");
            assert!(error.offset <= source.len(), "{source}");
            assert!(error.line >= 1 && error.utf16_column >= 1, "{source}");
        }
    }
}

#[test]
fn byte_diagnostics_use_utf16_positions_and_limit_offset() {
    let mut invalid = "😀\nabc".as_bytes().to_vec();
    invalid.push(0xFF);
    let error = cwtools_cwt_syntax::parse_cwt_bytes(&invalid)
        .unwrap_err()
        .remove(0);
    assert_eq!(
        (error.code, error.offset, error.line, error.utf16_column),
        (CWT001, 8, 2, 4)
    );
    let bytes = vec![b'a'; MAX_INPUT_BYTES + 1];
    let error = cwtools_cwt_syntax::parse_cwt_bytes(&bytes)
        .unwrap_err()
        .remove(0);
    assert_eq!(
        (error.offset, error.line, error.utf16_column),
        (MAX_INPUT_BYTES, 1, MAX_INPUT_BYTES + 1)
    );
}
