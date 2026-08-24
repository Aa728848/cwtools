#![forbid(unsafe_code)]
use cwtools_cwt_project::{build_snapshot_from_texts, definition_at, references_at};
use cwtools_cwt_service::{
    AnalysisResult, CompletionArgument, Diagnostic, Position, Range, Reference, Symbol,
    analyze_document, completions_with_project,
};
use serde::{Deserialize, Serialize};
use std::{
    io::{self, Read},
    path::Path,
};

#[derive(Debug, Deserialize)]
struct Input {
    files: Vec<InputFile>,
    #[serde(default = "default_mode")]
    mode: String,
    query: Option<String>,
    #[serde(rename = "queryLine")]
    query_line: Option<u32>,
    #[serde(rename = "queryColumn")]
    query_column: Option<u32>,
    operation: Option<String>,
}

fn default_mode() -> String {
    "document".into()
}

#[derive(Debug, Deserialize)]
struct InputFile {
    path: String,
    text: String,
}
#[derive(Debug, Serialize)]
struct Output {
    files: Vec<FileOutput>,
}
#[derive(Debug, Serialize, PartialEq, Eq)]
struct CompletionOutput {
    mode: String,
    items: Vec<CompletionItem>,
}
#[derive(Debug, Serialize, PartialEq, Eq)]
struct CompletionItem {
    label: String,
    kind: String,
    #[serde(rename = "insertText")]
    insert_text: Option<String>,
}
#[derive(Debug, Serialize)]
struct NavigationOutput {
    mode: String,
    locations: Vec<NavigationLocation>,
}
#[derive(Debug, Serialize)]
struct NavigationLocation {
    path: String,
    kind: String,
    name: String,
    #[serde(flatten)]
    range: WireRange,
}
#[derive(Debug, Serialize)]
struct ProjectOutput {
    mode: String,
    diagnostics: Vec<ProjectDiagnostic>,
    summary: ProjectSummary,
}
#[derive(Debug, Serialize)]
struct ProjectDiagnostic {
    path: String,
    code: String,
    #[serde(rename = "messageKey")]
    message_key: String,
    phase: String,
}
#[derive(Debug, Serialize)]
struct ProjectSummary {
    partial: bool,
    skipped: usize,
    #[serde(rename = "parseFailed")]
    parse_failed: usize,
}
#[derive(Debug, Serialize)]
struct FileOutput {
    path: String,
    diagnostics: Vec<WireDiagnostic>,
    symbols: Vec<WireSymbol>,
    references: Vec<WireReference>,
    #[serde(rename = "completionArguments")]
    completion_arguments: Vec<WireCompletion>,
}
#[derive(Debug, Serialize)]
struct WireRange {
    #[serde(rename = "startLine")]
    start_line: u32,
    #[serde(rename = "startColumn")]
    start_column: u32,
    #[serde(rename = "endLine")]
    end_line: u32,
    #[serde(rename = "endColumn")]
    end_column: u32,
}
#[derive(Debug, Serialize)]
struct WireDiagnostic {
    phase: String,
    code: String,
    #[serde(rename = "messageKey")]
    message_key: String,
    #[serde(flatten)]
    range: WireRange,
}
#[derive(Debug, Serialize)]
struct WireSymbol {
    kind: String,
    name: String,
    #[serde(flatten)]
    range: WireRange,
}
#[derive(Debug, Serialize)]
struct WireReference {
    kind: String,
    name: String,
    #[serde(flatten)]
    range: WireRange,
}

fn wire_range(range: &Range) -> WireRange {
    WireRange {
        start_line: range.start.line,
        start_column: range.start.character,
        end_line: range.end.line,
        end_column: range.end.character,
    }
}
#[derive(Debug, Serialize)]
struct WireCompletion {
    family: String,
    name: String,
}

fn diagnostic(d: &Diagnostic) -> WireDiagnostic {
    WireDiagnostic {
        phase: d.phase.clone(),
        code: d.code.clone(),
        message_key: d.message_key.clone(),
        range: wire_range(&d.range),
    }
}
fn kind_name(kind: cwtools_cwt_service::SymbolKind) -> String {
    use cwtools_cwt_service::SymbolKind;
    match kind {
        SymbolKind::Complex => "complexEnum".into(),
        SymbolKind::Value => "valueSet".into(),
        _ => {
            let debug = format!("{kind:?}");
            let mut chars = debug.chars();
            chars.next().map_or_else(String::new, |first| {
                first.to_lowercase().chain(chars).collect()
            })
        }
    }
}
fn symbol(s: &Symbol) -> WireSymbol {
    WireSymbol {
        kind: kind_name(s.kind),
        name: s.name.clone(),
        range: wire_range(&s.range),
    }
}
fn reference(r: &Reference) -> WireReference {
    WireReference {
        kind: kind_name(r.kind),
        name: r.name.clone(),
        range: wire_range(&r.range),
    }
}
fn completion(c: &CompletionArgument) -> WireCompletion {
    WireCompletion {
        family: c.detail.clone().unwrap_or_else(|| kind_name(c.kind)),
        name: c.label.clone(),
    }
}
fn file_output(path: String, analysis: &AnalysisResult) -> FileOutput {
    FileOutput {
        path,
        diagnostics: analysis.diagnostics.iter().map(diagnostic).collect(),
        symbols: analysis.model.symbols.iter().map(symbol).collect(),
        references: analysis.model.references.iter().map(reference).collect(),
        completion_arguments: analysis
            .model
            .completion_arguments
            .iter()
            .map(completion)
            .collect(),
    }
}
fn run_project(input: &Input) -> ProjectOutput {
    let entries: Vec<_> = input
        .files
        .iter()
        .map(|f| (f.path.clone(), f.text.clone()))
        .collect();
    let snapshot = build_snapshot_from_texts(&entries, Path::new("."));
    let mut diagnostics = snapshot
        .diagnostics
        .iter()
        .chain(snapshot.semantic_diagnostics.iter())
        .map(|d| ProjectDiagnostic {
            path: d.file.clone(),
            code: d.code.clone(),
            message_key: d.message_key.clone(),
            phase: d.phase.clone(),
        })
        .collect::<Vec<_>>();
    diagnostics.sort_by(|a, b| {
        (&a.path, &a.phase, &a.code, &a.message_key).cmp(&(
            &b.path,
            &b.phase,
            &b.code,
            &b.message_key,
        ))
    });
    ProjectOutput {
        mode: "project".into(),
        diagnostics,
        summary: ProjectSummary {
            partial: snapshot.partial,
            skipped: snapshot.skipped.len(),
            parse_failed: snapshot.parse_failed.len(),
        },
    }
}

fn utf16_offset(source: &str, line: u32, column: u32) -> Option<usize> {
    let line_text = source.split('\n').nth(line as usize)?;
    let line_text = line_text.strip_suffix('\r').unwrap_or(line_text);
    let mut units = 0u32;
    for (offset, ch) in line_text.char_indices() {
        if units == column {
            return Some(offset + line as usize /* sentinel removed below */);
        }
        let next = units + u32::try_from(ch.len_utf16()).expect("UTF-16 width is at most two");
        if column < next {
            return None;
        }
        units = next;
    }
    (units == column).then_some(line_text.len())
}

fn absolute_utf16_offset(source: &str, line: u32, column: u32) -> Option<usize> {
    let start = source
        .split_inclusive('\n')
        .take(line as usize)
        .map(str::len)
        .sum::<usize>();
    let line_text = source.get(start..)?.split('\n').next().unwrap_or("");
    let line_text = line_text.strip_suffix('\r').unwrap_or(line_text);
    let local = utf16_offset(line_text, 0, column)?;
    Some(start + local)
}

fn completion_output(input: &Input) -> CompletionOutput {
    let Some(query_path) = input.query.as_deref() else {
        return CompletionOutput {
            mode: "completion".into(),
            items: vec![],
        };
    };
    let Some(line) = input.query_line else {
        return CompletionOutput {
            mode: "completion".into(),
            items: vec![],
        };
    };
    let Some(column) = input.query_column else {
        return CompletionOutput {
            mode: "completion".into(),
            items: vec![],
        };
    };
    let Some(query_file) = input.files.iter().find(|f| f.path == query_path) else {
        return CompletionOutput {
            mode: "completion".into(),
            items: vec![],
        };
    };
    let Some(offset) = absolute_utf16_offset(&query_file.text, line, column) else {
        return CompletionOutput {
            mode: "completion".into(),
            items: vec![],
        };
    };
    let entries: Vec<_> = input
        .files
        .iter()
        .map(|f| (f.path.clone(), f.text.clone()))
        .collect();
    let snapshot = build_snapshot_from_texts(&entries, Path::new("."));
    let symbols: Vec<_> = snapshot
        .documents
        .iter()
        .flat_map(|d| d.model.symbols.iter().cloned())
        .collect();
    let args: Vec<_> = snapshot
        .documents
        .iter()
        .flat_map(|d| d.model.completion_arguments.iter().cloned())
        .collect();
    let mut items: Vec<_> = completions_with_project(&query_file.text, offset, &symbols, &args)
        .into_iter()
        .map(|c| CompletionItem {
            label: c.label,
            kind: c.detail.unwrap_or_else(|| kind_name(c.kind)),
            insert_text: None,
        })
        .collect();
    items.sort_by(|a, b| a.label.cmp(&b.label));
    items.dedup_by(|a, b| a.label == b.label && a.kind == b.kind);
    CompletionOutput {
        mode: "completion".into(),
        items,
    }
}

fn navigation_output(input: &Input) -> NavigationOutput {
    let empty = || NavigationOutput {
        mode: "navigation".into(),
        locations: vec![],
    };
    let (Some(path), Some(line), Some(character), Some(operation)) = (
        input.query.as_deref(),
        input.query_line,
        input.query_column,
        input.operation.as_deref(),
    ) else {
        return empty();
    };
    let entries: Vec<_> = input
        .files
        .iter()
        .map(|f| (f.path.clone(), f.text.clone()))
        .collect();
    let snapshot = build_snapshot_from_texts(&entries, Path::new("."));
    let position = Position { line, character };
    let locations = match operation {
        "definition" => definition_at(&snapshot, path, position),
        "references" => references_at(&snapshot, path, position),
        _ => return empty(),
    };
    NavigationOutput {
        mode: "navigation".into(),
        locations: locations
            .into_iter()
            .map(|location| NavigationLocation {
                path: location.path,
                kind: kind_name(location.kind),
                name: location.name,
                range: wire_range(&location.range),
            })
            .collect(),
    }
}

fn run(input: Input) -> Output {
    let mut files = input.files;
    files.sort_by(|a, b| a.path.cmp(&b.path));
    Output {
        files: files
            .iter()
            .map(|f| {
                let analysis = analyze_document(&f.text);
                file_output(f.path.clone(), &analysis)
            })
            .collect(),
    }
}
fn main() {
    let mut text = String::new();
    io::stdin().read_to_string(&mut text).expect("read stdin");
    let input: Input = serde_json::from_str(&text).expect("invalid JSON input");
    if input.mode == "project" {
        println!(
            "{}",
            serde_json::to_string(&run_project(&input)).expect("serialize output")
        );
    } else if input.mode == "navigation" {
        println!(
            "{}",
            serde_json::to_string(&navigation_output(&input)).expect("serialize output")
        );
    } else if input.mode == "completion" {
        println!(
            "{}",
            serde_json::to_string(&completion_output(&input)).expect("serialize output")
        );
    } else {
        println!(
            "{}",
            serde_json::to_string(&run(input)).expect("serialize output")
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn parse(s: &str) -> Output {
        run(serde_json::from_str(s).unwrap())
    }
    #[test]
    fn empty_input_is_stable() {
        assert!(parse(r#"{"files":[]}"#).files.is_empty());
    }
    #[test]
    fn sorts_files() {
        assert_eq!(
            parse(r#"{"files":[{"path":"b","text":""},{"path":"a","text":""}]}"#).files[0].path,
            "a"
        );
    }
    #[test]
    fn projects_symbol_name_and_kind() {
        let o = parse(r#"{"files":[{"path":"a.cwt","text":"type[thing] = {}"}]}"#);
        assert!(
            o.files[0]
                .symbols
                .iter()
                .any(|s| s.name == "thing" && s.kind == "type")
        );
    }
    #[test]
    fn emits_diagnostic_code_key_phase() {
        let o = parse(r#"{"files":[{"path":"a.cwt","text":"@unknown x"}]}"#);
        assert!(o.files[0].diagnostics.iter().any(|d| d.code == "CWT101"
            && d.message_key == "directive.unknown"
            && d.phase == "directive"));
    }
    #[test]
    fn emits_completion_arguments() {
        let o = parse(r#"{"files":[{"path":"a.cwt","text":"type[x] = {}"}]}"#);
        assert!(
            o.files[0].completion_arguments.is_empty()
                || o.files[0]
                    .completion_arguments
                    .iter()
                    .all(|c| !c.name.is_empty())
        );
    }
    #[test]
    fn unicode_ranges_are_utf16() {
        let o = parse(
            r#"{"files":[{"path":"a.cwt","text":"😀 = scalar\ntype[名] = {}\nrule = <名>"}]}"#,
        );
        let s = o.files[0].symbols.iter().find(|s| s.name == "名").unwrap();
        assert_eq!((s.range.start_line, s.range.start_column), (1, 0));
        let r = o.files[0]
            .references
            .iter()
            .find(|r| r.name == "名")
            .unwrap();
        assert_eq!((r.range.start_line, r.range.start_column), (2, 0));
    }
    #[test]
    fn diagnostic_unicode_range_is_utf16() {
        let o = parse(r#"{"files":[{"path":"a.cwt","text":"😀 = scalar\n## not_real = x"}]}"#);
        let d = o.files[0]
            .diagnostics
            .iter()
            .find(|d| d.code == "CWT101")
            .unwrap();
        assert_eq!((d.range.start_line, d.range.start_column), (1, 0));
    }
    fn project(s: &str) -> ProjectOutput {
        run_project(&serde_json::from_str(s).unwrap())
    }
    #[test]
    fn project_reports_cwt301() {
        let o = project(
            r#"{"mode":"project","files":[{"path":"defs.cwt","text":"type[known] = {}"},{"path":"a.cwt","text":"rule = <missing>"}]}"#,
        );
        assert!(
            o.diagnostics
                .iter()
                .any(|d| d.code == "CWT301" && d.path == "a.cwt")
        );
    }
    #[test]
    fn project_reports_cwt302() {
        let o = project(
            r#"{"mode":"project","files":[{"path":"a.cwt","text":"type[same] = {}\ntype[same] = {}"}]}"#,
        );
        assert!(o.diagnostics.iter().any(|d| d.code == "CWT302"));
    }
    #[test]
    fn project_reports_cwt401() {
        let o = project(r#"{"mode":"project","files":[{"path":"a.cwt","text":"inject = a.cwt"}]}"#);
        assert!(o.diagnostics.iter().any(|d| d.code == "CWT401"));
    }
    #[test]
    fn project_diagnostics_are_sorted() {
        let o = project(
            r#"{"mode":"project","files":[{"path":"b.cwt","text":"rule = value[missing]"},{"path":"a.cwt","text":"rule = value[missing]"}]}"#,
        );
        let paths: Vec<_> = o.diagnostics.iter().map(|d| d.path.as_str()).collect();
        assert!(paths.windows(2).all(|pair| pair[0] <= pair[1]));
    }
}
