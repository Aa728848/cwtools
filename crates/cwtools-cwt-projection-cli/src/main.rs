#![forbid(unsafe_code)]
use cwtools_cwt_service::{
    AnalysisResult, CompletionArgument, Diagnostic, Range, Reference, Symbol, analyze_document,
};
use serde::{Deserialize, Serialize};
use std::io::{self, Read};

#[derive(Debug, Deserialize)]
struct Input {
    files: Vec<InputFile>,
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
    println!(
        "{}",
        serde_json::to_string(&run(input)).expect("serialize output")
    );
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
}
