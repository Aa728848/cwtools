#![forbid(unsafe_code)]
//! Semantic analysis compatibility crate.

pub const KNOWLEDGE_SCHEMA_VERSION: u32 = 7;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SemanticSnapshot {
    pub graph_version: i64,
    pub status: String,
}

impl SemanticSnapshot {
    #[must_use]
    pub fn is_ready(&self) -> bool {
        self.status == "ready"
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FlowAnalysis {
    pub definitions: Vec<String>,
    pub reads: Vec<String>,
    pub writes: Vec<String>,
    pub calls: Vec<String>,
    pub unresolved: Vec<String>,
}

#[must_use]
pub fn analyze_pdx_flow(text: &str, limit: usize) -> FlowAnalysis {
    let mut result = FlowAnalysis::default();
    let mut known = std::collections::BTreeSet::new();
    for line in text.lines().take(limit.clamp(1, 100_000)) {
        let line = line.split('#').next().unwrap_or("");
        let Some((left, right)) = line.split_once('=') else {
            continue;
        };
        let key = left.trim();
        if key.is_empty() {
            continue;
        }
        let key = key.to_owned();
        known.insert(key.clone());
        result.definitions.push(key.clone());
        result.writes.push(key);
        for token in right
            .split(|c: char| !c.is_alphanumeric() && !matches!(c, '_' | '@' | '.' | ':'))
            .filter(|v| !v.is_empty())
        {
            if token.starts_with('@') {
                result.reads.push(token.to_owned());
            }
            if token.starts_with("scripted_") || token.ends_with("_event") {
                result.calls.push(token.to_owned());
            }
        }
    }
    result.definitions.sort();
    result.definitions.dedup();
    result.reads.sort();
    result.reads.dedup();
    result.writes.sort();
    result.writes.dedup();
    result.calls.sort();
    result.calls.dedup();
    result.unresolved = result
        .reads
        .iter()
        .filter(|v| !known.contains(*v))
        .cloned()
        .collect();
    result
}

#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ExploreOptions {
    pub query: String,
    pub file: Option<String>,
    pub type_name: Option<String>,
    pub exact: bool,
    pub depth: usize,
    pub max_nodes: usize,
    pub max_edges: usize,
    pub include_metadata: bool,
}
#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GraphNode {
    pub id: String,
    pub entity_type: String,
    pub file: String,
    pub line: usize,
    pub score: i32,
}
#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GraphEdge {
    pub source: String,
    pub target: String,
    pub kind: String,
    pub file: String,
    pub line: usize,
}
#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticGraphResult {
    pub schema_version: u32,
    pub status: String,
    pub fresh: bool,
    pub nodes: Vec<GraphNode>,
    pub edges: Vec<GraphEdge>,
    pub truncated: bool,
}

#[must_use]
pub fn explore_project(
    texts: &[(String, String)],
    options: &ExploreOptions,
) -> SemanticGraphResult {
    let query = options.query.to_ascii_lowercase();
    let limit = options.max_nodes.clamp(1, 100);
    let mut nodes = Vec::new();
    for (file, text) in texts {
        for (line_no, line) in text.lines().enumerate() {
            let Some((left, _)) = line.split_once('=') else {
                continue;
            };
            let id = left
                .trim()
                .trim_matches(|c: char| c == '{' || c.is_whitespace());
            if id.is_empty()
                || (options.exact && !id.eq_ignore_ascii_case(&query))
                || (!options.exact
                    && !query.is_empty()
                    && !id.to_ascii_lowercase().contains(&query))
            {
                continue;
            }
            let score = if id.eq_ignore_ascii_case(&query) {
                1200
            } else if id.to_ascii_lowercase().starts_with(&query) {
                700
            } else {
                100
            };
            nodes.push(GraphNode {
                id: id.into(),
                entity_type: options
                    .type_name
                    .clone()
                    .unwrap_or_else(|| "definition".into()),
                file: file.clone(),
                line: line_no + 1,
                score,
            });
        }
    }
    nodes.sort_by(|a, b| {
        b.score
            .cmp(&a.score)
            .then_with(|| (&a.id, &a.file, a.line).cmp(&(&b.id, &b.file, b.line)))
    });
    let truncated = nodes.len() > limit;
    nodes.truncate(limit);
    SemanticGraphResult {
        schema_version: 2,
        status: "fresh".into(),
        fresh: true,
        nodes,
        edges: Vec::new(),
        truncated,
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct InlineGraphFacts {
    pub templates: Vec<String>,
    pub invocations: Vec<String>,
    pub expansions: Vec<String>,
    pub problems: Vec<String>,
    pub truncated: bool,
}
#[must_use]
pub fn explore_inline_graph(texts: &[(String, String)], limit: usize) -> InlineGraphFacts {
    let mut templates = Vec::new();
    let mut invocations = Vec::new();
    let expansions = Vec::new();
    let mut problems = Vec::new();
    for (file, text) in texts {
        if file.to_ascii_lowercase().contains("inline_scripts") {
            templates.push(file.clone());
        }
        for line in text.lines() {
            if line.contains("inline_script") {
                invocations.push(format!("{file}:{}", invocations.len() + 1));
            }
        }
    }
    if invocations.len() > limit.clamp(1, 200) {
        problems.push("inline graph result truncated".into());
    }
    invocations.truncate(limit.clamp(1, 200));
    InlineGraphFacts {
        templates,
        invocations,
        expansions,
        problems,
        truncated: false,
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct KnowledgeManifest {
    pub schema_version: u32,
    pub status: String,
    pub database_path: String,
    pub generated_at_unix_ms: i64,
}
#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct KnowledgeQuery {
    pub identifier: Option<String>,
    pub entity_type: Option<String>,
    pub limit: usize,
}
#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct KnowledgeResult {
    pub ok: bool,
    pub status: String,
    pub schema_version: u32,
    pub manifest: KnowledgeManifest,
    pub evidence: Vec<GraphNode>,
    pub truncated: bool,
}

/// Atomically exports bounded project knowledge to schema-V7 SQLite.
///
/// # Errors
/// Returns an error when the destination is invalid or SQLite/file publication fails.
pub fn export_project_knowledge(
    path: &std::path::Path,
    texts: &[(String, String)],
) -> Result<KnowledgeManifest, String> {
    let parent = path
        .parent()
        .ok_or_else(|| "invalid knowledge path".to_owned())?;
    std::fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    let temp = parent.join(format!(".knowledge-{}.tmp", std::process::id()));
    let conn = rusqlite::Connection::open(&temp).map_err(|e| e.to_string())?;
    conn.execute_batch("CREATE TABLE IF NOT EXISTS metadata (key TEXT PRIMARY KEY, value TEXT NOT NULL); CREATE TABLE IF NOT EXISTS definitions (id TEXT NOT NULL, entity_type TEXT NOT NULL, file TEXT NOT NULL, line INTEGER NOT NULL); DELETE FROM metadata; DELETE FROM definitions;").map_err(|e| e.to_string())?;
    for (file, text) in texts {
        for (line, source) in text.lines().enumerate() {
            let Some((left, _)) = source.split_once('=') else {
                continue;
            };
            let id = left.trim();
            if id.is_empty() {
                continue;
            }
            conn.execute(
                "INSERT INTO definitions(id,entity_type,file,line) VALUES (?1,'definition',?2,?3)",
                rusqlite::params![id, file, i64::try_from(line + 1).unwrap_or(i64::MAX)],
            )
            .map_err(|e| e.to_string())?;
        }
    }
    conn.execute(
        "INSERT INTO metadata(key,value) VALUES ('schema_version','7')",
        [],
    )
    .map_err(|e| e.to_string())?;
    conn.execute(
        "INSERT INTO metadata(key,value) VALUES ('source_count',?1)",
        [texts.len().to_string()],
    )
    .map_err(|e| e.to_string())?;
    drop(conn);
    if path.exists() {
        std::fs::remove_file(path).map_err(|e| e.to_string())?;
    }
    std::fs::rename(temp, path).map_err(|e| e.to_string())?;
    Ok(KnowledgeManifest {
        schema_version: 7,
        status: "fresh".into(),
        database_path: path.to_string_lossy().into(),
        generated_at_unix_ms: 0,
    })
}

/// Queries a schema-V7 knowledge database with bounded deterministic output.
///
/// # Errors
/// Returns an error for invalid schema, SQLite errors, or an unreadable database.
pub fn query_project_knowledge(
    path: &std::path::Path,
    query: &KnowledgeQuery,
) -> Result<KnowledgeResult, String> {
    let conn = rusqlite::Connection::open(path).map_err(|e| e.to_string())?;
    let schema: String = conn
        .query_row(
            "SELECT value FROM metadata WHERE key='schema_version'",
            [],
            |row| row.get(0),
        )
        .map_err(|e| e.to_string())?;
    if schema != KNOWLEDGE_SCHEMA_VERSION.to_string() {
        return Err(format!("unsupported knowledge schema {schema}"));
    }
    let mut statement = conn
        .prepare("SELECT id,entity_type,file,line FROM definitions ORDER BY id,file,line")
        .map_err(|e| e.to_string())?;
    let rows = statement
        .query_map([], |row| {
            Ok(GraphNode {
                id: row.get(0)?,
                entity_type: row.get(1)?,
                file: row.get(2)?,
                line: row.get::<_, usize>(3)?,
                score: 100,
            })
        })
        .map_err(|e| e.to_string())?;
    let limit = query.limit.clamp(1, 500);
    let mut evidence = Vec::new();
    for row in rows {
        let node = row.map_err(|e| e.to_string())?;
        if query
            .identifier
            .as_ref()
            .is_some_and(|id| !node.id.eq_ignore_ascii_case(id))
            || query
                .entity_type
                .as_ref()
                .is_some_and(|kind| !node.entity_type.eq_ignore_ascii_case(kind))
        {
            continue;
        }
        if evidence.len() >= limit {
            break;
        }
        evidence.push(node);
    }
    Ok(KnowledgeResult {
        ok: true,
        status: "fresh".to_owned(),
        schema_version: KNOWLEDGE_SCHEMA_VERSION,
        manifest: KnowledgeManifest {
            schema_version: KNOWLEDGE_SCHEMA_VERSION,
            status: "fresh".to_owned(),
            database_path: path.to_string_lossy().into_owned(),
            generated_at_unix_ms: 0,
        },
        truncated: evidence.len() == limit,
        evidence,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schema_and_readiness_are_stable() {
        assert_eq!(KNOWLEDGE_SCHEMA_VERSION, 7);
        assert!(
            SemanticSnapshot {
                graph_version: 1,
                status: "ready".into()
            }
            .is_ready()
        );
    }
}
