#![forbid(unsafe_code)]
#![allow(
    clippy::missing_errors_doc,
    clippy::match_same_arms,
    clippy::semicolon_if_nothing_returned
)]
//! Bounded deterministic semantic graphs, flow analysis, and project knowledge storage.
use rusqlite::{Connection, params};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::path::Path;

pub const SCHEMA_VERSION: i64 = 1;
pub const DEFAULT_LIMIT: usize = 1_000;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub struct Node {
    pub id: String,
    pub kind: String,
    pub label: String,
}
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub struct Edge {
    pub from: String,
    pub to: String,
    pub kind: String,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Direction {
    Incoming,
    Outgoing,
    Both,
}
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct GraphSlice {
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    pub truncated: bool,
}
#[derive(Clone, Debug, Default)]
pub struct Graph {
    nodes: BTreeMap<String, Node>,
    edges: BTreeSet<Edge>,
}
impl Graph {
    pub fn insert_node(&mut self, node: Node) {
        self.nodes.insert(node.id.clone(), node);
    }
    pub fn insert_edge(&mut self, edge: Edge) {
        self.edges.insert(edge);
    }
    #[must_use]
    pub fn slice(
        &self,
        seeds: &[String],
        direction: Direction,
        max_depth: usize,
        limit: usize,
    ) -> GraphSlice {
        let limit = limit.min(DEFAULT_LIMIT);
        let mut seen: BTreeSet<String> = seeds
            .iter()
            .filter(|id| self.nodes.contains_key(*id))
            .cloned()
            .collect();
        let mut queue: VecDeque<(String, usize)> = seen.iter().cloned().map(|id| (id, 0)).collect();
        let mut edges = BTreeSet::new();
        let mut truncated = false;
        while let Some((id, depth)) = queue.pop_front() {
            if depth >= max_depth {
                continue;
            }
            for edge in &self.edges {
                let next = match direction {
                    Direction::Outgoing if edge.from == id => Some(edge.to.clone()),
                    Direction::Incoming if edge.to == id => Some(edge.from.clone()),
                    Direction::Both if edge.from == id => Some(edge.to.clone()),
                    Direction::Both if edge.to == id => Some(edge.from.clone()),
                    _ => None,
                };
                if let Some(next) = next {
                    if seen.len() >= limit && !seen.contains(&next) {
                        truncated = true;
                        continue;
                    }
                    edges.insert(edge.clone());
                    if seen.insert(next.clone()) {
                        queue.push_back((next, depth + 1));
                    }
                }
            }
        }
        GraphSlice {
            nodes: seen
                .into_iter()
                .filter_map(|id| self.nodes.get(&id).cloned())
                .collect(),
            edges: edges.into_iter().collect(),
            truncated,
        }
    }
}
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct InlineGraph {
    pub graph: GraphSlice,
    pub cycles: Vec<Vec<String>>,
    pub unresolved: Vec<String>,
}
#[must_use]
pub fn inline_graph(
    definitions: &BTreeMap<String, Vec<String>>,
    root: &str,
    limit: usize,
) -> InlineGraph {
    let mut graph = Graph::default();
    for name in definitions.keys() {
        graph.insert_node(Node {
            id: name.clone(),
            kind: "inline".into(),
            label: name.clone(),
        });
    }
    let mut unresolved = BTreeSet::new();
    for (from, calls) in definitions {
        for to in calls {
            if definitions.contains_key(to) {
                graph.insert_edge(Edge {
                    from: from.clone(),
                    to: to.clone(),
                    kind: "calls".into(),
                });
            } else {
                unresolved.insert(to.clone());
            }
        }
    }
    let slice = graph.slice(&[root.to_owned()], Direction::Outgoing, 64, limit);
    let mut cycles = Vec::new();
    for edge in &slice.edges {
        if edge.from == edge.to {
            cycles.push(vec![edge.from.clone()]);
        } else if slice
            .edges
            .iter()
            .any(|other| other.from == edge.to && other.to == edge.from)
        {
            let mut pair = vec![edge.from.clone(), edge.to.clone()];
            pair.sort();
            if !cycles.contains(&pair) {
                cycles.push(pair);
            }
        }
    }
    InlineGraph {
        graph: slice,
        cycles,
        unresolved: unresolved.into_iter().collect(),
    }
}
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct FlowAnalysis {
    pub definitions: Vec<String>,
    pub reads: Vec<String>,
    pub writes: Vec<String>,
    pub calls: Vec<String>,
    pub unresolved: Vec<String>,
}
#[must_use]
pub fn analyze_pdx_flow(text: &str, limit: usize) -> FlowAnalysis {
    let mut out = FlowAnalysis::default();
    let mut known = BTreeSet::new();
    for line in text.lines().take(limit) {
        let line = line.split('#').next().unwrap_or("").trim();
        if let Some((left, right)) = line.split_once('=') {
            let key = left.trim().to_owned();
            if !key.is_empty() {
                known.insert(key.clone());
                out.definitions.push(key.clone());
                out.writes.push(key);
            }
            for token in right
                .split(|c: char| !c.is_alphanumeric() && c != '_' && c != '@')
                .filter(|s| !s.is_empty())
            {
                if token.starts_with('@') {
                    out.reads.push(token.to_owned());
                }
                if token.starts_with("scripted_") {
                    out.calls.push(token.to_owned());
                }
            }
        }
    }
    out.definitions.sort();
    out.definitions.dedup();
    out.reads.sort();
    out.reads.dedup();
    out.writes.sort();
    out.writes.dedup();
    out.calls.sort();
    out.calls.dedup();
    out.unresolved = out
        .reads
        .iter()
        .filter(|name| !known.contains(*name))
        .cloned()
        .collect();
    out
}

#[derive(Debug)]
pub enum StoreError {
    Sql(rusqlite::Error),
    StaleSchema,
    StaleFingerprint,
}
impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for StoreError {}
impl From<rusqlite::Error> for StoreError {
    fn from(e: rusqlite::Error) -> Self {
        Self::Sql(e)
    }
}
pub struct ProjectKnowledgeStore {
    connection: Connection,
}
impl ProjectKnowledgeStore {
    pub fn open(path: &Path, fingerprint: &str) -> Result<Self, StoreError> {
        let connection = Connection::open(path)?;
        connection.execute_batch("CREATE TABLE IF NOT EXISTS metadata(key TEXT PRIMARY KEY,value TEXT NOT NULL);CREATE TABLE IF NOT EXISTS nodes(id TEXT PRIMARY KEY,kind TEXT NOT NULL,label TEXT NOT NULL);CREATE TABLE IF NOT EXISTS edges(src TEXT NOT NULL,dst TEXT NOT NULL,kind TEXT NOT NULL,PRIMARY KEY(src,dst,kind));")?;
        let schema: Option<String> = connection
            .query_row("SELECT value FROM metadata WHERE key='schema'", [], |r| {
                r.get(0)
            })
            .ok();
        if let Some(schema) = schema {
            if schema != SCHEMA_VERSION.to_string() {
                return Err(StoreError::StaleSchema);
            }
        }
        connection.execute(
            "INSERT OR REPLACE INTO metadata(key,value) VALUES('schema',?1)",
            [SCHEMA_VERSION.to_string()],
        )?;
        let old: Option<String> = connection
            .query_row(
                "SELECT value FROM metadata WHERE key='fingerprint'",
                [],
                |r| r.get(0),
            )
            .ok();
        if let Some(old) = old {
            if old != fingerprint {
                return Err(StoreError::StaleFingerprint);
            }
        }
        connection.execute(
            "INSERT OR REPLACE INTO metadata(key,value) VALUES('fingerprint',?1)",
            [fingerprint],
        )?;
        Ok(Self { connection })
    }
    pub fn replace(&mut self, nodes: &[Node], edges: &[Edge]) -> Result<(), StoreError> {
        let tx = self.connection.transaction()?;
        tx.execute("DELETE FROM edges", [])?;
        tx.execute("DELETE FROM nodes", [])?;
        for n in nodes {
            tx.execute(
                "INSERT INTO nodes(id,kind,label) VALUES(?1,?2,?3)",
                params![n.id, n.kind, n.label],
            )?;
        }
        for e in edges {
            tx.execute(
                "INSERT INTO edges(src,dst,kind) VALUES(?1,?2,?3)",
                params![e.from, e.to, e.kind],
            )?;
        }
        tx.commit()?;
        Ok(())
    }
    pub fn query(&self, query: &str, limit: usize) -> Result<GraphSlice, StoreError> {
        let pattern = format!("%{}%", query.replace('%', r"\%"));
        let mut stmt=self.connection.prepare("SELECT id,kind,label FROM nodes WHERE id LIKE ?1 OR label LIKE ?1 ORDER BY id LIMIT ?2")?;
        let nodes = stmt
            .query_map(
                params![
                    pattern,
                    i64::try_from(limit.min(DEFAULT_LIMIT)).unwrap_or(i64::MAX)
                ],
                |r| {
                    Ok(Node {
                        id: r.get(0)?,
                        kind: r.get(1)?,
                        label: r.get(2)?,
                    })
                },
            )?
            .collect::<Result<Vec<_>, _>>()?;
        let ids: BTreeSet<_> = nodes.iter().map(|n| n.id.clone()).collect();
        let mut stmt = self
            .connection
            .prepare("SELECT src,dst,kind FROM edges ORDER BY src,dst,kind")?;
        let edges = stmt
            .query_map([], |r| {
                Ok(Edge {
                    from: r.get(0)?,
                    to: r.get(1)?,
                    kind: r.get(2)?,
                })
            })?
            .filter_map(Result::ok)
            .filter(|e| ids.contains(&e.from) || ids.contains(&e.to))
            .take(limit.min(DEFAULT_LIMIT))
            .collect();
        Ok(GraphSlice {
            truncated: nodes.len() >= limit.min(DEFAULT_LIMIT),
            nodes,
            edges,
        })
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn graph_bounds_and_directions() {
        let mut g = Graph::default();
        for id in ["a", "b", "c"] {
            g.insert_node(Node {
                id: id.into(),
                kind: "k".into(),
                label: id.into(),
            })
        }
        g.insert_edge(Edge {
            from: "a".into(),
            to: "b".into(),
            kind: "x".into(),
        });
        g.insert_edge(Edge {
            from: "b".into(),
            to: "c".into(),
            kind: "x".into(),
        });
        assert_eq!(
            g.slice(&["a".into()], Direction::Outgoing, 1, 10)
                .nodes
                .len(),
            2
        );
        assert_eq!(
            g.slice(&["c".into()], Direction::Incoming, 2, 10)
                .nodes
                .len(),
            3
        );
        assert!(g.slice(&["a".into()], Direction::Both, 9, 2).truncated)
    }
    #[test]
    fn inline_cycles_and_unresolved() {
        let defs = BTreeMap::from([
            ("a".into(), vec!["b".into(), "missing".into()]),
            ("b".into(), vec!["a".into()]),
        ]);
        let result = inline_graph(&defs, "a", 10);
        assert_eq!(result.cycles, vec![vec!["a".to_owned(), "b".to_owned()]]);
        assert_eq!(result.unresolved, vec!["missing"])
    }
    #[test]
    fn flow_is_deterministic() {
        let f = analyze_pdx_flow(
            "x = @missing
scripted_effect = yes",
            20,
        );
        assert!(f.unresolved.contains(&"@missing".into()));
        assert!(f.definitions.contains(&"x".into()))
    }
    #[test]
    fn sqlite_fingerprint_and_order() {
        let mut store = ProjectKnowledgeStore::open(Path::new(":memory:"), "one").unwrap();
        let nodes = vec![
            Node {
                id: "b".into(),
                kind: "k".into(),
                label: "B".into(),
            },
            Node {
                id: "a".into(),
                kind: "k".into(),
                label: "A".into(),
            },
        ];
        store.replace(&nodes, &[]).unwrap();
        assert_eq!(store.query("", 10).unwrap().nodes[0].id, "a");
    }
}
