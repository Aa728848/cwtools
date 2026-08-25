#![forbid(unsafe_code)]
#![allow(clippy::missing_errors_doc, clippy::must_use_candidate)]
//! Bounded deterministic graph traversal and static flow contracts.

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub const MAX_DEPTH: usize = 64;
pub const MAX_NODES: usize = 1_000;
pub const MAX_EDGES: usize = 3_000;
pub const MAX_FLOW_LINES: usize = 100_000;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GraphNode {
    pub id: String,
    pub kind: String,
    pub label: String,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GraphEdge {
    pub source: String,
    pub target: String,
    pub kind: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Direction {
    Incoming,
    Outgoing,
    Both,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GraphQuery {
    pub seeds: Vec<String>,
    pub direction: Direction,
    pub max_depth: usize,
    pub max_nodes: usize,
    pub max_edges: usize,
}

impl Default for GraphQuery {
    fn default() -> Self {
        Self {
            seeds: Vec::new(),
            direction: Direction::Both,
            max_depth: 1,
            max_nodes: 100,
            max_edges: 300,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GraphResult {
    pub nodes: Vec<GraphNode>,
    pub edges: Vec<GraphEdge>,
    pub truncated: bool,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Graph {
    nodes: BTreeMap<String, GraphNode>,
    edges: BTreeSet<GraphEdge>,
}

impl Graph {
    pub fn insert_node(&mut self, node: GraphNode) {
        self.nodes.insert(node.id.clone(), node);
    }

    pub fn insert_edge(&mut self, edge: GraphEdge) {
        self.edges.insert(edge);
    }

    pub fn query(&self, query: &GraphQuery) -> GraphResult {
        let max_depth = query.max_depth.min(MAX_DEPTH);
        let max_nodes = query.max_nodes.clamp(1, MAX_NODES);
        let max_edges = query.max_edges.clamp(1, MAX_EDGES);
        let mut seen: BTreeSet<String> = query
            .seeds
            .iter()
            .filter(|id| self.nodes.contains_key(*id))
            .cloned()
            .collect();
        let mut queue: VecDeque<(String, usize)> = seen.iter().cloned().map(|id| (id, 0)).collect();
        let mut edges = BTreeSet::new();
        let mut truncated = seen.len() > max_nodes;
        if seen.len() > max_nodes {
            seen = seen.into_iter().take(max_nodes).collect();
            queue = seen.iter().cloned().map(|id| (id, 0)).collect();
        }
        while let Some((id, depth)) = queue.pop_front() {
            if depth >= max_depth {
                continue;
            }
            for edge in &self.edges {
                let next = match query.direction {
                    Direction::Outgoing => (edge.source == id).then_some(&edge.target),
                    Direction::Both if edge.source == id => Some(&edge.target),
                    Direction::Incoming | Direction::Both => {
                        (edge.target == id).then_some(&edge.source)
                    }
                };
                let Some(next) = next else { continue };
                if edges.len() >= max_edges {
                    truncated = true;
                    continue;
                }
                if !seen.contains(next) && seen.len() >= max_nodes {
                    truncated = true;
                    continue;
                }
                edges.insert(edge.clone());
                if seen.insert(next.clone()) {
                    queue.push_back((next.clone(), depth + 1));
                }
            }
        }
        GraphResult {
            nodes: seen
                .into_iter()
                .filter_map(|id| self.nodes.get(&id).cloned())
                .collect(),
            edges: edges.into_iter().collect(),
            truncated,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FlowQuery {
    pub max_lines: usize,
    pub max_facts: usize,
}

impl Default for FlowQuery {
    fn default() -> Self {
        Self {
            max_lines: 10_000,
            max_facts: 1_000,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FlowResult {
    pub definitions: Vec<String>,
    pub reads: Vec<String>,
    pub writes: Vec<String>,
    pub calls: Vec<String>,
    pub unresolved: Vec<String>,
    pub truncated: bool,
}

#[must_use]
pub fn analyze_flow(text: &str, query: &FlowQuery) -> FlowResult {
    let max_lines = query.max_lines.clamp(1, MAX_FLOW_LINES);
    let max_facts = query.max_facts.clamp(1, MAX_NODES);
    let total_lines = text.lines().count();
    let mut definitions = BTreeSet::new();
    let mut reads = BTreeSet::new();
    let mut writes = BTreeSet::new();
    let mut calls = BTreeSet::new();
    let mut fact_limit_hit = false;
    for line in text.lines().take(max_lines) {
        let line = line.split('#').next().unwrap_or("").trim();
        let Some((left, right)) = line.split_once('=') else {
            continue;
        };
        let key = left.trim();
        if !key.is_empty() {
            definitions.insert(key.to_owned());
            writes.insert(key.to_owned());
        }
        for token in right
            .split(|character: char| {
                !character.is_alphanumeric() && !matches!(character, '_' | '@' | '.' | ':')
            })
            .filter(|value| !value.is_empty())
        {
            if token.starts_with('@') {
                reads.insert(token.to_owned());
            }
            if token.starts_with("scripted_") || token.ends_with("_event") {
                calls.insert(token.to_owned());
            }
        }
        if definitions.len() + reads.len() + writes.len() + calls.len() > max_facts {
            fact_limit_hit = true;
            break;
        }
    }
    let cap = |values: BTreeSet<String>| values.into_iter().take(max_facts).collect::<Vec<_>>();
    let definitions = cap(definitions);
    let reads = cap(reads);
    let writes = cap(writes);
    let calls = cap(calls);
    let known: BTreeSet<&String> = definitions.iter().collect();
    let unresolved = reads
        .iter()
        .filter(|value| !known.contains(value))
        .take(max_facts)
        .cloned()
        .collect();
    FlowResult {
        definitions,
        reads,
        writes,
        calls,
        unresolved,
        truncated: total_lines > max_lines || fact_limit_hit,
    }
}

pub mod graph {
    pub use super::{Direction, Graph, GraphEdge, GraphNode, GraphQuery, GraphResult};
}

pub mod flow {
    pub use super::{FlowQuery, FlowResult, analyze_flow};
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(id: &str) -> GraphNode {
        GraphNode {
            id: id.into(),
            kind: "event".into(),
            label: id.into(),
        }
    }

    #[test]
    fn graph_query_is_directional_bounded_and_sorted() {
        let mut graph = Graph::default();
        for id in ["c", "a", "b"] {
            graph.insert_node(node(id));
        }
        graph.insert_edge(GraphEdge {
            source: "a".into(),
            target: "b".into(),
            kind: "calls".into(),
        });
        graph.insert_edge(GraphEdge {
            source: "b".into(),
            target: "c".into(),
            kind: "calls".into(),
        });
        let result = graph.query(&GraphQuery {
            seeds: vec!["a".into()],
            direction: Direction::Outgoing,
            max_depth: 8,
            max_nodes: 2,
            max_edges: 8,
        });
        assert_eq!(
            result
                .nodes
                .iter()
                .map(|value| value.id.as_str())
                .collect::<Vec<_>>(),
            vec!["a", "b"]
        );
        assert!(result.truncated);
        let incoming = graph.query(&GraphQuery {
            seeds: vec!["c".into()],
            direction: Direction::Incoming,
            max_depth: 2,
            ..GraphQuery::default()
        });
        assert_eq!(incoming.nodes.len(), 3);
    }

    #[test]
    fn graph_query_is_deterministic() {
        let mut graph = Graph::default();
        for id in ["b", "a"] {
            graph.insert_node(node(id));
        }
        graph.insert_edge(GraphEdge {
            source: "a".into(),
            target: "b".into(),
            kind: "calls".into(),
        });
        let query = GraphQuery {
            seeds: vec!["a".into()],
            ..GraphQuery::default()
        };
        assert_eq!(graph.query(&query), graph.query(&query));
    }

    #[test]
    fn flow_is_bounded_sorted_and_reports_unresolved() {
        let result = analyze_flow(
            "z = @missing\na = scripted_effect\ncall = country_event",
            &FlowQuery {
                max_lines: 2,
                max_facts: 10,
            },
        );
        assert_eq!(result.definitions, vec!["a", "z"]);
        assert_eq!(result.reads, vec!["@missing"]);
        assert_eq!(result.calls, vec!["scripted_effect"]);
        assert_eq!(result.unresolved, vec!["@missing"]);
        assert!(result.truncated);
    }

    #[test]
    fn zero_limits_are_normalized_without_panics() {
        let result = analyze_flow(
            "x = @y",
            &FlowQuery {
                max_lines: 0,
                max_facts: 0,
            },
        );
        assert_eq!(result.definitions, vec!["x"]);
        let mut graph = Graph::default();
        graph.insert_node(node("x"));
        assert_eq!(
            graph
                .query(&GraphQuery {
                    seeds: vec!["x".into()],
                    max_nodes: 0,
                    max_edges: 0,
                    ..GraphQuery::default()
                })
                .nodes
                .len(),
            1
        );
    }
}
