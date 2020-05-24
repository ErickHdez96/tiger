use crate::flow::FlowGraph;
use crate::frame::X86_64;
use crate::graph::{Entry, Graph};
use crate::temp::Temp;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug)]
pub struct InterferenceGraph {
    graph: Graph<Temp>,
    temp_nodes: HashMap<Temp, Entry>,
    graph_nodes: HashMap<Entry, Temp>,
    moves: Vec<usize>,
}

impl fmt::Display for InterferenceGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for node in self.graph.nodes() {
            write!(f, "Node: {:<4}\t", X86_64::temp_to_string(*node.element()))?;
            writeln!(
                f,
                "adjacent: [{}]\t",
                node.adjacent()
                    .iter()
                    .map(|e| X86_64::temp_to_string(self.graph_nodes[e]))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }

        Ok(())
    }
}

pub fn interference_graph(flow_graph: FlowGraph) -> InterferenceGraph {
    let mut live_in: HashMap<usize, HashSet<Temp>> = HashMap::new();
    let mut live_out: HashMap<usize, HashSet<Temp>> = HashMap::new();

    loop {
        // TODO: Don't clone
        let old_live_in = live_in.clone();
        let old_live_out = live_out.clone();

        for (i, node) in flow_graph.control().nodes().iter().enumerate() {
            let live_out_entry = live_out.entry(i).or_insert_with(HashSet::new);
            let out_def_difference = live_out_entry.difference(node.element().definitions());

            let mut in_entry = node.element().uses().clone();
            in_entry.extend(out_def_difference);
            live_in.insert(i, in_entry);

            let mut out_entry = HashSet::new();
            for successor in node.successors() {
                if let Some(entry) = live_in.get(&successor.as_usize()) {
                    out_entry.extend(entry);
                }
            }
            live_out.insert(i, out_entry);
        }

        if live_in == old_live_in && live_out == old_live_out {
            break;
        }
    }

    macro_rules! get_graph_node {
        ($graph:expr, $temp_nodes:expr, $graph_nodes:expr, $temp:expr) => {
            match $temp_nodes.get($temp) {
                Some(e) => *e,
                None => {
                    let entry = $graph.new_node(*$temp);
                    $temp_nodes.insert(*$temp, entry);
                    $graph_nodes.insert(entry, *$temp);
                    entry
                }
            }
        };
    }

    let mut graph: Graph<Temp> = Graph::new();
    let mut temp_nodes = HashMap::new();
    let mut graph_nodes = HashMap::new();

    for (i, node) in flow_graph.control().nodes().iter().enumerate() {
        // At a move instruction a ← c where variables b1,...bj are live-out, add interference
        // edges (a,b1),...(a, bj) for any bi that is not the same as c.
        if node.element().is_move() {
            for def in node.element().definitions() {
                // TODO: Check this
                let entry = get_graph_node!(graph, temp_nodes, graph_nodes, def);

                for tmp in &live_out[&i] {
                    if node.element().uses().contains(tmp) {
                        continue;
                    }
                    let tmp_entry = get_graph_node!(graph, temp_nodes, graph_nodes, tmp);
                    graph.make_edge(entry, tmp_entry);
                }
            }
        // At any nonmove instruction that defines a variable α, where the live-out variables are
        // b1,...,bj, add interference edges(a,b1),...,(a,bj).
        } else {
            for def in node.element().definitions() {
                let entry = get_graph_node!(graph, temp_nodes, graph_nodes, def);

                for tmp in &live_out[&i] {
                    let tmp_entry = get_graph_node!(graph, temp_nodes, graph_nodes, tmp);
                    graph.make_edge(entry, tmp_entry);
                }
            }
        }
    }

    InterferenceGraph {
        graph,
        temp_nodes,
        graph_nodes,
        moves: vec![],
    }
}
