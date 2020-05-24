use std::collections::HashSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Entry(pub(self) usize);

impl Entry {
    fn new(n: usize) -> Self {
        Self(n)
    }

    pub fn as_usize(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<T: PartialEq + Eq> {
    element: T,
    successors: HashSet<Entry>,
    predecesors: HashSet<Entry>,
}

impl<T: PartialEq + Eq> Node<T> {
    pub fn new(content: T) -> Self {
        Self {
            element: content,
            successors: HashSet::new(),
            predecesors: HashSet::new(),
        }
    }

    pub fn element(&self) -> &T {
        &self.element
    }

    pub fn successors(&self) -> &HashSet<Entry> {
        &self.successors
    }

    pub fn predecesors(&self) -> &HashSet<Entry> {
        &self.predecesors
    }

    pub fn adjacent(&self) -> HashSet<Entry> {
        let mut adjacent = self.successors.clone();
        adjacent.extend(&self.predecesors);
        adjacent
    }
}

#[derive(Debug, Default)]
pub struct Graph<T: PartialEq + Eq> {
    nodes: Vec<Node<T>>,
}

impl<T: PartialEq + Eq> Graph<T> {
    pub fn new() -> Self {
        Self { nodes: vec![] }
    }

    pub fn nodes(&self) -> &[Node<T>] {
        &self.nodes
    }

    pub fn new_node(&mut self, content: T) -> Entry {
        self.nodes.push(Node::new(content));
        Entry::new(self.nodes.len() - 1)
    }

    pub fn make_edge(&mut self, from: Entry, to: Entry) {
        self.nodes[from.0].successors.insert(to);
        self.nodes[to.0].predecesors.insert(from);
    }

    pub fn remove_edge(&mut self, from: Entry, to: Entry) {
        self.nodes[from.0].successors.remove(&to);
        self.nodes[to.0].successors.remove(&from);
    }
}
