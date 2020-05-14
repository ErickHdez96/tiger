use crate::Symbol;
use std::collections::HashMap;

#[derive(Debug)]
pub struct Env<'a, T> {
    parent: Option<&'a Env<'a, T>>,
    items: HashMap<Symbol, T>,
}

impl<'a, T> Env<'a, T> {
    pub fn new() -> Self {
        Self {
            parent: None,
            items: HashMap::new(),
        }
    }

    pub fn with_parent(parent: &'a Env<'a, T>) -> Self {
        Self {
            parent: Some(&parent),
            items: HashMap::new(),
        }
    }

    pub fn insert(&mut self, s: Symbol, t: T) {
        self.items.insert(s, t);
    }

    pub fn get(&self, s: Symbol) -> Option<&T> {
        self.items.get(&s).or_else(|| match self.parent {
            Some(p) => p.get(s),
            _ => None,
        })
    }
}
