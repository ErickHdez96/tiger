use crate::Symbol;
use std::cell::Cell;
use std::default::Default;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Temp(u32);

impl Temp {
    /// Create a new Temp, each one is unique and different from the previous one.
    pub fn new() -> Self {
        Self(new_number())
    }
}

impl Default for Temp {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Label {
    Named(Symbol),
    Num(u32),
}

impl Label {
    /// Create a new label with a uniquely generated number.
    pub fn new() -> Self {
        Self::Num(new_number())
    }

    /// Create a new label with a given name.
    pub fn with_name(symbol: Symbol) -> Self {
        Self::Named(symbol)
    }

    /// Get the name of the current label.
    ///
    /// ## Panics
    ///
    /// If it is an anonymous label (i.e. it was created with Label::new()).
    pub fn to_str(&self) -> &'static str {
        match self {
            Label::Num(_) => panic!("Anonymous label does not have a name"),
            Label::Named(s) => s.as_str(),
        }
    }
}

impl Default for Label {
    fn default() -> Self {
        Self::new()
    }
}

fn new_number() -> u32 {
    COUNTER.with(|counter| counter.next_number())
}

#[derive(Debug, Default)]
pub struct Counter {
    current: Cell<u32>,
}

impl Counter {
    pub fn next_number(&self) -> u32 {
        let n = self.current.get();
        self.current
            .set(n.checked_add(1).expect("Too many temporals created"));
        n
    }
}

thread_local! {
    pub static COUNTER: Counter = Counter::default()
}
