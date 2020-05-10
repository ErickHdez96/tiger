//! # String interning
//!
//! This module handels the interning and lookup of [`String`]s.

use std::cell::RefCell;
use std::collections::HashMap;
use std::mem;

/// A Symbol is a representation of an interned [`String`]. They allow faster string comparison, as
/// it is only required to compare two [`u32`]s.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

impl Symbol {
    /// Retrieve the internal `u32` representation of the Symbol.
    pub fn as_u32(self) -> u32 {
        self.0
    }

    /// Intern a `String` and receive a `Symbol` that points to it.
    ///
    /// For example:
    /// ```no_run
    /// use tiger::Symbol;
    ///
    /// let s = Symbol::intern("Hello, world!");
    /// assert_eq!(s.as_str(), "Hello, world!");
    /// ```
    pub fn intern(string: impl Into<String>) -> Self {
        with_interner(|interner| interner.intern(string))
    }

    /// Retrieve the string representation of the symbol.
    ///
    /// It is assumed that the string interner lives for the whole life of the compiler, hence the
    /// `'static` lifetime.
    ///
    /// # Panic
    /// If the symbol does not exist in the interner, for example, if you have created the symbol
    /// by hand.
    pub fn as_str(self) -> &'static str {
        // The GLOBALS variable is expected to live for the whole lifetime of the compiler. As
        // such, the interner will be initialized at startup and droped once the program
        // terminates. This means that the strings inside it can be expected to have a static
        // lifetime.
        with_interner(|interner| unsafe { mem::transmute::<&str, &str>(interner.lookup(self)) })
    }
}

/// # String interner.
/// Given a [`String`], interns it and returns a [`Symbol`], the strings are never dropped, they
/// have the same lifetime of the `Interner`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Interner {
    data: HashMap<String, Symbol>,
}

impl Interner {
    fn new() -> Self {
        Self {
            data: HashMap::new(),
        }
    }

    fn intern(&mut self, string: impl Into<String>) -> Symbol {
        let string = string.into();
        if let Some(symbol) = self.data.get(&string) {
            return *symbol;
        }

        let symbol = Symbol(self.data.len() as u32);
        self.data.insert(string, symbol);
        symbol
    }

    fn lookup(&self, symbol: Symbol) -> &str {
        for (key, value) in self.data.iter() {
            if symbol == *value {
                return key;
            }
        }
        panic!(
            "The given symbol {}, is not in the interner.",
            symbol.as_u32()
        );
    }
}

#[inline(always)]
fn with_interner<T, F: FnOnce(&mut Interner) -> T>(f: F) -> T {
    GLOBALS.with(|globals| f(&mut *globals.symbols.borrow_mut()))
}

/// Refer to the [`GLOBALS`] static variable for more information.
#[derive(Debug)]
pub struct Globals {
    symbols: RefCell<Interner>,
}

impl Globals {
    fn new() -> Self {
        Self {
            symbols: RefCell::new(Interner::new()),
        }
    }
}

thread_local!(
    /// Contains the string interner, being a static variable, all of the strings inside it can be
    /// assumed to have `'static` lifetime, since they are never dropped.
    pub static GLOBALS: Globals = Globals::new()
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_string_interning_and_lookup() {
        let mut interner = Interner::new();
        let s = interner.intern("Hello");
        assert_eq!(interner.lookup(s), "Hello");
    }

    #[test]
    fn test_multiple_string_interning_and_lookup() {
        let mut interner = Interner::new();
        let s = interner.intern("Hello");
        assert_eq!(interner.lookup(s), "Hello");
        let s2 = interner.intern("World");
        assert_eq!(interner.lookup(s2), "World");
        let s3 = interner.intern("!");
        assert_eq!(interner.lookup(s3), "!");
        assert_eq!(interner.lookup(s2), "World");
        assert_eq!(interner.lookup(s), "Hello");
    }

    #[test]
    fn test_interning_similar_strings() {
        let mut interner = Interner::new();
        let s = interner.intern("Hello");
        assert_eq!(interner.lookup(s), "Hello");
        let s2 = interner.intern("Hello");
        assert_eq!(interner.lookup(s2), "Hello");
        assert_eq!(s, s2);
    }
}
