#![allow(clippy::len_without_is_empty)]
/// The span of some item during the compilation process.
/// The `offset` is the start of the item in the sourcefile.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Span {
    offset: u32,
    len: u32,
}

impl Span {
    /// Create a new span with the given `offset` and `len`.
    pub fn new(offset: u32, len: u32) -> Self {
        Self { offset, len }
    }

    /// Get the offset of the span.
    pub fn offset(self) -> u32 {
        self.offset
    }

    /// Get the length of the span.
    pub fn len(self) -> u32 {
        self.len
    }

    /// Create a new `Span` starting from `self.offset`, and ending in `other.offset + other.len`.
    ///
    /// For example:
    /// ```
    /// use tiger::Span;
    ///
    /// let start_span = Span::new(0, 5);
    /// let end_span = Span::new(15, 5);
    /// let extended_span = start_span.extend(end_span);
    /// assert_eq!(extended_span.offset(), 0);
    /// assert_eq!(extended_span.len(), 20);
    /// ```
    pub fn extend(self, other: Self) -> Self {
        Self {
            offset: self.offset,
            len: (other.offset + other.len) - self.offset,
        }
    }

    /// Given two absolute `Span`s, the first `Span` inside of the second `Span`, shifts the first
    /// to be relative to the second one.
    ///
    /// For example:
    /// ```
    /// use tiger::Span;
    ///
    /// let outer_span = Span::new(10, 5);
    /// let inner_span = Span::new(12, 3);
    /// assert_eq!(inner_span.relative_span(outer_span), Span::new(2, 3));
    /// ```
    pub fn relative_span(self, other: Self) -> Self {
        assert!(self.offset >= other.offset && self.offset + self.len <= other.offset + other.len);
        Self {
            offset: self.offset - other.offset,
            len: self.len,
        }
    }
}
