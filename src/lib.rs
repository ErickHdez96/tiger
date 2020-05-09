//! # Tiger
//! Compiler for the Tiger language, as per the [reference
//! manual](https://www.lrde.epita.fr/~tiger/tiger.html).

pub mod token;
pub mod span;
pub mod lexer;
pub mod symbol;
pub mod source_file;
pub mod error_reporter;
pub mod terminal;

pub use token::{Token, TokenKind};
pub use span::Span;
pub use symbol::Symbol;
pub use lexer::tokenize;
pub use source_file::SourceFile;
pub use error_reporter::{CompilerError, print_compiler_errors};

pub fn count_lines(s: &str) -> usize {
    s
        .as_bytes()
        .iter()
        .fold(0, |acc, &b| if b == b'\n' { acc + 1 } else { acc })
}

#[test]
fn test_count_lines() {
    assert_eq!(count_lines(""), 0);
    assert_eq!(count_lines("\n"), 1);
    assert_eq!(count_lines("ab\ncd\nef\ngh\nij"), 4);
}
