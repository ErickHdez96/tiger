//! # Tiger
//! Compiler for the Tiger language, as per the [reference
//! manual](https://www.lrde.epita.fr/~tiger/tiger.html).

pub mod ast;
pub mod error_reporter;
pub mod lexer;
pub mod parser;
pub mod source_file;
pub mod span;
pub mod symbol;
pub mod terminal;
pub mod token;

pub use ast::Item;
pub use error_reporter::{print_compiler_errors, CompilerError};
pub use lexer::tokenize;
pub use parser::parse;
pub use source_file::SourceFile;
pub use span::Span;
pub use symbol::Symbol;
pub use token::{Token, TokenKind};

pub fn count_lines(s: &str) -> usize {
    s.as_bytes()
        .iter()
        .fold(0, |acc, &b| if b == b'\n' { acc + 1 } else { acc })
}

#[test]
fn test_count_lines() {
    assert_eq!(count_lines(""), 0);
    assert_eq!(count_lines("\n"), 1);
    assert_eq!(count_lines("ab\ncd\nef\ngh\nij"), 4);
}
