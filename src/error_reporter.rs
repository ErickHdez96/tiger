use crate::{
    count_lines,
    terminal::{Color, Style},
    SourceFile, Span,
};
use std::cmp;

pub trait CompilerError {
    fn msg(&self) -> &str;
    fn snippet_span(&self) -> Span;
    fn error_span(&self) -> Span;
}

pub fn print_compiler_errors(errors: &[impl CompilerError], source_file: &SourceFile) {
    for error in errors.iter() {
        print_compiler_error(error, source_file);
    }
}

pub fn print_compiler_error(error: &impl CompilerError, source_file: &SourceFile) {
    eprintln!(
        "{}{}error:{} {}",
        Color::Red,
        Style::Bold,
        Color::Clear,
        error.msg()
    );
    let snippet_span = error.snippet_span();
    let error_span = error.error_span().relative_span(snippet_span);
    let (snippet, start_line) = source_file.get_snippet(snippet_span);
    let last_line = count_lines(&snippet) + start_line;
    let line_length = cmp::max(usize_length(last_line), 2);
    let lines_count = last_line - start_line + if snippet.ends_with('\n') { 0 } else { 1 };

    eprintln!(
        "{}{}{}>{} {}",
        Color::Cyan,
        Style::Bold,
        "-".repeat(line_length + 1),
        Color::Clear,
        source_file.path(),
    );

    if lines_count == 1 {
        print_single_line_error(snippet, error_span, start_line, line_length);
    } else {
        print_multiline_error(snippet, start_line, line_length);
    }
}

fn print_single_line_error(snipet: &str, span: Span, start_line: usize, line_length: usize) {
    eprintln!(
        "{}{}{} |{}",
        Color::Cyan,
        Style::Bold,
        " ".repeat(line_length),
        Color::Clear
    );
    eprintln!(
        "{}{}{} |{}",
        Color::Cyan,
        Style::Bold,
        " ".repeat(line_length),
        Color::Clear
    );

    let current_line = start_line + 1;
    let current_line_length = usize_length(current_line);
    eprintln!(
        "{}{}{}{} | {}{}",
        Color::Cyan,
        Style::Bold,
        " ".repeat(line_length - current_line_length),
        current_line,
        Color::Clear,
        snipet,
    );
    eprintln!(
        "{} {}{}| {}{}{}{}",
        " ".repeat(line_length),
        Color::Cyan,
        Style::Bold,
        Color::Red,
        " ".repeat(span.offset() as usize),
        "^".repeat(span.len() as usize),
        Style::Clear
    );

    eprintln!(
        "{}{}{} |{}",
        Color::Cyan,
        Style::Bold,
        " ".repeat(line_length),
        Color::Clear
    );
    eprintln!(
        "{}{}{} |{}",
        Color::Cyan,
        Style::Bold,
        " ".repeat(line_length),
        Color::Clear
    );
}

fn print_multiline_error(snipet: &str, start_line: usize, line_length: usize) {
    for (i, line) in snipet.lines().enumerate() {
        let current_line = start_line + i + 1;
        let current_line_length = usize_length(current_line);
        eprintln!(
            "{}{}{}{}| {}{}",
            Color::Cyan,
            Style::Bold,
            " ".repeat(line_length - current_line_length),
            current_line,
            Color::Clear,
            line,
        );
    }
}

fn usize_length(n: usize) -> usize {
    if n < 10 {
        1
    } else if n < 100 {
        2
    } else if n < 1_000 {
        3
    } else if n < 10_000 {
        4
    } else {
        todo!()
    }
}
