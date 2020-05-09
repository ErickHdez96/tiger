use std::path::Path;
use std::borrow::Cow;
use std::io;
use std::fs;
use crate::{Span, count_lines};

#[derive(Debug)]
pub struct SourceFile<'a> {
    path: &'a Path,
    content: String,
}

impl<'a> SourceFile<'a> {
    pub fn from_path(path: &'a Path) -> io::Result<Self> {
        let content = fs::read_to_string(path)?;
        Ok(Self {
            path,
            content,
        })
    }

    pub fn input(&self) -> &str {
        &self.content
    }

    pub fn get_snippet(&self, span: Span) -> (&str, usize) {
        let line_start = count_lines(&self.content.as_str()[0..(span.offset() as usize)]);
        let start = span.offset() as usize;
        let end = start + span.len() as usize;
        let snippet = &self.content.as_str()[start..end];
        (snippet, line_start)
    }

    pub fn path(&self) -> Cow<str> {
        self.path.to_string_lossy()
    }
}
