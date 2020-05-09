use std::fmt;

#[derive(Debug, Copy, Clone)]
pub enum Color {
    Red,
    Cyan,
    Clear,
}

impl fmt::Display for Color {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Color::*;

        write!(f, "\x1b[{}m", match self {
            Red => "31",
            Cyan => "36",
            Clear => "0",
        })
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Style {
    Bold,
    Clear,
}

impl fmt::Display for Style {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Style::*;

        write!(f, "\x1b[{}m", match self {
            Bold => "1",
            Clear => "0",
        })
    }
}
