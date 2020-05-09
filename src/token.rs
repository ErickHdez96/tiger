use std::fmt;
use crate::{Span, Symbol};

/// A `Token` is a combination of a [`TokenKind`], which represents what kind of token this is
/// (e.g. Comma, Assign, etc.), and a [`Span`], which contains the offset of where this token
/// starts in the source file, and the length of it.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Token {
    kind: TokenKind,
    span: Span,
}

impl Token {
    /// Create a new token with the given `kind` and `span`.
    ///
    /// For example:
    /// ```
    /// use tiger::{Token, TokenKind, Span, T};
    ///
    /// let token = Token::new(TokenKind::Assign, Span::new(10, 2));
    /// assert_eq!(token.kind(), T![:=]);
    /// assert_eq!(token.span().offset(), 10);
    /// assert_eq!(token.span().len(), 2);
    /// ```
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// Get the [`TokenKind`] that this Token represents.
    pub fn kind(&self) -> TokenKind {
        self.kind
    }

    /// Get the [`Span`] of this token.
    pub fn span(&self) -> Span {
        self.span
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} at offset {} with length {}", self.kind, self.span.offset(), self.span.len())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TokenKind {
    Comma,
    Colon,
    Semicolon,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Period,
    Plus,
    Minus,
    Star,
    Slash,
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    Assign,
    Eof,

    // Keywords
    Array,
    If,
    Then,
    Else,
    While,
    For,
    To,
    Do,
    Let,
    In,
    End,
    Of,
    Break,
    Nil,
    Function,
    Var,
    Type,
    Import,
    Primitive,
    Main,
    Class,
    Extends,
    Method,
    New,

    // A string
    Literal(Symbol),

    Ident(Symbol),

    Number(Symbol),
    Unknown(char),
}

impl From<Symbol> for TokenKind {
    fn from(s: Symbol) -> Self {
        match s.as_str() {
            "array" => TokenKind::Array,
            "if" => TokenKind::If,
            "then" => TokenKind::Then,
            "else" => TokenKind::Else,
            "while" => TokenKind::While,
            "for" => TokenKind::For,
            "to" => TokenKind::To,
            "do" => TokenKind::Do,
            "let" => TokenKind::Let,
            "in" => TokenKind::In,
            "end" => TokenKind::End,
            "of" => TokenKind::Of,
            "break" => TokenKind::Break,
            "nil" => TokenKind::Nil,
            "function" => TokenKind::Function,
            "var" => TokenKind::Var,
            "type" => TokenKind::Type,
            "import" => TokenKind::Import,
            "primitive" => TokenKind::Primitive,
            "_main" => TokenKind::Main,
            "class" => TokenKind::Class,
            "extends" => TokenKind::Extends,
            "method" => TokenKind::Method,
            "new" => TokenKind::New,
            _ => TokenKind::Ident(s),
        }
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use TokenKind::*;

        write!(f, "{}", match self {
            Comma => ",",
            Colon => ":",
            Semicolon => ";",
            LParen => "(",
            RParen => ")",
            LBracket => "[",
            RBracket => "]",
            LBrace => "{",
            RBrace => "}",
            Period => ".",
            Plus => "+",
            Minus => "-",
            Star => "*",
            Slash => "/",
            Eq => "=",
            Neq => "<>",
            Lt => "<",
            Lte => "<=",
            Gt => ">",
            Gte => ">=",
            And => "&",
            Or => "|",
            Assign => ":=",
            Eof => "EOF",
            Array => "array",
            If => "if",
            Then => "then",
            Else => "else",
            While => "while",
            For => "for",
            To => "to",
            Do => "do",
            Let => "let",
            In => "in",
            End => "end",
            Of => "of",
            Break => "break",
            Nil => "nil",
            Function => "function",
            Var => "var",
            Type => "type",
            Import => "import",
            Primitive => "primitive",
            Main => "_main",
            Class => "class",
            Extends => "extends",
            Method => "method",
            New => "new",
            Number(s) | Ident(s) => s.as_str(),
            Literal(s) => return write!(f, "\"{}\"", s.as_str()),
            Unknown(c) => return write!(f, "{}", c),
        })
    }
}

/// Helper to generate a [`TokenKind`] from an easier to read Token representation.
///
/// For example:
///
/// ```
/// use tiger::{T, TokenKind};
///
/// assert_eq!(T![,], TokenKind::Comma);
/// assert_eq!(T!['('], TokenKind::LParen);
/// assert_eq!(T![:=], TokenKind::Assign);
/// ```
#[macro_export]
macro_rules! T {
    (,) => { TokenKind::Comma };
    (:) => { TokenKind::Colon };
    (;) => { TokenKind::Semicolon };
    ('(') => { TokenKind::LParen };
    (')') => { TokenKind::RParen };
    ('[') => { TokenKind::LBracket };
    (']') => { TokenKind::RBracket };
    ('{') => { TokenKind::LBrace };
    ('}') => { TokenKind::RBrace };
    (.) => { TokenKind::Period };
    (+) => { TokenKind::Plus };
    (-) => { TokenKind::Minus };
    (*) => { TokenKind::Star };
    (/) => { TokenKind::Slash };
    (=) => { TokenKind::Eq };
    (<>) => { TokenKind::Neq };
    (<) => { TokenKind::Lt };
    (<=) => { TokenKind::Lte };
    (>) => { TokenKind::Gt };
    (>=) => { TokenKind::Gte };
    (&) => { TokenKind::And };
    (|) => { TokenKind::Or };
    (:=) => { TokenKind::Assign };
    (eof) => { TokenKind::Eof };
    (array) => { TokenKind::Array };
    (if) => { TokenKind::If };
    (then) => { TokenKind::Then };
    (else) => { TokenKind::Else };
    (while) => { TokenKind::While };
    (for) => { TokenKind::For };
    (to) => { TokenKind::To };
    (do) => { TokenKind::Do };
    (let) => { TokenKind::Let };
    (in) => { TokenKind::In };
    (end) => { TokenKind::End };
    (of) => { TokenKind::Of };
    (break) => { TokenKind::Break };
    (nil) => { TokenKind::Nil };
    (function) => { TokenKind::Function };
    (var) => { TokenKind::Var };
    (type) => { TokenKind::Type };
    (import) => { TokenKind::Import };
    (primitive) => { TokenKind::Primitive };
    (_main) => { TokenKind::Main };
    (class) => { TokenKind::Class };
    (extends) => { TokenKind::Extends };
    (method) => { TokenKind::Method };
    (new) => { TokenKind::New };
    (n $symbol:expr) => { TokenKind::Number($symbol) };
    (i $symbol:expr) => { TokenKind::Ident($symbol) };
    (l $symbol:expr) => { TokenKind::Literal($symbol) };
}
