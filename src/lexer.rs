//! Lexer module for the Tiger language.

use crate::{CompilerError, Span, Symbol, Token, TokenKind, T};
use std::iter::Iterator;
use std::str::Chars;

/// Converts a string into a list of [`Token`]s.
///
/// For example:
/// ```
/// use tiger::{Token, TokenKind, Span, tokenize};
///
/// let (tokens, errors) = tokenize(",.");
/// assert!(errors.is_empty());
///
/// let mut tokens = tokens.into_iter();
/// assert_eq!(tokens.next(), Some(Token::new(TokenKind::Comma, Span::new(0, 1))));
/// assert_eq!(tokens.next(), Some(Token::new(TokenKind::Period, Span::new(1, 1))));
/// assert_eq!(tokens.next(), Some(Token::new(TokenKind::Eof, Span::new(2, 1))));
/// assert_eq!(tokens.next(), None);
/// ```
pub fn tokenize(input: &str) -> (Vec<Token>, Vec<LexerError>) {
    if input.len() >= u32::MAX as usize {
        panic!("Files larger than 4GiB are not supported.");
    }
    let mut lexer = Lexer::new(input);
    let mut tokens = vec![];

    while let Some(t) = lexer.next() {
        tokens.push(t);
    }

    (tokens, lexer.into_errors())
}

struct Lexer<'a> {
    /// An iterator over the characters of the input.
    chars: Chars<'a>,
    /// The amount of bytes consumed so far. It is bytes and not characters, to support Unicode.
    pos: u32,
    /// How deep into nested comments we currently are.
    comment_depth: usize,
    errors: Vec<LexerError>,
    /// When the Lexer reaches the end of file, it should return an [`TokenKind`]::Eof first, then
    /// None.
    has_returned_eof: bool,
    /// Used while consuming a string, to determine if a `"` is terminating the string, or it was
    /// escaped with `\`.
    previous_char: char,
    current_char: char,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars(),
            pos: 0,
            comment_depth: 0,
            errors: vec![],
            has_returned_eof: false,
            previous_char: '\0',
            current_char: '\0',
        }
    }

    pub fn into_errors(self) -> Vec<LexerError> {
        self.errors
    }

    /// Check if the lexer has consumed all input.
    fn at_eof(&self) -> bool {
        self.chars.clone().next().is_none()
    }

    /// Return the next character from the input and advance the pointer.
    /// To check if '\0' is the NUL byte or the end of the input, use `self.at_eof`.
    fn consume(&mut self) -> char {
        self.previous_char = self.current_char;
        let c = self.chars.next().unwrap_or('\0');
        self.current_char = c;
        self.pos += c.len_utf8() as u32;
        c
    }

    /// Return the next character from the input without advancing the pointer.
    /// To check if '\0' is the NUL byte or the end of the input, use `self.at_eof`.
    fn peek(&self) -> char {
        self.nth_char(0)
    }

    /// Return the `n`th character from the input, without advancing the pointer.
    /// To check if '\0' is the NUL byte or the end of the input, use `self.at_eof`.
    fn nth_char(&self, n: usize) -> char {
        self.chars.clone().nth(n).unwrap_or('\0')
    }

    /// Skip all whitespace and comments.
    /// Once this function returns, the next character should be a non-whitespace.
    fn skip_whitespace_and_comments(&mut self) {
        let mut start = 0;
        loop {
            match self.peek() {
                ' ' | '\t' | '\n' | '\r' => {
                    self.consume();
                }
                '/' if self.nth_char(1) == '*' => {
                    if self.comment_depth == 0 {
                        start = self.pos;
                    }
                    self.consume();
                    self.consume();
                    self.comment_depth += 1;
                }
                '*' if self.nth_char(1) == '/' => {
                    self.consume();
                    self.consume();
                    self.comment_depth -= 1;
                }
                '\0' if self.comment_depth > 0 => {
                    let span = Span::new(start, self.pos);
                    self.errors.push(LexerError::new(
                        match self.comment_depth {
                            1 => "There is one unclosed comment.".to_string(),
                            d => format!("There are {} unclosed nested comments.", d),
                        },
                        span,
                        span,
                    ));
                    self.comment_depth = 0;
                    break;
                }
                _ if self.comment_depth == 0 => break,
                _ => {
                    self.consume();
                }
            }
        }
    }

    /// With the first character pointing to a number, consume the whole number and return a
    /// [`TokenKind`]::Number with the number as a string interned.
    /// The `self.chars` iterator is left right after the last digit.
    fn eat_number(&mut self) -> TokenKind {
        let chars = self.chars.clone();
        let start = self.pos;

        while self.peek().is_ascii_digit() {
            self.consume();
        }

        TokenKind::Number(Symbol::intern(
            chars.take((self.pos - start) as usize).collect::<String>(),
        ))
    }

    /// With the first [`char`] pointing to a valid start of an identifier, consume the whole
    /// identifier and return a [`TokenKind`]::Ident or the specific Keyword.
    /// The `self.chars` iterator is left right after the last digit.
    fn eat_identifier(&mut self) -> TokenKind {
        let chars = self.chars.clone();
        let start = self.pos;

        while is_ident_char(self.peek(), false) {
            self.consume();
        }

        TokenKind::from(Symbol::intern(
            chars.take((self.pos - start) as usize).collect::<String>(),
        ))
    }

    /// With the first [`char`] pointing to the start of the string (`"`), consume the whole
    /// string (until the next not-escaped `"`). A String may span multiple lines.
    fn eat_string(&mut self) -> TokenKind {
        self.consume();
        let start = self.pos;
        let chars = self.chars.clone();

        // Consume all the characters while not at the end of a string and not at the end of the
        // string or the end of the input.
        while self.peek() != '"' && !self.at_eof() {
            // If the next two characters are a escaped `"`, consume both so it does not end the
            // string.
            if self.peek() == '\\' && self.nth_char(1) == '"' {
                self.consume();
            }
            self.consume();
        }

        let mut literal = chars.take((self.pos - start) as usize).collect::<String>();

        if self.at_eof() {
            self.errors.push(LexerError::new(
                "Unexpected EOF while reading string.",
                Span::new(start - 1, self.pos),
                Span::new(self.pos - 1, self.pos),
            ));
        } else {
            let (unescaped, errors) = unescape_string(literal, start as usize);
            self.errors.extend(errors);
            literal = unescaped;
        }

        // Consume the last `"`.
        self.consume();

        TokenKind::Literal(Symbol::intern(literal))
    }
}

/// Takes a &[`str`] without the outer quotes (`"`), and returns a [`String`] with all escaped
/// sequences replaced, along with with any errors found.
///
/// `start` should be the position of the first character inside the string.
fn unescape_string(literal: String, start: usize) -> (String, Vec<LexerError>) {
    let mut errors = vec![];
    if !literal.contains('\\') {
        return (literal, errors);
    }

    let mut out = String::with_capacity(literal.len());
    let mut chars = literal.chars();
    let mut literal_pos = 0;
    // -1 because `start` is right after the double quote `"`.
    // +2 due to the two enclosing `"`.
    let string_span = Span::new(start as u32 - 1, literal.len() as u32 + 2);

    while let Some(current_char) = chars.next() {
        match current_char {
            '\\' => {
                let (parsed_char, consumed_chars) =
                    parse_escape_char(&mut chars, string_span, start + literal_pos);
                match parsed_char {
                    Ok(c) => out.push(c),
                    Err(e) => errors.push(e),
                }
                // Consumed characters plus `\`
                literal_pos += consumed_chars as usize + 1;
            }
            c => {
                literal_pos += c.len_utf8();
                out.push(c);
            }
        }
    }

    (out, errors)
}

/// Parses a sequence following a backslash (`\`), returning the parsed character if the escape
/// sequence is valid, or an error otherwise, along with the amount of characters consumed from the
/// Chars iterator.
fn parse_escape_char(
    chars: &mut Chars,
    str_span: Span,
    initial_pos: usize,
) -> (Result<char, LexerError>, u8) {
    macro_rules! c {
        (eof) => { c!(eof 0) };
        // Number parsed is greater than 127, the last valid ASCII character.
        (invalid_sequence) => {
            (
                Err(
                    LexerError::new(
                        "Numeral escape sequence not a valid ASCII character",
                        str_span,
                        Span::new(initial_pos as u32, 4)
                    ),
                ),
                3
            )
        };
        ($c:expr) => { (Ok($c), 1) };
        ($c:expr, $len:expr) => { (Ok($c), $len) };
        // Invalid character following the `\`.
        (unexpected $c:expr) => {
            (
                Err(
                    LexerError::new(
                        format!("Unexpected escape sequence: {}", $c),
                        str_span,
                        // The + 1 is due to the previous `\`.
                        Span::new(initial_pos as u32, $c.len_utf8() as u32 + 1)
                    ),
                ),
                $c.len_utf8() as u8
            )
        };
        // While parsing the 3 numbers of an octal escape sequence, a non-digit character was
        // found.
        (unexpected_octal $c:expr, $current_length:expr) => {
            (
                Err(
                    LexerError::new(
                        format!("Unexpected character while reading octal escape sequence: {}", $c),
                        str_span,
                        Span::new(initial_pos as u32, $current_length + $c.len_utf8() as u32 + 1)
                    ),
                ),
                $current_length + $c.len_utf8() as u8
            )
        };
        // While parsing the 2 hex-numbers of a hexadecimal escape sequence, an invalid
        // hex-symbol was found.
        (unexpected_hex $c:expr, $current_length:expr) => {
            (
                Err(
                    LexerError::new(
                        format!("Unexpected character while reading hex escape sequence: {}", $c),
                        str_span,
                        Span::new(initial_pos as u32, $current_length + $c.len_utf8() as u32 + 1)
                    ),
                ),
                $current_length + $c.len_utf8() as u8
            )
        };
        // Either the string ends with a `\`, or while trying to read the 3 numbers of a numeral
        // escape sequence, we reached the end of the string.
        (eof $len:expr) => {
            (
                Err(
                    LexerError::new(
                        "Unexpected end of string while parsing escape sequence",
                        str_span,
                        Span::new(initial_pos as u32, $len + 1)
                    ),
                ),
                $len
            )
        };
    }

    match chars.next() {
        Some('n') => c!('\n'),
        Some('r') => c!('\r'),
        Some('t') => c!('\t'),
        Some('\\') => c!('\\'),
        Some('"') => c!('"'),
        Some('a') => c!(7 as char),
        Some('b') => c!(8 as char),
        Some('v') => c!(11 as char),
        Some('f') => c!(12 as char),
        Some(c) if c.is_ascii_digit() => match chars.next() {
            Some(c2) if c2.is_ascii_digit() => match chars.next() {
                Some(c3) if c3.is_ascii_digit() => {
                    let sequence = vec![c, c2, c3].into_iter().collect::<String>();
                    match u8::from_str_radix(&sequence, 8) {
                        Ok(n) if n <= 127 => c!(n as char, 3),
                        _ => c!(invalid_sequence),
                    }
                }
                Some(c3) => c!(unexpected_octal c3, 2),
                None => c!(eof 2),
            },
            Some(c2) => c!(unexpected_octal c2, 1),
            None => c!(eof 1),
        },
        Some('x') => match chars.next() {
            Some(c1) if c1.is_ascii_hexdigit() => match chars.next() {
                Some(c2) if c2.is_ascii_hexdigit() => {
                    let sequence = vec![c1, c2].into_iter().collect::<String>();
                    match u8::from_str_radix(&sequence, 16) {
                        Ok(n) if n <= 127 => c!(n as char, 3),
                        _ => c!(invalid_sequence),
                    }
                }
                Some(c2) => c!(unexpected_hex c2, 2),
                None => c!(eof 2),
            },
            Some(c1) => c!(unexpected_hex c1, 1),
            None => c!(eof 1),
        },
        Some(c) => c!(unexpected c),
        None => c!(eof),
    }
}

/// Consume the current char and return the TokenKind.
/// It can receive a possible next token to match TokenKinds with length > 1.
///
/// For example:
///
/// ```no-run
/// kind_consume!(self, ,) // Consumes the current token and returns TokenKind::Comma
/// // Consumes the current token, if the next is `>`, consumes that as well and returns
/// TokenKind::Neq, otherwise, returns TokenKind::Lt
/// kind_consume!(self, <, ('>', T![<>]))
/// ```
macro_rules! kind_consume {
    ($self:expr, $basekind:tt, $(($peek:expr, $kind:expr)),+ $(,)?) => {{
        $self.consume();
        match $self.peek() {
            $($peek => kind_consume!($self, $kind, expr),)+
            _ => T![$basekind],
        }
    }};
    ($self:expr, $kind:tt) => {{
        $self.consume();
        T![$kind]
    }};
    ($self:expr, $kind:expr, expr) => {{
        $self.consume();
        $kind
    }};
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        use TokenKind as K;
        if self.at_eof() && self.has_returned_eof {
            return None;
        }
        self.skip_whitespace_and_comments();

        let start = self.pos;
        let kind = match self.peek() {
            ',' => kind_consume!(self, ,),
            ':' => kind_consume!(self, :, ('=', T![:=])),
            ';' => kind_consume!(self, ;),
            '(' => kind_consume!(self, '('),
            ')' => kind_consume!(self, ')'),
            '[' => kind_consume!(self, '['),
            ']' => kind_consume!(self, ']'),
            '{' => kind_consume!(self, '{'),
            '}' => kind_consume!(self, '}'),
            '.' => kind_consume!(self, .),
            '+' => kind_consume!(self, +),
            '-' => kind_consume!(self, -),
            '*' => kind_consume!(self, *),
            '/' => kind_consume!(self, /),
            '=' => kind_consume!(self, =),
            '<' => kind_consume!(self, <, ('>', T![<>]), ('=', T![<=])),
            '>' => kind_consume!(self, >, ('=', T![>=])),
            '&' => kind_consume!(self, &),
            '|' => kind_consume!(self, |),
            '\0' => {
                if self.at_eof() {
                    self.has_returned_eof = true;
                }
                kind_consume!(self, eof)
            }
            '"' => self.eat_string(),
            c if c.is_ascii_digit() => self.eat_number(),
            c if is_ident_char(c, true) => self.eat_identifier(),
            // Only _main is allowed to start with a `_`.
            '_' => {
                let mut kind = K::Unknown('_');
                let mut chars = self.chars.clone();
                // Skip '_'
                chars.next();

                if let Some('m') = chars.next() {
                    if let Some('a') = chars.next() {
                        if let Some('i') = chars.next() {
                            if let Some('n') = chars.next() {
                                self.consume(); // m
                                self.consume(); // a
                                self.consume(); // i
                                self.consume(); // n
                                kind = T![_main];
                            }
                        }
                    }
                }

                self.consume();
                kind
            }
            c => K::Unknown(c),
        };

        Some(Token::new(kind, Span::new(start, self.pos - start)))
    }
}

fn is_ident_char(c: char, is_first_char: bool) -> bool {
    (c >= 'a' && c <= 'z')
        || (c >= 'A' && c <= 'Z')
        || ((c >= '0' && c <= '9') && !is_first_char)
        || (c == '_' && !is_first_char)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexerError {
    msg: String,
    snippet_span: Span,
    error_span: Span,
}

impl LexerError {
    pub fn new(msg: impl Into<String>, snippet_span: Span, error_span: Span) -> Self {
        Self {
            msg: msg.into(),
            snippet_span,
            error_span,
        }
    }

    pub fn into_parts(self) -> (String, Span, Span) {
        (self.msg, self.snippet_span, self.error_span)
    }
}

impl CompilerError for LexerError {
    fn msg(&self) -> &str {
        &self.msg
    }

    fn snippet_span(&self) -> Span {
        self.snippet_span
    }

    fn error_span(&self) -> Span {
        self.snippet_span
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! tok {
        ($kind:expr, $base:expr, $len:expr) => {
            Token::new($kind, Span::new($base, $len))
        };
    }

    #[test]
    fn test_symbols() {
        let input = ", : ; ( ) [ ] { } . + - * / = <> < <= > >= & | :=";
        let (tokens, errors) = tokenize(&input);
        assert!(errors.is_empty());

        let expected = vec![
            tok!(T![,], 0, 1),
            tok!(T![:], 2, 1),
            tok!(T![;], 4, 1),
            tok!(T!['('], 6, 1),
            tok!(T![')'], 8, 1),
            tok!(T!['['], 10, 1),
            tok!(T![']'], 12, 1),
            tok!(T!['{'], 14, 1),
            tok!(T!['}'], 16, 1),
            tok!(T![.], 18, 1),
            tok!(T![+], 20, 1),
            tok!(T![-], 22, 1),
            tok!(T![*], 24, 1),
            tok!(T![/], 26, 1),
            tok!(T![=], 28, 1),
            tok!(T![<>], 30, 2),
            tok!(T![<], 33, 1),
            tok!(T![<=], 35, 2),
            tok!(T![>], 38, 1),
            tok!(T![>=], 40, 2),
            tok!(T![&], 43, 1),
            tok!(T![|], 45, 1),
            tok!(T![:=], 47, 2),
            tok!(T![eof], 49, 1),
        ];

        assert_eq!(expected.len(), tokens.len());
        for (token, expected) in tokens.into_iter().zip(expected.into_iter()) {
            assert_eq!(token, expected);
        }
    }

    #[test]
    fn test_numbers() {
        let input = "0 500 1234567890";
        let (tokens, errors) = tokenize(&input);
        assert!(errors.is_empty());

        let expected = vec![
            tok!(T![n Symbol::intern("0")], 0, 1),
            tok!(T![n Symbol::intern("500")], 2, 3),
            tok!(T![n Symbol::intern("1234567890")], 6, 10),
            tok!(T![eof], 16, 1),
        ];

        assert_eq!(expected.len(), tokens.len());
        for (token, expected) in tokens.into_iter().zip(expected.into_iter()) {
            assert_eq!(token, expected);
        }
    }

    #[test]
    fn test_keywords() {
        let input = "array if then else while for to do let in end of break nil function var type import primitive _main class extends method new";
        let (tokens, errors) = tokenize(&input);
        assert!(errors.is_empty());

        let expected = vec![
            tok!(T![array], 0, 5),
            tok!(T![if], 6, 2),
            tok!(T![then], 9, 4),
            tok!(T![else], 14, 4),
            tok!(T![while], 19, 5),
            tok!(T![for], 25, 3),
            tok!(T![to], 29, 2),
            tok!(T![do], 32, 2),
            tok!(T![let], 35, 3),
            tok!(T![in], 39, 2),
            tok!(T![end], 42, 3),
            tok!(T![of], 46, 2),
            tok!(T![break], 49, 5),
            tok!(T![nil], 55, 3),
            tok!(T![function], 59, 8),
            tok!(T![var], 68, 3),
            tok!(T![type], 72, 4),
            tok!(T![import], 77, 6),
            tok!(T![primitive], 84, 9),
            tok!(T![_main], 94, 5),
            tok!(T![class], 100, 5),
            tok!(T![extends], 106, 7),
            tok!(T![method], 114, 6),
            tok!(T![new], 121, 3),
            tok!(T![eof], 124, 1),
        ];

        assert_eq!(tokens.len(), expected.len());
        for (token, expected) in tokens.into_iter().zip(expected.into_iter()) {
            assert_eq!(token, expected);
        }
    }

    #[test]
    fn test_comments() {
        let input = "/* Single line coment. */";
        let (tokens, errors) = tokenize(&input);
        assert!(errors.is_empty());
        assert_eq!(tokens.len(), 1, "Unexpected tokens returned");
        assert_eq!(
            tokens.into_iter().next().unwrap(),
            tok!(T![eof], input.len() as u32, 1)
        );

        let input = "/* Unterminated comment";
        let (tokens, errors) = tokenize(&input);
        assert_eq!(errors.len(), 1, "Expected 1 error");
        assert_eq!(tokens.len(), 1, "Unexpected tokens returned");

        assert_eq!(
            tokens.into_iter().next().unwrap(),
            tok!(T![eof], input.len() as u32, 1)
        );

        assert_eq!(
            errors.into_iter().next().unwrap(),
            LexerError::new(
                "There is one unclosed comment.".to_string(),
                Span::new(0, input.len() as u32),
                Span::new(0, input.len() as u32),
            ),
        );
    }

    #[test]
    fn test_nested_comments() {
        let input = r"/*
        Depth 1
        /*
        Depth 2
        /*
        Depth 3
        /*
        Depth 4
        */
        Depth 3
        */
        Depth 2
        */
        Depth 1
        */";
        let (tokens, errors) = tokenize(&input);
        assert!(errors.is_empty());
        assert_eq!(tokens.len(), 1, "Unexpected tokens returned");
        assert_eq!(
            tokens.into_iter().next().unwrap(),
            tok!(T![eof], input.len() as u32, 1)
        );

        let input = r"/*
        Depth 1
        /*
        Depth 2
        /*
        Depth 3
        /*
        Depth 4
        */
        Depth 3
        */
        Depth 2

        Depth 1
        ";
        let (tokens, errors) = tokenize(&input);
        assert_eq!(errors.len(), 1, "Expected 1 error");
        assert_eq!(tokens.len(), 1, "Unexpected tokens returned");
        assert_eq!(
            tokens.into_iter().next().unwrap(),
            tok!(T![eof], input.len() as u32, 1)
        );

        assert_eq!(
            errors.into_iter().next().unwrap(),
            LexerError::new(
                "There are 2 unclosed nested comments.".to_string(),
                Span::new(0, input.len() as u32),
                Span::new(0, input.len() as u32)
            ),
        );
    }

    #[test]
    fn test_strings() {
        let input = r"Normal string".to_string();
        let (escaped_input, errors) = unescape_string(input.clone(), 1);
        assert!(errors.is_empty());
        assert_eq!(&input, &escaped_input);
    }

    #[test]
    fn test_basic_escaping() {
        let input = r#"\a\b\f\n\r\t\v\\\""#.to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = vec![
            7 as char, 8 as char, 12 as char, '\n', '\r', '\t', 11 as char, '\\', '"',
        ]
        .into_iter()
        .collect::<String>();
        assert!(errors.is_empty());
        assert_eq!(escaped_input, expected_output);
    }

    #[test]
    fn test_octal_numeral_escaping() {
        let input = r"\000 \177 \141".to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = vec![0o000 as char, ' ', 0o177 as char, ' ', 0o141 as char]
            .into_iter()
            .collect::<String>();
        assert!(errors.is_empty());
        assert_eq!(escaped_input, expected_output);
    }

    #[test]
    fn test_hex_numeral_escaping() {
        let input = r"\x00 \x1F \x61".to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = vec![0x00 as char, ' ', 0x1F as char, ' ', 0x61 as char]
            .into_iter()
            .collect::<String>();
        assert!(errors.is_empty());
        assert_eq!(escaped_input, expected_output);
    }

    #[test]
    fn test_single_errors_while_escaping_strings() {
        let input = r"\".to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = "".to_string();
        assert_eq!(escaped_input, expected_output);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors.into_iter().next().unwrap(),
            LexerError::new(
                "Unexpected end of string while parsing escape sequence",
                Span::new(0, 3),
                Span::new(1, 1)
            ),
        );

        let input = r"\0".to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = "".to_string();
        assert_eq!(escaped_input, expected_output);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors.into_iter().next().unwrap(),
            LexerError::new(
                "Unexpected end of string while parsing escape sequence",
                Span::new(0, 4),
                Span::new(1, 2)
            ),
        );

        let input = r"\00".to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = "".to_string();
        assert_eq!(escaped_input, expected_output);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors.into_iter().next().unwrap(),
            LexerError::new(
                "Unexpected end of string while parsing escape sequence",
                Span::new(0, 5),
                Span::new(1, 3)
            ),
        );

        let input = r"\200".to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = "".to_string();
        assert_eq!(escaped_input, expected_output);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors.into_iter().next().unwrap(),
            LexerError::new(
                "Numeral escape sequence not a valid ASCII character",
                Span::new(0, 6),
                Span::new(1, 4)
            ),
        );

        let input = r"\00ñ".to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = "".to_string();
        assert_eq!(escaped_input, expected_output);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors.into_iter().next().unwrap(),
            LexerError::new(
                "Unexpected character while reading octal escape sequence: ñ",
                Span::new(0, 7),
                Span::new(1, 5)
            ),
        );

        let input = r"\xñ".to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = "".to_string();
        assert_eq!(escaped_input, expected_output);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors.into_iter().next().unwrap(),
            LexerError::new(
                "Unexpected character while reading hex escape sequence: ñ",
                Span::new(0, 6),
                Span::new(1, 4)
            ),
        );

        let input = r"\xFñ".to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = "".to_string();
        assert_eq!(escaped_input, expected_output);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors.into_iter().next().unwrap(),
            LexerError::new(
                "Unexpected character while reading hex escape sequence: ñ",
                Span::new(0, 7),
                Span::new(1, 5)
            ),
        );

        let input = r"\xFF".to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = "".to_string();
        assert_eq!(escaped_input, expected_output);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors.into_iter().next().unwrap(),
            LexerError::new(
                "Numeral escape sequence not a valid ASCII character",
                Span::new(0, 6),
                Span::new(1, 4)
            ),
        );

        let input = r"\z".to_string();
        let (escaped_input, errors) = unescape_string(input, 1);
        let expected_output = "".to_string();
        assert_eq!(escaped_input, expected_output);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors.into_iter().next().unwrap(),
            LexerError::new(
                "Unexpected escape sequence: z",
                Span::new(0, 4),
                Span::new(1, 2)
            ),
        );
    }

    #[test]
    fn test_multiple_string_escaping_errors() {
        let input = r"\o \200 \2ñ \xFñ \xFF \".to_string();
        let input_span = Span::new(4, input.len() as u32 + 2);
        let (escaped_input, errors) = unescape_string(input, 5);
        let expected_output = "     ".to_string();
        assert_eq!(escaped_input, expected_output);
        assert_eq!(errors.len(), 6);
        let mut errors = errors.into_iter();

        assert_eq!(
            errors.next().unwrap(),
            LexerError::new("Unexpected escape sequence: o", input_span, Span::new(5, 2)),
        );

        assert_eq!(
            errors.next().unwrap(),
            LexerError::new(
                "Numeral escape sequence not a valid ASCII character",
                input_span,
                Span::new(8, 4)
            ),
        );

        assert_eq!(
            errors.next().unwrap(),
            LexerError::new(
                "Unexpected character while reading octal escape sequence: ñ",
                input_span,
                Span::new(13, 4)
            ),
        );

        assert_eq!(
            errors.next().unwrap(),
            LexerError::new(
                "Unexpected character while reading hex escape sequence: ñ",
                input_span,
                Span::new(18, 5)
            ),
        );

        assert_eq!(
            errors.next().unwrap(),
            LexerError::new(
                "Numeral escape sequence not a valid ASCII character",
                input_span,
                Span::new(24, 4)
            ),
        );

        assert_eq!(
            errors.next().unwrap(),
            LexerError::new(
                "Unexpected end of string while parsing escape sequence",
                input_span,
                Span::new(29, 1)
            ),
        );
    }
}
