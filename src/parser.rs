mod dec;
mod exp;

use crate::ast::BinOp;
use crate::{CompilerError, Item, Span, Symbol, Token, TokenKind, T};
use std::vec::IntoIter;

pub fn parse(tokens: impl Into<Vec<Token>>) -> (Option<Item>, Vec<ParserError>) {
    let mut parser = Parser::new(tokens);
    (parser.parse(), parser.into_errors())
}

#[derive(Debug)]
struct Parser {
    tokens: IntoIter<Token>,
    /// The start of the current item being parsed.
    start: Span,
    /// Whether the parser has found an error and is trying to keep building the current node. Any
    /// error found during that time should not be reported.
    synchronizing: bool,
    ast_pos: AstPos,
    errors: Vec<ParserError>,
}

impl Parser {
    pub fn new(tokens: impl Into<Vec<Token>>) -> Self {
        let tokens = tokens.into();
        assert!(!tokens.is_empty(), "Cannot parse an empty list of tokens");
        Self {
            tokens: tokens.into_iter(),
            start: Span::new(0, 0),
            synchronizing: false,
            ast_pos: AstPos::Root,
            errors: vec![],
        }
    }

    pub fn parse(&mut self) -> Option<Item> {
        if self.peek().kind().can_start_declaration() {
            self.start = self.peek().span();
            Some(Item::Decs(self.parse_decs()?))
        } else if self.peek().kind().can_start_expression() {
            self.start = self.peek().span();
            Some(Item::Exp(Box::new(self.parse_exp(0)?)))
        } else {
            None
        }
    }

    pub fn into_errors(self) -> Vec<ParserError> {
        self.errors
    }

    /// Skip all the tokens that don't resolve to `true` with the given `test` function. Or once a
    /// token has been found that can help synchronize during the current position in the ast.
    fn synchronize<F: Fn(TokenKind) -> bool>(&mut self, test: F) {
        self.synchronizing = true;
        loop {
            let kind = self.peek().kind();
            if test(kind) || self.ast_pos.ends_synchronization(kind) || kind == T![eof] {
                return;
            }
            self.advance();
        }
    }

    /// If the current token is of the expected kind, consume and return it, otherwise add an error
    /// and return None.
    fn eat(&mut self, expected_kind: TokenKind) -> Option<Token> {
        if self.peek().kind() == expected_kind {
            Some(self.advance())
        } else {
            self.unexpected_token(format!("`{}`", expected_kind));
            None
        }
    }

    /// Similar to `self.eat`. Except that if the current token does not match the expected one,
    /// but `sync(self.peek())` evaluates to true, outputs an error and returns the current token
    /// without consuming it.
    fn eat_or_try_synchronize<F: Fn(TokenKind) -> bool>(
        &mut self,
        expected_kind: TokenKind,
        ast_pos: AstPos,
        sync: F,
    ) -> Option<Token> {
        self.ast_pos = ast_pos;
        self.synchronizing = false;
        if self.peek().kind() == expected_kind {
            Some(self.advance())
        } else if sync(self.peek().kind()) {
            self.unexpected_token(format!("`{}`", expected_kind));
            Some(self.peek())
        } else {
            self.unexpected_token(format!("`{}`", expected_kind));
            None
        }
    }

    fn eat_identifier(&mut self) -> Option<(Symbol, Span)> {
        match self.peek().kind() {
            TokenKind::Ident(s) => {
                let span = self.advance().span();
                Some((s, span))
            }
            _ => {
                self.unexpected_token("an identifier");
                None
            }
        }
    }

    fn eat_string(&mut self) -> Option<(Symbol, Span)> {
        match self.peek().kind() {
            TokenKind::Literal(s) => {
                let span = self.advance().span();
                Some((s, span))
            }
            _ => {
                self.unexpected_token("a string");
                None
            }
        }
    }

    /// The parser has found an unexpected token.
    fn unexpected_token(&mut self, msg: impl AsRef<str>) {
        if self.synchronizing {
            return;
        }
        let token = self.peek();

        self.errors.push(ParserError::new(
            format!(
                "Expected {}, found `{}`",
                msg.as_ref(),
                token.kind().kind_name()
            ),
            self.start.extend(token.span()),
            token.span(),
        ))
    }

    /// Eats the next token if it is a binary operator with a higher precedence than `precedence`.
    fn eat_op_with_precedence(&mut self, precedence: usize) -> Option<(BinOp, Span)> {
        let op = match self.peek().kind() {
            TokenKind::Plus => BinOp::Plus,
            TokenKind::Minus => BinOp::Minus,
            TokenKind::Star => BinOp::Times,
            TokenKind::Slash => BinOp::Div,
            TokenKind::Eq => BinOp::Eq,
            TokenKind::Neq => BinOp::Neq,
            TokenKind::Gt => BinOp::Gt,
            TokenKind::Lt => BinOp::Lt,
            TokenKind::Gte => BinOp::Gte,
            TokenKind::Lte => BinOp::Lte,
            TokenKind::And => BinOp::And,
            TokenKind::Or => BinOp::Or,
            _ => return None,
        };

        if precedence < op.precedence() {
            let span = self.advance().span();
            Some((op, span))
        } else {
            None
        }
    }

    fn advance(&mut self) -> Token {
        self.tokens.next().unwrap_or_else(Token::dummy)
    }

    fn peek(&self) -> Token {
        self.nth_token(0)
    }

    fn nth_token(&self, n: usize) -> Token {
        self.tokens.clone().nth(n).unwrap_or_else(Token::dummy)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ParserError {
    msg: String,
    snippet_span: Span,
    error_span: Span,
}

impl ParserError {
    pub fn new(msg: impl Into<String>, snippet_span: Span, error_span: Span) -> Self {
        Self {
            msg: msg.into(),
            snippet_span,
            error_span,
        }
    }
}

impl CompilerError for ParserError {
    fn msg(&self) -> &str {
        &self.msg
    }

    fn snippet_span(&self) -> Span {
        self.snippet_span
    }

    fn error_span(&self) -> Span {
        self.error_span
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum AstPos {
    /// Root level.
    Root,
    /// Let expression between `let` and `in`.
    Let,
    /// Let expression between `in` and `end`.
    LetIn,

    /// For expression after parsing `for`.
    For,
    /// For expression after parsing `:=`.
    ForAssign,
    /// For expression after parsing `to`.
    ForTo,
    /// For expression after parsing `do`.
    ForDo,
}

impl AstPos {
    /// When synchronizing the parser, whether we have reached a token that can help the parser to
    /// keep parsing.
    pub fn ends_synchronization(self, kind: TokenKind) -> bool {
        use AstPos::*;

        match self {
            Root => kind.is_initial_token(),
            Let => kind == T![in] || kind == T![end],
            LetIn => kind == T![end],
            For => kind == T![:=] || kind == T![to] || kind == T![do],
            ForAssign => kind == T![to] || kind == T![do],
            ForTo => kind == T![do],
            ForDo => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tokenize;

    macro_rules! E {
        ($msg:expr, ($offset1:expr, $length1:expr), ($offset2:expr, $length2:expr)) => {
            ParserError::new(
                $msg,
                Span::new($offset1 as u32, $length1 as u32),
                Span::new($offset2 as u32, $length2 as u32),
            )
        };
    }

    #[test]
    fn test_import_path_error() {
        let input = "import 3";
        let errors = parse(tokenize(input).0).1;

        assert_eq!(
            errors.into_iter().next().expect("Expected one error"),
            E!("Expected a string, found `int`", (0, input.len()), (7, 1))
        );
    }

    #[test]
    fn test_expression_error() {
        let input = "3 + + 3";
        let errors = parse(tokenize(input).0).1;

        assert_eq!(
            errors.into_iter().next().expect("Expected one error"),
            E!("Expected an expression, found `+`", (0, 5), (4, 1))
        );
    }

    #[test]
    fn test_let_parser_recovery() {
        let input = "let 3 + + 3";
        let mut errors = parse(tokenize(input).0).1.into_iter();

        assert_eq!(
            errors.next().expect("Expected one error"),
            E!("Expected `in`, found `int`", (0, 5), (4, 1))
        );

        assert_eq!(
            errors.next().expect("Expected one error"),
            E!("Expected an expression, found `+`", (0, 9), (8, 1))
        );

        assert_eq!(
            errors.next().expect("Expected one error"),
            E!(
                "Expected `end`, found `<eof>`",
                (0, input.len()),
                (input.len() - 1, 1)
            )
        );
    }

    #[test]
    fn test_for_parser_recovery() {
        let input = "for i 0 to do print(i)";
        let mut errors = parse(tokenize(input).0).1.into_iter();

        assert_eq!(
            errors.next().expect("Expected one error"),
            E!("Expected `:=`, found `int`", (0, 7), (6, 1))
        );

        assert_eq!(
            errors.next().expect("Expected one error"),
            E!("Expected an expression, found `do`", (0, 13), (11, 2))
        );
    }
}
