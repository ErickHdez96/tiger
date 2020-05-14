use super::{AstPos, Parser};
use crate::ast::{BinOp, Exp, Identifier, LValue, Member};
use crate::{Span, TokenKind, IK, T};

impl Parser {
    /// Parse an expression with a lower precedence than `precedence`.
    ///
    /// ```ignore
    /// exp ::=
    ///     `nil`                                               ✓
    ///     | integer                                           ✓
    ///     | string                                            ✓
    ///
    ///     # Array and record creations.
    ///     | type-id `[` exp `]` `of` exp                      ✓
    ///     | type-id `{`[ id `=` exp { `,` id `=` exp } ] `}`  ✓
    ///
    ///     # Object creation.
    ///     | `new` type-id                                     ✓
    ///
    ///     # Variables, field, elements of an array.
    ///     | lvalue                                            ✓
    ///
    ///     # Function call.
    ///     | id `(` [ exp { `,` exp }] `)`                     ✓
    ///
    ///     # Method call.
    ///     | lvalue `.` id `(` [ exp { `,` exp }] `)`          ✓
    ///
    ///     # Operations.
    ///     | `-` exp                                           ✓
    ///     | exp op exp                                        ✓
    ///     | `(` exps `)`                                      ✓
    ///
    ///     # Assignment.
    ///     | lvalue `:=` exp                                   ✓
    ///
    ///     # Control structures.                               ✓
    ///     | `if` exp `then` exp [`else` exp]                  ✓
    ///     | `while` exp `do` exp                              ✓
    ///     | `for` id `:=` exp `to` exp `do` exp               ✓
    ///     | `break`                                           ✓
    ///     | `let` decs `in` exps `end`                        ✓
    ///
    /// lvalue ::= id                                           ✓
    ///     | lvalue `.` id                                     ✓
    ///     | lvalue `[` exp `]`                                ✓
    /// exps ::= [ exp { `;` exp } ]                            ✓
    /// ```
    pub(super) fn parse_exp(&mut self, precedence: usize) -> Option<Exp> {
        let start = self.peek().span();
        let mut left = match self.peek().kind() {
            // `nil`
            T![nil] => Some(IK![nil, self.advance().span().offset()]),
            // integer
            TokenKind::Number(s) => {
                let span = self.advance().span();
                Some(IK![int, s, span.offset(), span.len()])
            }
            // string
            TokenKind::Literal(s) => {
                let span = self.advance().span();
                Some(IK![str, s, span.offset(), span.len()])
            }
            // lvalue
            TokenKind::Ident(_) => self.parse_exp_starting_with_id(),
            T![let] => {
                self.ast_pos = AstPos::Let;
                self.parse_let_exp()
            }
            T![if] => self.parse_if_exp(),
            T![while] => self.parse_while_exp(),
            T![for] => self.parse_for_exp(),
            T![break] => {
                let span = self.advance().span();
                Some(IK![break, span.offset()])
            }
            // `-` exp
            T![-] => {
                let start = self.advance().span();
                let exp = self.parse_exp(BinOp::MAX_PRECEDENCE)?;
                let span = start.extend(exp.span());
                Some(IK![-, exp, span.offset(), span.len()])
            }
            // `(` exp `)`
            T!['('] => {
                let mut start = self.advance().span();
                let mut exp = self.parse_exp(BinOp::MIN_PRECEDENCE)?;
                if self.peek().kind() == T![;] {
                    let mut exps = vec![exp];
                    while self.peek().kind() == T![;] {
                        self.advance();
                        let exp = self.parse_exp(0)?;
                        start = start.extend(exp.span());
                        exps.push(exp);
                    }
                    exp = IK![exps, exps, start.offset(), start.len()]
                }
                let end = self.eat(T![')'])?.span();
                exp.set_span(start.extend(end));
                Some(exp)
            }
            T![new] => {
                let start = self.advance().span();
                let (id, end) = self.eat_identifier()?;
                let id = IK![ident, id, end.offset(), end.len()];
                let end = start.extend(end);
                Some(IK![new, id, end.offset(), end.len()])
            }
            _ => {
                // Try to synchronize to a valid expression, but dont report any new errors found.
                self.unexpected_token("an expression");
                self.synchronize(|k| k.can_start_expression());
                if self.peek().kind().can_start_expression() {
                    return self.parse_exp(0);
                }
                None
            }
        }?;

        while let Some((op, op_span)) = self.eat_op_with_precedence(precedence) {
            let right = self.parse_exp(op.precedence())?;
            let end = start.extend(right.span());
            left = IK![op, left, right, end.offset(), end.len(), op_span.offset()];
        }

        Some(left)
    }

    /// Parse a let expression.
    ///
    /// `let` parse_decs `in` parse_exp `end`
    fn parse_let_exp(&mut self) -> Option<Exp> {
        let start = self.advance().span();
        let decs = self.parse_decs()?;
        self.eat_or_try_synchronize(T![in], AstPos::LetIn, |k| k.can_start_expression())?;

        let exprs = self.parse_exps()?;
        let end = self
            .eat_or_try_synchronize(T![end], AstPos::Root, |k| k == T![eof])?
            .span();
        let let_span = start.extend(end);
        Some(IK![let, decs, exprs, let_span.offset(), let_span.len()])
    }

    /// Parse 0 or more expressions separated by a semicolon `;`.
    ///
    /// [ exp { `;` exp } ]
    fn parse_exps(&mut self) -> Option<Vec<Exp>> {
        if !self.peek().kind().can_start_expression() {
            return Some(vec![]);
        }

        let mut exps = vec![self.parse_exp(0)?];
        while self.peek().kind() == T![;] {
            self.advance();
            exps.push(self.parse_exp(0)?);
        }
        Some(exps)
    }

    /// Parse an if expression.
    ///
    /// `if` exp `then` exp [`else` exp]
    fn parse_if_exp(&mut self) -> Option<Exp> {
        let start = self.advance().span();
        let cond = self.parse_exp(0)?;
        self.eat(T![then])?;
        let then = self.parse_exp(0)?;
        let mut end = then.span();
        let else_branch = if self.peek().kind() == T![else] {
            self.advance();
            let else_expr = Box::new(self.parse_exp(0)?);
            end = else_expr.span();
            Some(else_expr)
        } else {
            None
        };

        let if_span = start.extend(end);

        Some(IK![if, cond, then, opt else_branch, if_span.offset(), if_span.len()])
    }

    /// Parse a while expression.
    ///
    /// `while` exp `do` exp
    fn parse_while_exp(&mut self) -> Option<Exp> {
        let start = self.advance().span();
        let cond = self.parse_exp(0)?;
        self.eat(T![do])?;
        let do_exp = self.parse_exp(0)?;
        let while_span = start.extend(do_exp.span());
        Some(IK![
            while,
            cond,
            do_exp,
            while_span.offset(),
            while_span.len()
        ])
    }

    /// Parse a for expression.
    ///
    /// `for` id `:=` exp `to` exp `do` exp
    fn parse_for_exp(&mut self) -> Option<Exp> {
        self.ast_pos = AstPos::For;
        let start = self.advance().span();
        let (id, id_span) = self.eat_identifier()?;
        self.eat_or_try_synchronize(T![:=], AstPos::ForAssign, |k| k.can_start_expression())?;
        let from = self.parse_exp(0)?;
        self.eat_or_try_synchronize(T![to], AstPos::ForTo, |k| k.can_start_expression())?;
        let to = self.parse_exp(0)?;
        self.eat_or_try_synchronize(T![do], AstPos::ForDo, |k| k.can_start_expression())?;
        let do_exp = self.parse_exp(0)?;
        let for_span = start.extend(do_exp.span());
        Some(IK![
            for,
            IK![ident, id, id_span.offset(), id_span.len()],
            from,
            to,
            do_exp,
            for_span.offset(),
            for_span.len()
        ])
    }

    /// Parses an epxression that can start either with an `id` or an `lvalue`.
    ///
    /// exp ::=
    ///     type-id `[` exp `]` `of` exp
    ///     | type-id `{`[ id `=` exp { `,` id `=` exp } ]`}`
    ///     | lvalue
    ///     | id `(` [ exp { `,` exp }] `)`
    ///     | lvalue `.` id `(` [ exp { `,` exp }] `)`
    ///     | lvalue `:=` exp
    ///
    /// lvalue ::= id
    ///     | lvalue `.` id
    ///     | lvalue `[` exp `]`
    ///
    /// type-id ::= id
    fn parse_exp_starting_with_id(&mut self) -> Option<Exp> {
        // The current token is an `Identifier`, take a look at the next token to see how to parse
        // it.
        if self.nth_token(1).kind() == T!['{'] {
            return self.parse_record_creation();
        }
        let lvalue = self.parse_lvalue_exp()?;

        match self.peek().kind() {
            T![:=] => {
                self.advance();
                let exp = self.parse_exp(0)?;
                let span = lvalue.span().extend(exp.span());
                Some(IK![assign, lvalue, exp, span.offset(), span.len()])
            }
            T!['('] => {
                self.advance();
                let exps = self.parse_arguments()?;
                let end = lvalue.span().extend(self.eat(T![')'])?.span());
                Some(IK![fncall, lvalue, exps, end.offset(), end.len()])
            }
            T![of] => {
                self.advance();
                let init = self.parse_exp(0)?;

                match lvalue {
                    LValue::ArrayAccess { lvalue, exp, .. } => match *lvalue {
                        LValue::Identifier(id) => {
                            let end = id.span().extend(init.span());
                            Some(IK![newarray, id, box exp, init, end.offset(), end.len()])
                        }
                        _ => None,
                    },
                    _ => None,
                }
            }
            _ => Some(IK![explvalue, lvalue]),
        }
    }

    fn parse_lvalue_exp(&mut self) -> Option<LValue> {
        let (id, start) = self.eat_identifier()?;
        let mut left = IK![lvalue, IK![ident, id, start.offset(), start.len()]];

        loop {
            match self.peek().kind() {
                T![.] => {
                    self.advance();
                    let (id, span) = self.eat_identifier()?;
                    let id = IK![ident, id, span.offset(), span.len()];
                    let current_span = start.extend(id.span());
                    left = IK![member, left, id, current_span.offset(), current_span.len()];
                }
                T!['['] => {
                    self.advance();
                    let exp = self.parse_exp(0)?;
                    let end = self.eat(T![']'])?.span();
                    let current_span = start.extend(end);
                    left = IK![array, left, exp, current_span.offset(), current_span.len()];
                }
                _ => break,
            }
        }

        Some(left)
    }

    fn parse_arguments(&mut self) -> Option<Vec<Exp>> {
        if self.peek().kind() == T![')'] {
            return Some(vec![]);
        }

        let mut exps = vec![self.parse_exp(0)?];

        while self.peek().kind() == T![,] {
            self.advance();
            exps.push(self.parse_exp(0)?);
        }

        Some(exps)
    }

    fn parse_record_creation(&mut self) -> Option<Exp> {
        let (record_name, start) = self.eat_identifier()?;
        self.eat(T!['{'])?;
        let members = self.parse_record_members()?;
        let end = start.extend(self.eat(T!['}'])?.span());
        Some(IK![
            newrecord,
            IK![ident, record_name, start.offset(), start.len()],
            members,
            end.offset(),
            end.len()
        ])
    }

    fn parse_record_members(&mut self) -> Option<Vec<Member>> {
        if self.peek().kind() == T!['}'] {
            return Some(vec![]);
        }
        let mut members = vec![self.parse_record_member()?];

        while self.peek().kind() == T![,] {
            self.advance();
            members.push(self.parse_record_member()?);
        }

        Some(members)
    }

    fn parse_record_member(&mut self) -> Option<Member> {
        let (id, span) = self.eat_identifier()?;
        self.eat(T![=])?;
        let exp = self.parse_exp(0)?;
        let end = span.extend(exp.span());
        Some(IK![
            newmember,
            IK![ident, id, span.offset(), span.len()],
            exp,
            end.offset(),
            end.len()
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Item;
    use crate::{parse, tokenize, Symbol, IK};

    macro_rules! item {
        ($item:expr) => {
            Item::Exp(Box::new($item))
        };
    }

    #[test]
    fn test_single_value_expr() {
        let input = "nil";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");
        assert_eq!(item, item!(IK!(nil, 0)));

        let input = "3";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");
        assert_eq!(item, item!(IK!(int, Symbol::intern("3"), 0, 1)));

        let input = r#""Hello, world!""#;
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");
        assert_eq!(
            item,
            item!(IK!(str, Symbol::intern("Hello, world!"), 0, input.len()))
        );
    }

    #[test]
    fn test_let_expr() {
        let input = "let in nil end";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");
        assert_eq!(
            item,
            item!(IK!(let, vec![], vec![IK![nil, 7]], 0, input.len()))
        );
    }

    #[test]
    fn test_if_expr() {
        let input = "if 1 then ident";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let cond = IK![int, Symbol::intern("1"), 3, 1];
        let then = IK![
            explvalue,
            IK![lvalue, IK![ident, Symbol::intern("ident"), 10, 5]]
        ];

        assert_eq!(item, item!(IK!(if, cond, then, 0, input.len())),);

        let input = r#"if 1 then ident else "Hello""#;
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let cond = IK![int, Symbol::intern("1"), 3, 1];
        let then = IK![
            explvalue,
            IK![lvalue, IK![ident, Symbol::intern("ident"), 10, 5]]
        ];
        let else_branch = IK![str, Symbol::intern("Hello"), 21, 7];

        assert_eq!(
            item,
            item!(IK!(if, cond, then, else_branch, 0, input.len())),
        );
    }

    #[test]
    fn test_while_expr() {
        let input = r#"while 1 do 3"#;
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let cond = IK![int, Symbol::intern("1"), 6, 1];
        let do_exp = IK![int, Symbol::intern("3"), 11, 1];

        assert_eq!(item, item!(IK!(while, cond, do_exp, 0, input.len())),);
    }

    #[test]
    fn test_for_expr() {
        let input = r#"for i := 0 to 10 do "Hello""#;
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let id = IK![ident, Symbol::intern("i"), 4, 1];
        let from = IK![int, Symbol::intern("0"), 9, 1];
        let to = IK![int, Symbol::intern("10"), 14, 2];
        let do_exp = IK![str, Symbol::intern("Hello"), 20, 7];

        assert_eq!(item, item!(IK!(for, id, from, to, do_exp, 0, input.len())),);
    }

    #[test]
    fn test_break_expr() {
        let input = "break";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let break_exp = IK![break, 0];

        assert_eq!(item, item!(break_exp));
    }

    #[test]
    fn test_arithmetic_expressions() {
        let input = "3 + 3";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let left = IK![int, Symbol::intern("3"), 0, 1];
        let right = IK![int, Symbol::intern("3"), 4, 1];

        assert_eq!(item, item!(IK![+, left, right, 0, input.len(), 2]));

        let input = "3 - 3";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let left = IK![int, Symbol::intern("3"), 0, 1];
        let right = IK![int, Symbol::intern("3"), 4, 1];

        assert_eq!(item, item!(IK![-, left, right, 0, input.len(), 2]));

        let input = "3 * 3";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let left = IK![int, Symbol::intern("3"), 0, 1];
        let right = IK![int, Symbol::intern("3"), 4, 1];

        assert_eq!(item, item!(IK![*, left, right, 0, input.len(), 2]));

        let input = "3 / 3";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let left = IK![int, Symbol::intern("3"), 0, 1];
        let right = IK![int, Symbol::intern("3"), 4, 1];

        assert_eq!(item, item!(IK![/, left, right, 0, input.len(), 2]));
    }

    #[test]
    fn test_arithmetic_precedence() {
        let input = "1 + 2 * 3";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let left = IK![int, Symbol::intern("1"), 0, 1];
        let mid = IK![int, Symbol::intern("2"), 4, 1];
        let right = IK![int, Symbol::intern("3"), 8, 1];

        assert_eq!(
            item,
            item!(IK![+, left, IK![*, mid, right, 4, 5, 6], 0, input.len(), 2])
        );

        let input = "1 - 2 - 3";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let left = IK![int, Symbol::intern("1"), 0, 1];
        let mid = IK![int, Symbol::intern("2"), 4, 1];
        let right = IK![int, Symbol::intern("3"), 8, 1];

        assert_eq!(
            item,
            item!(IK![-, IK![-, left, mid, 0, 5, 2], right, 0, input.len(), 6])
        );
    }

    #[test]
    fn test_unary_expression() {
        let input = "-1 + 2";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let left = IK![-, IK![int, Symbol::intern("1"), 1, 1], 0, 2];
        let right = IK![int, Symbol::intern("2"), 5, 1];

        assert_eq!(item, item!(IK![+, left, right, 0, input.len(), 3]));

        let input = "---1";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let n1 = IK![int, Symbol::intern("1"), 3, 1];
        let inner = IK![-, n1, 2, 2];
        let mid = IK![-, inner, 1, 3];
        let outer = IK![-, mid, 0, input.len()];

        assert_eq!(item, item!(outer));

        let input = "1 * -2";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let n1 = IK![int, Symbol::intern("1"), 0, 1];
        let n2 = IK![int, Symbol::intern("2"), 5, 1];
        let right = IK![-, n2, 4, 2];

        assert_eq!(item, item!(IK![*, n1, right, 0, input.len(), 2]));
    }

    #[test]
    fn test_parenthesized_expressions() {
        let input = "1 * -( 2 - 3 )";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let n1 = IK![int, Symbol::intern("1"), 0, 1];
        let n2 = IK![int, Symbol::intern("2"), 7, 1];
        let n3 = IK![int, Symbol::intern("3"), 11, 1];
        let paren = IK![-, n2, n3, 5, 9, 9];
        let minus_paren = IK![-, paren, 4, 10];

        assert_eq!(item, item!(IK![*, n1, minus_paren, 0, input.len(), 2]));
    }

    #[test]
    fn test_member_access() {
        let input = "object.inner.member";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let member = IK![ident, Symbol::intern("member"), 13, 6];
        let inner = IK![ident, Symbol::intern("inner"), 7, 5];
        let object = IK![ident, Symbol::intern("object"), 0, 6];
        let object_inner = IK![member, IK![lvalue, object], inner, 0, 12];
        let inner_member = IK![member, object_inner, member, 0, input.len()];

        assert_eq!(item, item!(IK![explvalue, inner_member]));
    }

    #[test]
    fn test_array_access() {
        let input = "chess[0][7]";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let chess = IK![ident, Symbol::intern("chess"), 0, 5];
        let n0 = IK![int, Symbol::intern("0"), 6, 1];
        let n7 = IK![int, Symbol::intern("7"), 9, 1];
        let first_access = IK![array, IK![lvalue, chess], n0, 0, 8];
        let last_access = IK![array, first_access, n7, 0, input.len()];

        assert_eq!(item, item!(IK![explvalue, last_access]));
    }

    #[test]
    fn test_assignment() {
        let input = r#"game.board[0][7] := "King""#;
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let game = IK![lvalue, IK![ident, Symbol::intern("game"), 0, 4]];
        let board = IK![ident, Symbol::intern("board"), 5, 5];
        let game_board = IK![member, game, board, 0, 10];
        let n0 = IK![int, Symbol::intern("0"), 11, 1];
        let game_board_0 = IK![array, game_board, n0, 0, 13];
        let n7 = IK![int, Symbol::intern("7"), 14, 1];
        let game_board_0_7 = IK![array, game_board_0, n7, 0, 16];
        let king = IK![str, Symbol::intern("King"), 20, 6];
        let assign = IK![assign, game_board_0_7, king, 0, input.len()];

        assert_eq!(item, item!(assign));
    }

    #[test]
    fn test_new_expression() {
        let input = "new Game";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let ident = IK![ident, Symbol::intern("Game"), 4, 4];

        assert_eq!(item, item!(IK![new, ident, 0, input.len()]));
    }

    #[test]
    fn test_function_and_method_call() {
        let input = r#"print("Hello, world!", "\n")"#;
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let print = IK![lvalue, IK![ident, Symbol::intern("print"), 0, 5]];
        let string = IK![str, Symbol::intern("Hello, world!"), 6, 15];
        let new_line = IK![str, Symbol::intern("\n"), 23, 4];

        assert_eq!(
            item,
            item!(IK![fncall, print, vec![string, new_line], 0, input.len()])
        );

        let input = r#"exit()"#;
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let exit = IK![lvalue, IK![ident, Symbol::intern("exit"), 0, 4]];

        assert_eq!(item, item!(IK![fncall, exit, vec![], 0, input.len()]));
    }

    #[test]
    fn test_record_creation() {
        let input = "Game { board = new Board }";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let game = IK![ident, Symbol::intern("Game"), 0, 4];
        let board = IK![ident, Symbol::intern("board"), 7, 5];
        let new_board = IK![new, IK![ident, Symbol::intern("Board"), 19, 5], 15, 9];
        let board_member = IK![newmember, board, new_board, 7, 17];

        assert_eq!(
            item,
            item!(IK![newrecord, game, vec![board_member], 0, input.len()])
        );
    }

    #[test]
    fn test_array_creation() {
        let input = "int_array [10] of 0";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let id = IK![ident, Symbol::intern("int_array"), 0, 9];
        let n10 = IK![int, Symbol::intern("10"), 11, 2];
        let n0 = IK![int, Symbol::intern("0"), 18, 1];

        assert_eq!(item, item!(IK![newarray, id, n10, n0, 0, input.len()]));
    }
}
