use super::Parser;
use crate::ast::{ClassField, Dec, Identifier, TypeDec, TypeField, VarDec};
use crate::{Span, TokenKind, IK, T};

impl Parser {
    /// Parse multiple expressions
    ///
    /// decs ::= { dec }
    pub(super) fn parse_decs(&mut self) -> Option<Vec<Dec>> {
        let mut decs = vec![];

        while self.peek().kind().can_start_declaration() {
            decs.push(self.parse_dec()?);
        }

        Some(decs)
    }

    /// Parse a single declaration
    ///
    /// ```ignore
    /// dec ::=
    ///   # Type declaration.
    ///     `type` id `=` ty                                        ✓
    ///   # Class definition (alternative form).
    ///   | `class` id [ `extends` type-id ] `{` classfields `}`    ✓
    ///   # Variable declaration.
    ///   | vardec                                                  ✓
    ///   # Function declaration.
    ///   | `function` id `(` tyfields `)` [ `:` type-id ] `=` exp  ✓
    ///   # Primitive declaration.
    ///   | `primitive` id `(` tyfields `)` [ `:` type-id ]         ✓
    ///   # Importing a set of declarations.
    ///   | `import` string                                         ✓
    /// ```
    fn parse_dec(&mut self) -> Option<Dec> {
        match self.peek().kind() {
            T![import] => self.parse_import(),
            T![var] => self.parse_var_dec(),
            T![function] => self.parse_function_dec(),
            T![primitive] => self.parse_primitive_dec(),
            T![class] => self.parse_class_definition(),
            T![type] => self.parse_type_dec(),
            _ => None,
        }
    }

    /// Parse a type declaration.
    ///
    /// ty ::=
    ///     # Type alias.
    ///     type-id                                                 ✓
    ///     # Record type definition.
    ///     | `{` tyfields `}`                                      ✓
    ///     # Array type definition.
    ///     | `array` `of` type-id                                  ✓
    ///     # Class definition (canonical form).
    ///     | `class` [ `extends` type-id ] `{` classfields `}`     ✓
    fn parse_type_dec(&mut self) -> Option<Dec> {
        let start = self.eat(T![type])?.span();
        let id = {
            let (id, span) = self.eat_identifier()?;
            IK![ident, id, span.offset(), span.len()]
        };
        self.eat(T![=])?;
        match self.peek().kind() {
            TokenKind::Ident(s) => {
                let span = self.advance().span();
                let end = start.extend(span);
                Some(IK![
                    typedec,
                    IK![
                        typename,
                        id,
                        IK![ident, s, span.offset(), span.len()],
                        end.offset(),
                        end.len()
                    ]
                ])
            }
            T!['{'] => {
                self.advance();
                let fields = self.parse_type_fields()?;
                let end = start.extend(self.eat(T!['}'])?.span());
                Some(IK![
                    typedec,
                    IK![typerecord, id, fields, end.offset(), end.len()]
                ])
            }
            T![array] => {
                self.advance();
                self.eat(T![of])?;
                let (type_id, end) = {
                    let (id, span) = self.eat_identifier()?;
                    (
                        IK![ident, id, span.offset(), span.len()],
                        start.extend(span),
                    )
                };
                Some(IK![
                    typedec,
                    IK![typearray, id, type_id, end.offset(), end.len()]
                ])
            }
            T![class] => {
                self.eat(T![class])?;

                let extends = if self.peek().kind() == T![:] {
                    self.advance();
                    let (id, span) = self.eat_identifier()?;
                    Some(IK![ident, id, span.offset(), span.len()])
                } else {
                    None
                };

                self.eat(T!['{'])?;
                let fields = self.parse_class_fields()?;
                let end = start.extend(self.eat(T!['}'])?.span());
                Some(IK![
                    typedec,
                    IK![typeclass, id, extends, fields, end.offset(), end.len()]
                ])
            }
            _ => None,
        }
    }

    /// Parse a variable declaration
    ///
    /// vardec ::= `var` id [ `:` type-id ] `:=` exp
    fn parse_var_dec(&mut self) -> Option<Dec> {
        let start = self.eat(T![var])?.span();
        let (id, id_span) = self.eat_identifier()?;
        let id = IK![ident, id, id_span.offset(), id_span.len()];
        let opt_type = if self.peek().kind() == T![:] {
            self.advance();
            let (id, span) = self.eat_identifier()?;
            Some(IK![ident, id, span.offset(), span.len()])
        } else {
            None
        };
        self.eat(T![:=])?;
        let exp = self.parse_exp(0)?;
        let end = start.extend(exp.span());
        Some(IK![var, id, opt_type, exp, end.offset(), end.len()])
    }

    /// Parse a function declaration
    ///
    /// `function` id `(` tyfields `)` [ `:` type-id ] `=` exp
    fn parse_function_dec(&mut self) -> Option<Dec> {
        let start = self.eat(T![function])?.span();
        let id = {
            let (id, span) = self.eat_identifier()?;
            IK![ident, id, span.offset(), span.len()]
        };
        self.eat(T!['('])?;
        let type_fields = self.parse_type_fields()?;
        self.eat(T![')'])?;

        let ret_type = if self.peek().kind() == T![:] {
            self.advance();
            let (id, span) = self.eat_identifier()?;
            Some(IK![ident, id, span.offset(), span.len()])
        } else {
            None
        };

        self.eat(T![=])?;
        let body = self.parse_exp(0)?;
        let end = start.extend(body.span());
        Some(IK![
            fn,
            id,
            type_fields,
            ret_type,
            body,
            end.offset(),
            end.len()
        ])
    }

    /// Parse a primitive declaration.
    ///
    /// `primitive` id `(` tyfields `)` [ `:` type-id ]
    fn parse_primitive_dec(&mut self) -> Option<Dec> {
        let start = self.eat(T![primitive])?.span();
        let id = {
            let (id, span) = self.eat_identifier()?;
            IK![ident, id, span.offset(), span.len()]
        };
        self.eat(T!['('])?;
        let type_fields = self.parse_type_fields()?;
        let rparen = self.eat(T![')'])?.span();

        let (ret_type, end) = if self.peek().kind() == T![:] {
            self.advance();
            let (id, span) = self.eat_identifier()?;
            (
                Some(IK![ident, id, span.offset(), span.len()]),
                start.extend(span),
            )
        } else {
            (None, start.extend(rparen))
        };

        Some(IK![
            primitive,
            id,
            type_fields,
            ret_type,
            end.offset(),
            end.len()
        ])
    }

    /// Parse an import declaration
    ///
    /// `import` string
    fn parse_import(&mut self) -> Option<Dec> {
        let start = self.eat(T![import])?.span();
        let (path, end) = self.eat_string()?;
        let span = start.extend(end);
        Some(IK![import, path, span.offset(), span.len()])
    }

    /// Parse a class definition.
    ///
    /// `class` id [ `extends` type-id ] `{` classfields `}`    •
    fn parse_class_definition(&mut self) -> Option<Dec> {
        let start = self.eat(T![class])?.span();
        let id = {
            let (id, span) = self.eat_identifier()?;
            IK![ident, id, span.offset(), span.len()]
        };

        let extends = if self.peek().kind() == T![:] {
            self.advance();
            let (id, span) = self.eat_identifier()?;
            Some(IK![ident, id, span.offset(), span.len()])
        } else {
            None
        };

        self.eat(T!['{'])?;
        let fields = self.parse_class_fields()?;
        let end = start.extend(self.eat(T!['}'])?.span());
        Some(IK![class, id, extends, fields, end.offset(), end.len()])
    }

    /// Parse 0 or more comma separated type fields.
    ///
    /// tyfields ::= [ id `:` type-id { `,` id `:` type-id } ]
    fn parse_type_fields(&mut self) -> Option<Vec<TypeField>> {
        if !self.peek().kind().is_identifier() {
            return Some(vec![]);
        }

        let mut type_fields = vec![self.parse_type_field()?];

        while self.peek().kind() == T![,] {
            self.advance();
            type_fields.push(self.parse_type_field()?);
        }
        Some(type_fields)
    }

    /// Parse a type field.
    ///
    /// id `:` type-id
    fn parse_type_field(&mut self) -> Option<TypeField> {
        let (id, start) = {
            let (id, span) = self.eat_identifier()?;
            (IK![ident, id, span.offset(), span.len()], span)
        };
        self.eat(T![:])?;
        let (type_id, end) = {
            let (id, span) = self.eat_identifier()?;
            (
                IK![ident, id, span.offset(), span.len()],
                start.extend(span),
            )
        };
        Some(IK![tyfield, id, type_id, end.offset(), end.len()])
    }

    /// Parses 0 or more class fields.
    ///
    /// classfields ::= { classfield }
    fn parse_class_fields(&mut self) -> Option<Vec<ClassField>> {
        let mut fields = vec![];

        while self.peek().kind() != T!['}'] {
            fields.push(self.parse_class_field()?);
        }

        Some(fields)
    }

    /// Parses a class fields.
    /// classfield ::=
    ///     # Attribute declaration.
    ///     vardec
    ///     # Method declaration.
    ///     | `method` id `(` tyfields `)` [ `:` type-id ] `=` exp
    fn parse_class_field(&mut self) -> Option<ClassField> {
        match self.peek().kind() {
            T![var] => self.parse_class_attribute(),
            T![method] => self.parse_class_method(),
            _ => None,
        }
    }

    /// Parse a class attribute definition.
    ///
    /// vardec ::= `var` id [ `:` type-id ] `:=` exp
    fn parse_class_attribute(&mut self) -> Option<ClassField> {
        let start = self.eat(T![var])?.span();
        let (id, id_span) = self.eat_identifier()?;
        let id = IK![ident, id, id_span.offset(), id_span.len()];
        let opt_type = if self.peek().kind() == T![:] {
            self.advance();
            let (id, span) = self.eat_identifier()?;
            Some(IK![ident, id, span.offset(), span.len()])
        } else {
            None
        };
        self.eat(T![:=])?;
        let exp = self.parse_exp(0)?;
        let end = start.extend(exp.span());
        Some(IK![classvar, id, opt_type, exp, end.offset(), end.len()])
    }

    /// Parses a class method definition.
    ///
    /// `method` id `(` tyfields `)` [ `:` type-id ] `=` exp
    fn parse_class_method(&mut self) -> Option<ClassField> {
        let start = self.eat(T![method])?.span();
        let id = {
            let (id, span) = self.eat_identifier()?;
            IK![ident, id, span.offset(), span.len()]
        };
        self.eat(T!['('])?;
        let type_fields = self.parse_type_fields()?;
        self.eat(T![')'])?;

        let ret_type = if self.peek().kind() == T![:] {
            self.advance();
            let (id, span) = self.eat_identifier()?;
            Some(IK![ident, id, span.offset(), span.len()])
        } else {
            None
        };

        self.eat(T![=])?;
        let body = self.parse_exp(0)?;
        let end = start.extend(body.span());
        Some(IK![
            classfn,
            id,
            type_fields,
            ret_type,
            body,
            end.offset(),
            end.len()
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinOp, Exp, Item, LValue, TypeField, VarDec};
    use crate::{parse, tokenize, Symbol};

    macro_rules! item {
        (exp, $item:expr) => {
            Item::Exp($item)
        };
        (decs, $item:expr) => {
            Item::Decs(vec![$item])
        };
    }

    #[test]
    fn test_import() {
        let input = r#"import "std""#;
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        assert_eq!(
            item,
            item!(decs, IK![import, Symbol::intern("std"), 0, input.len()])
        );
    }

    #[test]
    fn test_var_dec() {
        let input = "var pi: int := 3";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let pi = IK![ident, Symbol::intern("pi"), 4, 2];
        let int = IK![ident, Symbol::intern("int"), 8, 3];
        let n3 = IK![int, Symbol::intern("3"), 15, 1];

        assert_eq!(
            item,
            item!(decs, IK![var, pi, Some(int), n3, 0, input.len()])
        );
    }

    #[test]
    fn test_function_dec() {
        let input = "function add(x: int, y: int): int = x + y";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let fn_name = IK![ident, Symbol::intern("add"), 9, 3];
        let x_int = IK![ident, Symbol::intern("int"), 16, 3];
        let x = IK![
            tyfield,
            IK![ident, Symbol::intern("x"), 13, 1],
            x_int,
            13,
            6
        ];
        let y_int = IK![ident, Symbol::intern("int"), 24, 3];
        let y = IK![
            tyfield,
            IK![ident, Symbol::intern("y"), 21, 1],
            y_int,
            21,
            6
        ];
        let ret = IK![ident, Symbol::intern("int"), 30, 3];
        let x_body = IK![
            explvalue,
            IK![lvalue, IK![ident, Symbol::intern("x"), 36, 1]]
        ];
        let y_body = IK![
            explvalue,
            IK![lvalue, IK![ident, Symbol::intern("y"), 40, 1]]
        ];
        let body = IK![+, x_body, y_body, 36, 5, 38];

        assert_eq!(
            item,
            item!(
                decs,
                IK![fn, fn_name, vec![x, y], Some(ret), body, 0, input.len()]
            )
        );
    }

    #[test]
    fn test_primitive_dec() {
        let input = "primitive pow(x: int, y: int): int";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let fn_name = IK![ident, Symbol::intern("pow"), 10, 3];
        let x_int = IK![ident, Symbol::intern("int"), 17, 3];
        let x = IK![
            tyfield,
            IK![ident, Symbol::intern("x"), 14, 1],
            x_int,
            14,
            6
        ];
        let y_int = IK![ident, Symbol::intern("int"), 25, 3];
        let y = IK![
            tyfield,
            IK![ident, Symbol::intern("y"), 22, 1],
            y_int,
            22,
            6
        ];
        let ret = IK![ident, Symbol::intern("int"), 31, 3];

        assert_eq!(
            item,
            item!(
                decs,
                IK![primitive, fn_name, vec![x, y], Some(ret), 0, input.len()]
            )
        );
    }

    #[test]
    fn test_class_definition() {
        let input = r#"class Game { var player: string := "X" }"#;
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let class_name = IK![ident, Symbol::intern("Game"), 6, 4];
        let player = IK![ident, Symbol::intern("player"), 17, 6];
        let string = IK![ident, Symbol::intern("string"), 25, 6];
        let x = IK![str, Symbol::intern("X"), 35, 3];
        let vardec = IK![classvar, player, Some(string), x, 13, 25];

        assert_eq!(
            item,
            item!(
                decs,
                IK![class, class_name, None, vec![vardec], 0, input.len()]
            )
        );
    }

    #[test]
    fn test_type_name() {
        let input = "type int2 = int";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let int2 = IK![ident, Symbol::intern("int2"), 5, 4];
        let int = IK![ident, Symbol::intern("int"), 12, 3];

        assert_eq!(
            item,
            item!(decs, IK![typedec, IK![typename, int2, int, 0, input.len()]])
        );
    }

    #[test]
    fn test_type_record() {
        let input = "type Token = { kind: string, len: int }";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let token = IK![ident, Symbol::intern("Token"), 5, 5];
        let kind = IK![ident, Symbol::intern("kind"), 15, 4];
        let string = IK![ident, Symbol::intern("string"), 21, 6];
        let kind = IK![tyfield, kind, string, 15, 12];
        let len = IK![ident, Symbol::intern("len"), 29, 3];
        let int = IK![ident, Symbol::intern("int"), 34, 3];
        let len = IK![tyfield, len, int, 29, 8];

        assert_eq!(
            item,
            item!(
                decs,
                IK![
                    typedec,
                    IK![typerecord, token, vec![kind, len], 0, input.len()]
                ]
            )
        );
    }

    #[test]
    fn test_type_array() {
        let input = "type int_array = array of int";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let int_array = IK![ident, Symbol::intern("int_array"), 5, 9];
        let int = IK![ident, Symbol::intern("int"), 26, 3];

        assert_eq!(
            item,
            item!(
                decs,
                IK![typedec, IK![typearray, int_array, int, 0, input.len()]]
            )
        );
    }

    #[test]
    fn test_type_class() {
        let input = "type Math = class { method sqr(x: int): int = x * x }";
        let item = parse(tokenize(input).0).0.expect("Couldn't parse input");

        let math = IK![ident, Symbol::intern("Math"), 5, 4];
        let sqr = IK![ident, Symbol::intern("sqr"), 27, 3];
        let x_s = Symbol::intern("x");
        let int_s = Symbol::intern("int");
        let x_1 = IK![ident, x_s, 31, 1];
        let x_2 = IK![explvalue, IK![lvalue, IK![ident, x_s, 46, 1]]];
        let x_3 = IK![explvalue, IK![lvalue, IK![ident, x_s, 50, 1]]];
        let int_1 = IK![ident, int_s, 34, 3];
        let int_2 = IK![ident, int_s, 40, 3];
        let x_param = IK![tyfield, x_1, int_1, 31, 6];
        let body = IK![*, x_2, x_3, 46, 5, 48];
        let method = IK![classfn, sqr, vec![x_param], Some(int_2), body, 20, 31];

        assert_eq!(
            item,
            item!(
                decs,
                IK![
                    typedec,
                    IK![typeclass, math, None, vec![method], 0, input.len()]
                ]
            )
        );
    }
}
