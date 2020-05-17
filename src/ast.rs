use crate::{Span, Symbol};
use std::fmt;

#[derive(Debug, PartialEq, Eq)]
pub enum Item {
    Exp(Box<Exp>),
    Decs(Vec<Dec>),
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Item::Exp(e) => e.fmt(f),
            Item::Decs(decs) => {
                for dec in decs {
                    writeln!(f, "{}", dec)?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Dec {
    ImportDec {
        path: Symbol,
        span: Span,
    },
    Class {
        id: Identifier,
        extends: Option<Identifier>,
        fields: Vec<ClassField>,
        span: Span,
    },
    TypeDec(Box<TypeDec>),
    VarDec(Box<VarDec>),
}

impl Dec {
    pub fn span(&self) -> Span {
        match self {
            Dec::ImportDec { span, .. } | Dec::Class { span, .. } => *span,
            Dec::TypeDec(ty) => ty.span(),
            Dec::VarDec(var) => var.span(),
        }
    }
}

impl fmt::Display for Dec {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Dec::*;

        match self {
            ImportDec { path, .. } => write!(f, r#"import "{}""#, path.as_str()),
            Class {
                id,
                extends,
                fields,
                ..
            } => {
                write!(f, "class {}", id)?;
                if let Some(e) = extends {
                    write!(f, " extends {}", e)?;
                }
                writeln!(f, " {{")?;

                for field in fields {
                    writeln!(f, "{}", field)?;
                }

                writeln!(f, "}}")
            }
            TypeDec(ty) => ty.fmt(f),
            VarDec(var) => var.fmt(f),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypeField {
    pub id: Identifier,
    pub type_id: Identifier,
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq)]
pub struct FunctionField {
    pub id: Identifier,
    pub type_id: Identifier,
    pub escapes: bool,
    pub span: Span,
}

impl fmt::Display for TypeField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.id, self.type_id)
    }
}

impl fmt::Display for FunctionField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.id, self.type_id)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ClassField {
    Attribute {
        id: Identifier,
        opt_type: Option<Identifier>,
        exp: Box<Exp>,
        span: Span,
    },
    Method {
        id: Identifier,
        params: Vec<TypeField>,
        ret_type: Option<Identifier>,
        body: Box<Exp>,
        span: Span,
    },
}

impl fmt::Display for ClassField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClassField::Attribute {
                id, opt_type, exp, ..
            } => match opt_type {
                Some(ty) => write!(f, "var {}: {} := {}", id, ty, exp),
                None => write!(f, "var {} := {}", id, exp),
            },
            ClassField::Method {
                id,
                params,
                ret_type,
                body,
                ..
            } => {
                write!(f, "method {}(", id)?;
                for (i, param) in params.iter().enumerate() {
                    write!(f, "{}{}", if i == 0 { "" } else { ", " }, param)?;
                }
                match ret_type {
                    Some(ty) => writeln!(f, "): {} =\n{}", ty, body),
                    None => writeln!(f, ") =\n{}", body),
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TypeDec {
    Name {
        id: Identifier,
        type_id: Identifier,
        span: Span,
    },
    Record {
        id: Identifier,
        fields: Vec<TypeField>,
        span: Span,
    },
    Array {
        id: Identifier,
        type_id: Identifier,
        span: Span,
    },
    Class {
        id: Identifier,
        extends: Option<Identifier>,
        fields: Vec<ClassField>,
        span: Span,
    },
}

impl TypeDec {
    pub fn span(&self) -> Span {
        match self {
            TypeDec::Name { span, .. }
            | TypeDec::Record { span, .. }
            | TypeDec::Array { span, .. }
            | TypeDec::Class { span, .. } => *span,
        }
    }
}

impl fmt::Display for TypeDec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeDec::Name { id, type_id, .. } => write!(f, "type {} = {}", id, type_id),
            TypeDec::Record { id, fields, .. } => {
                write!(f, "type {} = {{ ", id)?;
                for (i, field) in fields.iter().enumerate() {
                    write!(f, "{}{}", if i == 0 { "" } else { ", " }, field)?;
                }
                write!(f, " }}")
            }
            TypeDec::Array { id, type_id, .. } => write!(f, "type {} = array of {}", id, type_id),
            TypeDec::Class {
                id,
                extends,
                fields,
                ..
            } => {
                write!(f, "class {}", id)?;
                if let Some(e) = extends {
                    write!(f, " extends {}", e)?;
                }
                writeln!(f, " {{")?;

                for field in fields {
                    writeln!(f, "{}", field)?;
                }

                writeln!(f, "}}")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum VarDec {
    Var {
        id: Identifier,
        opt_type: Option<Identifier>,
        exp: Box<Exp>,
        escapes: bool,
        span: Span,
    },
    Fn {
        id: Identifier,
        params: Vec<FunctionField>,
        ret_type: Option<Identifier>,
        body: Box<Exp>,
        span: Span,
    },
    Primitive {
        id: Identifier,
        params: Vec<TypeField>,
        ret_type: Option<Identifier>,
        span: Span,
    },
}

impl VarDec {
    pub fn span(&self) -> Span {
        match self {
            VarDec::Var { span, .. } | VarDec::Fn { span, .. } | VarDec::Primitive { span, .. } => {
                *span
            }
        }
    }
}

impl fmt::Display for VarDec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use VarDec::*;

        match self {
            Var {
                id, opt_type, exp, ..
            } => match opt_type {
                Some(ty) => write!(f, "var {}: {} := {}", id, ty, exp),
                None => write!(f, "var {} := {}", id, exp),
            },
            Fn {
                id,
                params,
                ret_type,
                body,
                ..
            } => {
                write!(f, "function {}(", id)?;
                for (i, param) in params.iter().enumerate() {
                    write!(f, "{}{}", if i == 0 { "" } else { ", " }, param)?;
                }
                match ret_type {
                    Some(ty) => writeln!(f, "): {} =\n{}", ty, body),
                    None => writeln!(f, ") =\n{}", body),
                }
            }
            Primitive {
                id,
                params,
                ret_type,
                ..
            } => {
                write!(f, "primitive {}(", id)?;
                for (i, param) in params.iter().enumerate() {
                    write!(f, "{}{}", if i == 0 { "" } else { ", " }, param)?;
                }
                match ret_type {
                    Some(ty) => writeln!(f, "): {}", ty),
                    None => writeln!(f, ")"),
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Exp {
    LetExp {
        decs: Vec<Dec>,
        exps: Vec<Exp>,
        span: Span,
    },
    IfExp {
        cond: Box<Exp>,
        then_branch: Box<Exp>,
        else_branch: Option<Box<Exp>>,
        span: Span,
    },
    WhileExp {
        cond: Box<Exp>,
        do_exp: Box<Exp>,
        span: Span,
    },
    ForExp {
        id: Identifier,
        id_escapes: bool,
        from: Box<Exp>,
        to: Box<Exp>,
        do_exp: Box<Exp>,
        span: Span,
    },

    NewArrayExp {
        id: Identifier,
        length: Box<Exp>,
        init: Box<Exp>,
        span: Span,
    },
    NewRecordExp {
        id: Identifier,
        members: Vec<Member>,
        span: Span,
    },
    Exps {
        exps: Vec<Exp>,
        span: Span,
    },

    LValue(Box<LValue>),
    AssignExp {
        lvalue: Box<LValue>,
        exp: Box<Exp>,
        span: Span,
    },
    NewExp {
        id: Identifier,
        span: Span,
    },
    FnCall {
        lvalue: Box<LValue>,
        args: Vec<Exp>,
        span: Span,
    },

    BinExp {
        op: BinOp,
        left: Box<Exp>,
        right: Box<Exp>,
        span: Span,
        op_span: Span,
    },
    UnaryExp {
        exp: Box<Exp>,
        span: Span,
    }, // -exp

    IntegerExp {
        value: usize,
        span: Span,
    },
    StringExp {
        value: Symbol,
        span: Span,
    },

    NilExp {
        span: Span,
    },
    BreakExp {
        span: Span,
    },
}

impl Exp {
    pub fn span(&self) -> Span {
        use Exp::*;

        match self {
            LetExp { span, .. }
            | IfExp { span, .. }
            | WhileExp { span, .. }
            | ForExp { span, .. }
            | Exps { span, .. }
            | NewRecordExp { span, .. }
            | NewArrayExp { span, .. }
            | AssignExp { span, .. }
            | NewExp { span, .. }
            | FnCall { span, .. }
            | BinExp { span, .. }
            | UnaryExp { span, .. }
            | IntegerExp { span, .. }
            | StringExp { span, .. }
            | BreakExp { span, .. }
            | NilExp { span, .. } => *span,
            LValue(lvalue) => lvalue.span(),
        }
    }

    pub fn set_span(&mut self, new_span: Span) {
        use Exp::*;

        match self {
            LetExp { ref mut span, .. }
            | IfExp { ref mut span, .. }
            | WhileExp { ref mut span, .. }
            | ForExp { ref mut span, .. }
            | Exps { ref mut span, .. }
            | NewRecordExp { ref mut span, .. }
            | NewArrayExp { ref mut span, .. }
            | AssignExp { ref mut span, .. }
            | NewExp { ref mut span, .. }
            | FnCall { ref mut span, .. }
            | BinExp { ref mut span, .. }
            | UnaryExp { ref mut span, .. }
            | IntegerExp { ref mut span, .. }
            | StringExp { ref mut span, .. }
            | BreakExp { ref mut span, .. }
            | NilExp { ref mut span, .. } => {
                *span = new_span;
            }
            LValue(lvalue) => lvalue.set_span(new_span),
        }
    }
}

impl fmt::Display for Exp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Exp::LetExp { decs, exps, .. } => {
                writeln!(f, "let")?;
                for dec in decs.iter() {
                    dec.fmt(f)?;
                }

                writeln!(f, "in")?;
                for exp in exps.iter() {
                    exp.fmt(f)?;
                }

                writeln!(f, "end")
            }
            Exp::AssignExp { lvalue, exp, .. } => write!(f, "{} := {}", lvalue, exp),
            Exp::BinExp {
                op, left, right, ..
            } => write!(f, "({} {} {})", left, op, right),
            Exp::IntegerExp { value, .. } => write!(f, "{}", value),
            Exp::LValue(lvalue) => lvalue.fmt(f),
            Exp::StringExp { value, .. } => write!(f, r#""{}""#, value.as_str()),
            Exp::Exps { exps, .. } => {
                for (i, exp) in exps.iter().enumerate() {
                    write!(f, "{}{}", if i == 0 { "" } else { "; " }, exp)?;
                }
                Ok(())
            }
            Exp::FnCall { lvalue, args, .. } => {
                write!(f, "{}(", lvalue)?;
                for (i, arg) in args.iter().enumerate() {
                    write!(f, "{}{}", if i == 0 { "" } else { ", " }, arg)?;
                }
                write!(f, ")")
            }
            e => todo!("{:?}", e),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Member {
    pub id: Identifier,
    pub exp: Box<Exp>,
    pub span: Span,
}

impl Member {
    pub fn new(id: Identifier, exp: Box<Exp>, span: Span) -> Self {
        Self { id, exp, span }
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn set_span(&mut self, new_span: Span) {
        self.span = new_span
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum LValue {
    Identifier(Identifier),
    MemberAccess {
        lvalue: Box<LValue>,
        member: Identifier,
        span: Span,
    },
    ArrayAccess {
        lvalue: Box<LValue>,
        exp: Box<Exp>,
        span: Span,
    },
}

impl LValue {
    pub fn span(&self) -> Span {
        use LValue::*;

        match self {
            MemberAccess { span, .. } | ArrayAccess { span, .. } => *span,
            Identifier(ident) => ident.span(),
        }
    }

    pub fn set_span(&mut self, new_span: Span) {
        use LValue::*;

        match self {
            MemberAccess { ref mut span, .. } | ArrayAccess { ref mut span, .. } => {
                *span = new_span;
            }
            Identifier(ident) => ident.set_span(new_span),
        }
    }
}

impl fmt::Display for LValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LValue::Identifier(id) => id.fmt(f),
            LValue::MemberAccess { lvalue, member, .. } => write!(f, "({}.{})", lvalue, member),
            LValue::ArrayAccess { lvalue, exp, .. } => write!(f, "({}[{}])", lvalue, exp),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Identifier {
    id: Symbol,
    span: Span,
}

impl Identifier {
    pub fn new(id: Symbol, span: Span) -> Self {
        Self { id, span }
    }

    pub fn id(self) -> Symbol {
        self.id
    }

    pub fn span(self) -> Span {
        self.span
    }

    pub fn set_span(&mut self, new_span: Span) {
        self.span = new_span;
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.id.as_str())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    /// +
    Plus,
    /// -
    Minus,
    /// *
    Times,
    /// /
    Div,
    /// =
    Eq,
    /// <>
    Neq,
    /// >
    Gt,
    /// <
    Lt,
    /// >=
    Gte,
    /// <=
    Lte,
    /// &
    And,
    /// |
    Or,
}

impl BinOp {
    pub const MIN_PRECEDENCE: usize = 0;
    pub const MAX_PRECEDENCE: usize = 6;

    pub fn precedence(self) -> usize {
        use BinOp::*;

        match self {
            Or => 1,
            And => 2,
            Gte | Lte | Eq | Neq | Gt | Lt => 3,
            Plus | Minus => 4,
            Times | Div => 5,
        }
    }

    /// Check if the operator is one of `+`, `-`, `*`, or `/`.
    pub fn is_arithmetic(self) -> bool {
        match self {
            BinOp::Plus | BinOp::Minus | BinOp::Times | BinOp::Div => true,
            _ => false,
        }
    }

    /// Check if the operator is either `=`, or `<>`.
    pub fn is_equality(self) -> bool {
        self == BinOp::Eq || self == BinOp::Neq
    }

    /// Check if the operator is one of `=`, `<>`, `<`, `>`, `<=`, or `>=`.
    pub fn is_comparison(self) -> bool {
        match self {
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Lte | BinOp::Gte => true,
            _ => false,
        }
    }

    /// Get the length of the token in bytes.
    pub fn char_len(self) -> usize {
        if self == BinOp::Neq || self == BinOp::Gte || self == BinOp::Lte {
            2
        } else {
            1
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                BinOp::Plus => "+",
                BinOp::Minus => "-",
                BinOp::Times => "*",
                BinOp::Div => "/",
                BinOp::Eq => "=",
                BinOp::Neq => "<>",
                BinOp::Gt => ">",
                BinOp::Lt => "<",
                BinOp::Gte => ">=",
                BinOp::Lte => "<=",
                BinOp::And => "&",
                BinOp::Or => "|",
            }
        )
    }
}

#[macro_export]
macro_rules! IK {
    (import, $path:expr, $offset:expr, $length:expr) => {
        Dec::ImportDec {
            path: $path,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (var, $id:expr, $type:expr, $exp:expr, $offset:expr, $length:expr) => {
        Dec::VarDec(Box::new(VarDec::Var {
            id: $id,
            opt_type: $type,
            exp: Box::new($exp),
            escapes: false,
            span: Span::new($offset as u32, $length as u32),
        }))
    };
    (fn, $id:expr, $params:expr, $ret_type:expr, $body:expr, $offset:expr, $length:expr) => {
        Dec::VarDec(Box::new(VarDec::Fn {
            id: $id,
            params: $params,
            ret_type: $ret_type,
            body: Box::new($body),
            span: Span::new($offset as u32, $length as u32),
        }))
    };
    (primitive, $id:expr, $params:expr, $ret_type:expr, $offset:expr, $length:expr) => {
        Dec::VarDec(Box::new(VarDec::Primitive {
            id: $id,
            params: $params,
            ret_type: $ret_type,
            span: Span::new($offset as u32, $length as u32),
        }))
    };
    (class, $id:expr, $extends:expr, $fields:expr, $offset:expr, $length:expr) => {
        Dec::Class {
            id: $id,
            extends: $extends,
            fields: $fields,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (tyfield, $id:expr, $type:expr, $offset:expr, $length:expr) => {
        TypeField {
            id: $id,
            type_id: $type,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (fnfield, $id:expr, $type:expr, $offset:expr, $length:expr) => {
        FunctionField {
            id: $id,
            type_id: $type,
            escapes: false,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (classvar, $id:expr, $type:expr, $exp:expr, $offset:expr, $length:expr) => {
        ClassField::Attribute {
            id: $id,
            opt_type: $type,
            exp: Box::new($exp),
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (classfn, $id:expr, $params:expr, $ret_type:expr, $body:expr, $offset:expr, $length:expr) => {
        ClassField::Method {
            id: $id,
            params: $params,
            ret_type: $ret_type,
            body: Box::new($body),
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (typedec, $type:expr) => {
        Dec::TypeDec(Box::new($type))
    };

    (typename, $id:expr, $type:expr, $offset:expr, $length:expr) => {
        TypeDec::Name {
            id: $id,
            type_id: $type,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (typerecord, $id:expr, $fields:expr, $offset:expr, $length:expr) => {
        TypeDec::Record {
            id: $id,
            fields: $fields,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (typearray, $id:expr, $type:expr, $offset:expr, $length:expr) => {
        TypeDec::Array {
            id: $id,
            type_id: $type,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (typeclass, $id:expr, $extends:expr, $fields:expr, $offset:expr, $length:expr) => {
        TypeDec::Class {
            id: $id,
            extends: $extends,
            fields: $fields,
            span: Span::new($offset as u32, $length as u32),
        }
    };

    (nil, $offset:expr) => {
        Exp::NilExp {
            span: Span::new($offset as u32, 3),
        }
    };
    (break, $offset:expr) => {
        Exp::BreakExp {
            span: Span::new($offset as u32, 5),
        }
    };
    (int, $int:expr, $offset:expr, $length:expr) => {
        Exp::IntegerExp {
            value: $int,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (str, $symbol:expr, $offset:expr, $length:expr) => {
        Exp::StringExp {
            value: $symbol,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (ident, $symbol:expr, $offset:expr, $length:expr) => {
        Identifier::new($symbol, Span::new($offset as u32, $length as u32))
    };
    (let, $decs:expr, $exps:expr, $offset:expr, $length:expr) => {
        Exp::LetExp {
            decs: $decs,
            exps: $exps,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (if, $cond:expr, $then:expr, opt $else:expr, $offset:expr, $length:expr) => {
        Exp::IfExp {
            cond: Box::new($cond),
            then_branch: Box::new($then),
            else_branch: $else,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (if, $cond:expr, $then:expr, $else:expr, $offset:expr, $length:expr) => {
        Exp::IfExp {
            cond: Box::new($cond),
            then_branch: Box::new($then),
            else_branch: Some(Box::new($else)),
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (if, $cond:expr, $then:expr, $offset:expr, $length:expr) => {
        Exp::IfExp {
            cond: Box::new($cond),
            then_branch: Box::new($then),
            else_branch: None,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (while, $cond:expr, $do:expr, $offset:expr, $length:expr) => {
        Exp::WhileExp {
            cond: Box::new($cond),
            do_exp: Box::new($do),
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (for, $id:expr, $from:expr, $to:expr, $do:expr, $offset:expr, $length:expr) => {
        Exp::ForExp {
            id: $id,
            id_escapes: false,
            from: Box::new($from),
            to: Box::new($to),
            do_exp: Box::new($do),
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (newrecord, $id:expr, $members:expr, $offset:expr, $length:expr) => {
        Exp::NewRecordExp {
            id: $id,
            members: $members,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (newarray, $id:expr, box $array_len:expr, $init:expr, $offset:expr, $length:expr) => {
        Exp::NewArrayExp {
            id: $id,
            length: $array_len,
            init: Box::new($init),
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (newarray, $id:expr, $array_len:expr, $init:expr, $offset:expr, $length:expr) => {
        Exp::NewArrayExp {
            id: $id,
            length: Box::new($array_len),
            init: Box::new($init),
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (newmember, $id:expr, $exp:expr, $offset:expr, $length:expr) => {
        Member::new($id, Box::new($exp), Span::new($offset, $length))
    };
    (assign, $lvalue:expr, $exp:expr, $offset:expr, $length:expr) => {
        Exp::AssignExp {
            lvalue: Box::new($lvalue),
            exp: Box::new($exp),
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (new, $ident:expr, $offset:expr, $length:expr) => {
        Exp::NewExp {
            id: $ident,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (fncall, $lvalue:expr, $exps:expr, $offset:expr, $length:expr) => {
        Exp::FnCall {
            lvalue: Box::new($lvalue),
            args: $exps,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (explvalue, $lvalue:expr) => {
        Exp::LValue(Box::new($lvalue))
    };
    (lvalue, $ident:expr) => {
        LValue::Identifier($ident)
    };
    (member, $lvalue:expr, $id:expr, $offset:expr, $length:expr) => {
        LValue::MemberAccess {
            lvalue: Box::new($lvalue),
            member: $id,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (array, $lvalue:expr, $exp:expr, $offset:expr, $length:expr) => {
        LValue::ArrayAccess {
            lvalue: Box::new($lvalue),
            exp: Box::new($exp),
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (exps, $exps:expr, $offset:expr, $length:expr) => {
        Exp::Exps {
            exps: $exps,
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (-, $exp:expr, $offset:expr, $length:expr) => {
        Exp::UnaryExp {
            exp: Box::new($exp),
            span: Span::new($offset as u32, $length as u32),
        }
    };
    (+, $left:expr, $right:expr, $offset:expr, $length:expr, $op_offset:expr) => {
        IK![BinOp::Plus, $left, $right, $offset, $length, $op_offset]
    };
    (-, $left:expr, $right:expr, $offset:expr, $length:expr, $op_offset:expr) => {
        IK![BinOp::Minus, $left, $right, $offset, $length, $op_offset]
    };
    (*, $left:expr, $right:expr, $offset:expr, $length:expr, $op_offset:expr) => {
        IK![BinOp::Times, $left, $right, $offset, $length, $op_offset]
    };
    (/, $left:expr, $right:expr, $offset:expr, $length:expr, $op_offset:expr) => {
        IK![BinOp::Div, $left, $right, $offset, $length, $op_offset]
    };
    ($op:expr, $left:expr, $right:expr, $offset:expr, $length:expr, $op_offset:expr) => {
        Exp::BinExp {
            op: $op,
            left: Box::new($left),
            right: Box::new($right),
            span: Span::new($offset as u32, $length as u32),
            op_span: Span::new($op_offset as u32, $op.char_len() as u32),
        }
    };
}
