mod dec;
mod exp;
mod ty;

use crate::env::Env;
use crate::error_reporter::CompilerError;
use crate::types::{TigerType, VarType};
use crate::{Item, Span, Symbol};
use std::fmt;
use std::rc::Rc;

type Vars<'a> = Env<'a, VarType>;
type Types<'a> = Env<'a, Rc<TigerType>>;
type TResult<T> = Result<T, TranslateError>;

#[macro_export]
macro_rules! terr {
    ($msg:expr, $snippet_span:expr, $error_span:expr) => {
        Err(TranslateError::new($msg, $snippet_span, $error_span))
    };
}

#[macro_export]
macro_rules! ty {
    (int) => {
        Rc::new(TigerType::Integer)
    };
    (str) => {
        Rc::new(TigerType::String)
    };
    (nil) => {
        Rc::new(TigerType::Nil)
    };
    (unit) => {
        Rc::new(TigerType::Unit)
    };
    ($self:expr, int) => {
        Rc::clone(&$self.int)
    };
    ($self:expr, str) => {
        Rc::clone(&$self.str)
    };
    ($self:expr, nil) => {
        Rc::clone(&$self.nil)
    };
    ($self:expr, unit) => {
        Rc::clone(&$self.unit)
    };
    ($types:expr, $id:expr, $snippet_span:expr) => {
        ty!($self, $types, $id, $snippet_span, $snippet_span)
    };
    ($types:expr, $id:expr, $snippet_span:expr, $error_span:expr) => {
        $types.get($id).ok_or_else(|| {
            TranslateError::new(
                format!("Type `{}` is not defined", $id.as_str()),
                $snippet_span,
                $error_span,
            )
        })
    };
}

#[derive(Debug, PartialEq, Eq)]
pub struct ExpType {
    pub exp: (),
    pub ty: Rc<TigerType>,
    pub span: Span,
}

impl ExpType {
    fn new(ty: Rc<TigerType>, span: Span) -> Self {
        Self { exp: (), ty, span }
    }
}

impl fmt::Display for ExpType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ty.fmt(f)
    }
}

pub fn translate(item: Item) -> TResult<ExpType> {
    let translator = Translator::new();
    translator.translate(item)
}

#[derive(Debug)]
struct Translator {
    int: Rc<TigerType>,
    str: Rc<TigerType>,
    nil: Rc<TigerType>,
    unit: Rc<TigerType>,
}

impl Translator {
    fn new() -> Self {
        Self {
            int: Rc::new(TigerType::Integer),
            str: Rc::new(TigerType::String),
            nil: Rc::new(TigerType::Nil),
            unit: Rc::new(TigerType::Unit),
        }
    }

    fn translate(self, item: Item) -> TResult<ExpType> {
        let mut vars: Vars = Env::new();
        let mut types: Types = Env::new();

        vars.insert(Symbol::intern("nil"), VarType::Var(ty!(self, nil)));

        types.insert(Symbol::intern("int"), ty!(self, int));
        types.insert(Symbol::intern("string"), ty!(self, str));

        match item {
            Item::Exp(e) => self.translate_exp(&vars, &types, &e),
            Item::Decs(decs) => {
                self.translate_decs(&vars, &types, &decs)?;
                Ok(ExpType::new(ty!(self, unit), Span::new(0, 1)))
            }
        }
    }
}

#[derive(Debug)]
pub struct TranslateError {
    msg: String,
    snippet_span: Span,
    error_span: Span,
}

impl TranslateError {
    fn new(msg: impl Into<String>, snippet_span: Span, error_span: Span) -> Self {
        Self {
            msg: msg.into(),
            snippet_span,
            error_span,
        }
    }
}

impl CompilerError for TranslateError {
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
