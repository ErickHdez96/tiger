mod dec;
mod exp;
mod ty;

use crate::env::Env;
use crate::error_reporter::CompilerError;
use crate::frame::{Fragment, Frame};
use crate::temp::Label;
use crate::translate::{self, ExpKind, Gen, Level};
use crate::types::{TigerType, VarType};
use crate::{Item, Span, Symbol};
use std::fmt;
use std::rc::Rc;

type Vars<'env, F> = Env<'env, VarType<F>>;
type Types<'a> = Env<'a, Rc<TigerType>>;
type TResult<T> = Result<T, TranslateError>;

#[macro_export]
macro_rules! terr {
    ($msg:expr, $snippet_span:expr, $error_span:expr $(,)?) => {
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

#[derive(Debug, PartialEq)]
pub struct ExpType {
    pub exp: ExpKind,
    pub ty: Rc<TigerType>,
    pub span: Span,
}

impl ExpType {
    fn new(exp: ExpKind, ty: Rc<TigerType>, span: Span) -> Self {
        Self { exp, ty, span }
    }
}

impl fmt::Display for ExpType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.exp.fmt(f)
    }
}

pub fn translate<F: Frame + PartialEq>(item: Item) -> TResult<Vec<Fragment<F>>> {
    let translator = Semant::<F>::new();
    translator.translate(item)
}

#[derive(Debug)]
struct Semant<F: Frame + PartialEq> {
    int: Rc<TigerType>,
    str: Rc<TigerType>,
    nil: Rc<TigerType>,
    unit: Rc<TigerType>,
    outerlevel: Rc<Level<F>>,

    gen: Gen<F>,

    /// A stack of labels pointing to the end of a loop expr. When reaching a break exression, it
    /// applies to the last label in the stack, if there is none, it means the break is ouside of a
    /// loop.
    loop_labels: Vec<Label>,
}

impl<F: Frame + PartialEq> Semant<F> {
    fn new() -> Self {
        Self {
            int: Rc::new(TigerType::Integer),
            str: Rc::new(TigerType::String),
            nil: Rc::new(TigerType::Nil),
            unit: Rc::new(TigerType::Unit),
            outerlevel: translate::outermost::<F>(),
            gen: Gen::new(),
            loop_labels: vec![],
        }
    }

    fn translate(mut self, item: Item) -> TResult<Vec<Fragment<F>>> {
        let vars = Env::new();
        let mut types = Env::new();

        types.insert(Symbol::intern("int"), ty!(self, int));
        types.insert(Symbol::intern("string"), ty!(self, str));

        match item {
            Item::Exp(e) => {
                let body = self.translate_exp(&vars, &types, &Rc::clone(&self.outerlevel), &e)?;
                self.gen.proc_entry_exit(
                    &Level::<F>::new(&self.outerlevel, Label::with_name("_main"), &[]),
                    body.exp,
                );
            }
            Item::Decs(decs) => {
                let (_, _, globals) =
                    self.translate_decs(&vars, &types, &Rc::clone(&self.outerlevel), &decs)?;
                self.gen.proc_entry_exit(&self.outerlevel, globals);
            }
        }

        Ok(self.gen.into_result())
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
