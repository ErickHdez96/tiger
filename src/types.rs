use crate::ast::BinOp;
use crate::frame::Frame;
use crate::temp::Label;
use crate::translate::{Access, Level};
use crate::Symbol;
use std::cmp::{Eq, PartialEq};
use std::fmt;
use std::rc::Rc;

#[derive(Debug)]
pub enum TigerType {
    Integer,
    String,
    Record(Vec<RecordMember>),
    Array(Rc<TigerType>),
    Nil,
    Unit,
    Name(Symbol, Option<Rc<TigerType>>),
}

impl TigerType {
    pub fn is_record(&self) -> bool {
        match self {
            TigerType::Record(_) => true,
            _ => false,
        }
    }

    pub fn is_int(&self) -> bool {
        *self == TigerType::Integer
    }

    pub fn is_nil(&self) -> bool {
        *self == TigerType::Nil
    }

    /// Test whether the two given types can appear on both sides of the operator `op`.
    ///
    /// Arithmetic operators: `+`, `-`, `*`, and `/`.
    /// Comparison operators: `=`, `<>`, `<=`, `<`, `>`, and `>=`.
    ///
    /// ## Rules:
    /// * Arithmetic expressions only apply on integers and return integers.
    /// * All the comparison operators apply to pairs of strings and pairs of integers.
    /// * Pairs of arrays and pairs of records of the same type can be compared for equality
    ///   (`=`) and inequality (`<>`).
    /// * The value nil can be compared against a value which type is that of a record or a class,
    ///   e.g. `nil = nil` is invalid.
    /// * Arrays, records and objects cannot be ordered: `<`, `>`, `<=`, `>=`.
    pub fn check_op_operation(&self, other: &Self, op: BinOp) -> bool {
        use TigerType::*;

        match (self, other) {
            // Any operator can be applied between ints
            (Integer, Integer) => true,
            // Only comparison operators
            (String, String) if op.is_comparison() => true,
            // Only equality between records, and arrays, or comparing nil to a record, but not nil
            // and nil.
            (Record(_), Nil) | (Nil, Record(_)) | (Record(_), Record(_)) | (Array(_), Array(_))
                if op.is_equality() =>
            {
                true
            }
            _ => false,
        }
    }

    /// Test whether the current type can be assigned to another type.
    ///
    /// Nil can be assigned to variables of Record or Class type.
    pub fn is_assignable_to(&self, other: &Self) -> bool {
        use TigerType::*;

        match (self, other) {
            (Nil, Record(_)) => true,
            _ => self == other,
        }
    }
}

impl fmt::Display for TigerType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TigerType::Integer => write!(f, "int"),
            TigerType::String => write!(f, "string"),
            TigerType::Nil => write!(f, "nil"),
            TigerType::Unit => write!(f, "unit"),
            TigerType::Record(members) => write!(
                f,
                "{{ {} }}",
                members
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            TigerType::Array(ty) => write!(f, "array of {}", ty),
            TigerType::Name(_, ty) => match ty {
                Some(ty) => ty.fmt(f),
                None => todo!(),
            },
        }
    }
}

impl PartialEq for TigerType {
    fn eq(&self, other: &TigerType) -> bool {
        use TigerType::*;

        match (self, other) {
            (Integer, Integer) | (String, String) | (Nil, Nil) | (Unit, Unit) => true,
            // Nominal type, compare if both refere to the same type. Don't compare by
            // record members.
            (Record(lmembers), Record(rmembers)) => lmembers.as_ptr().eq(&rmembers.as_ptr()),
            // Same as above
            (Array(l), Array(r)) => (&**l as *const TigerType).eq(&(&**r as *const TigerType)),
            // Compare the actual type they point to
            (Name(_, Some(l)), Name(_, Some(r))) => l == r,
            (Name(_, Some(l)), _) => &**l == other,
            (_, Name(_, Some(r))) => self == &**r,
            _ => false,
        }
    }
}

impl Eq for TigerType {}

#[derive(Debug)]
pub struct RecordMember {
    name: Symbol,
    tiger_type: Rc<TigerType>,
}

impl RecordMember {
    pub fn new(name: Symbol, ty: &Rc<TigerType>) -> Self {
        Self {
            name,
            tiger_type: Rc::clone(ty),
        }
    }

    /// Get the name of the member
    pub fn name(&self) -> Symbol {
        self.name
    }

    pub fn ty(&self) -> &Rc<TigerType> {
        &self.tiger_type
    }
}

impl fmt::Display for RecordMember {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name.as_str(), self.tiger_type)
    }
}

#[derive(Debug)]
pub enum VarType<F: Frame> {
    Var {
        ty: Rc<TigerType>,
        access: Access<F>,
    },
    Fn {
        formals: Vec<Rc<TigerType>>,
        ty: Rc<TigerType>,
        level: Rc<Level<F>>,
        label: Label,
    },
}

pub type VarFnDestructured<'a, F> = (
    &'a [Rc<TigerType>],
    &'a Rc<TigerType>,
    &'a Rc<Level<F>>,
    Label,
);

impl<F: Frame> VarType<F> {
    /// Create a new variable declaration with the given type and access.
    pub fn new_var(ty: Rc<TigerType>, access: Access<F>) -> Self {
        Self::Var { ty, access }
    }

    pub fn new_fn(
        formals: Vec<Rc<TigerType>>,
        ty: Rc<TigerType>,
        level: &Rc<Level<F>>,
        label: Label,
    ) -> Self {
        Self::Fn {
            formals,
            ty,
            level: Rc::clone(level),
            label,
        }
    }
}
