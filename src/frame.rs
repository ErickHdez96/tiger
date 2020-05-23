pub mod x86_64;

use crate::asm::Instruction;
use crate::codegen::Procedure;
use crate::ir::{Exp, Stmt};
use crate::temp::{Label, Temp};
use crate::Symbol;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{self, Debug};
use std::rc::Rc;
pub use x86_64::X86_64;

pub trait Frame {
    type Access: Debug + Copy + Clone;
    const WORD_SIZE: usize;

    /// Crate a new Frame with the given name and formals.
    ///
    /// Formals is a slice of all the parameters to be received by `Frame`, each representing if
    /// the parameter escapes or not.
    fn new(name: Label, formals: &[bool]) -> Self;

    /// Get the name of the current frame.
    fn name(&self) -> Label;

    /// Get the formals of the current frame.
    fn formals(&self) -> &[Self::Access];

    /// Allocate a new local inside the frame, returning the access level assigned to it.
    ///
    /// Note: the allocated local is not added to the formals list.
    fn allocate_local(&mut self, escapes: bool) -> Self::Access;

    /// Get the frame register.
    fn fp() -> Temp;

    /// Get the return register (rv = return value).
    fn return_value() -> Temp;

    /// Transform an access and a frame pointer, into either a memory load or a temp expression.
    fn exp(&self, access: Self::Access, fp: Box<Exp>) -> Box<Exp>;

    /// Handles generating a call to an external function.
    fn external_call(name: impl Into<String>, params: &[Box<Exp>]) -> Box<Exp>;

    /// Mapping between registers and string representation.
    fn temp_map() -> &'static HashMap<Temp, &'static str>;

    fn proc_entry_exit_1(&self, stmt: Box<Stmt>) -> Box<Stmt>;

    fn proc_entry_exit_2(&self, instructions: Vec<Instruction>) -> Vec<Instruction>;

    fn proc_entry_exit_3(&self, body: Vec<Instruction>) -> Procedure;
}

#[derive(Debug)]
pub enum Fragment<F: Frame> {
    Procedure {
        body: Box<Stmt>,
        frame: Rc<RefCell<F>>,
    },
    /// A label pointing to a string stored in the final executable.
    String(Label, Symbol),
}

impl<F: Frame> Fragment<F> {
    /// Create a new `Fragment::Procedure`.
    pub fn new_procedure(body: Box<Stmt>, frame: Rc<RefCell<F>>) -> Self {
        Self::Procedure { body, frame }
    }

    /// Create a new `Fragment::String`.
    pub fn new_string(label: Label, symbol: Symbol) -> Self {
        Self::String(label, symbol)
    }
}

impl<F: Frame> fmt::Display for Fragment<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Fragment::Procedure { body, frame } => {
                writeln!(f, "{}:", frame.borrow().name())?;
                write!(f, "{}", body)
            }
            Fragment::String(label, symbol) => {
                writeln!(f, "{}:", label)?;
                write!(f, "{}", symbol.as_str())
            }
        }
    }
}
