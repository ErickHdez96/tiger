use super::Frame;
use crate::exp;
use crate::ir::{BinOp, Exp, Stmt};
use crate::temp::{Label, Temp};
use std::cmp;

#[derive(Debug, Copy, Clone)]
pub enum Access {
    InFrame(isize),
    InReg(Temp),
}

#[derive(Debug)]
pub struct X86_64 {
    name: Label,
    formals: Vec<Access>,
    ptr: isize,
}

impl cmp::PartialEq for X86_64 {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Frame for X86_64 {
    type Access = Access;
    const WORD_SIZE: usize = 8;

    fn new(name: Label, formals: &[bool]) -> Self {
        let mut frame = Self {
            name,
            formals: vec![],
            ptr: 0,
        };

        frame.formals = formals
            .iter()
            .map(|&e| frame.allocate_local(e))
            .collect::<Vec<_>>();

        frame
    }

    fn name(&self) -> Label {
        self.name
    }

    fn formals(&self) -> &[Self::Access] {
        &self.formals
    }

    fn allocate_local(&mut self, escapes: bool) -> Self::Access {
        if escapes {
            // word_size will always be a small number.
            self.ptr -= Self::WORD_SIZE as isize;
            Access::InFrame(self.ptr)
        } else {
            Access::InReg(Temp::new())
        }
    }

    fn fp() -> Temp {
        // TODO: Change this
        FP.with(|f| *f)
    }

    fn rv() -> Temp {
        // TODO: Change this
        RV.with(|r| *r)
    }

    /// Given an access and the frame_pointer, return an expression pointing to the desired
    /// variable.
    /// If the variable does not escape, a temporal will be returned.
    /// If the variable escapes, a memory address will be returned.
    fn exp(&self, access: Self::Access, fp: Box<Exp>) -> Box<Exp> {
        match access {
            Access::InReg(r) => exp!(temp r),
            Access::InFrame(ptr) => exp!(mem exp!(+ exp!(const ptr), fp)),
        }
    }

    fn external_call(_name: impl Into<String>, _params: &[Box<Exp>]) -> Box<Exp> {
        // TODO
        exp!(const 0)
    }

    fn proc_entry_exit_1(&self, stmt: Box<Stmt>) -> Box<Stmt> {
        stmt
    }
}

thread_local! {
    // Frame pointer
    static FP: Temp = Temp::new();

    // Return value
    static RV: Temp = Temp::new();
}
