use super::Frame;
use crate::temp::{Label, Temp};

#[derive(Debug, Copy, Clone)]
pub enum Access {
    InFrame(isize),
    InReg(Temp),
}

const POINTER_SIZE: isize = 8;

#[derive(Debug)]
pub struct X86_64 {
    name: Label,
    formals: Vec<Access>,
    ptr: isize,
}

impl Frame for X86_64 {
    type Access = Access;

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
            self.ptr -= POINTER_SIZE;
            Access::InFrame(self.ptr)
        } else {
            Access::InReg(Temp::new())
        }
    }
}
