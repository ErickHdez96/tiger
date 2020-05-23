use super::Frame;
use crate::asm::Instruction;
use crate::codegen::Procedure;
use crate::exp;
use crate::ir::{BinOp, Exp, Stmt};
use crate::temp::{Label, Temp};
use lazy_static::lazy_static;
use std::cmp;
use std::collections::HashMap;

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

lazy_static! {
    static ref RBP: Temp = Temp::new();
    static ref RSP: Temp = Temp::new();
    static ref RAX: Temp = Temp::new();
    static ref RBX: Temp = Temp::new();
    static ref RCX: Temp = Temp::new();
    static ref RDX: Temp = Temp::new();
    static ref RDI: Temp = Temp::new();
    static ref RSI: Temp = Temp::new();
    static ref R8: Temp = Temp::new();
    static ref R9: Temp = Temp::new();
    static ref R10: Temp = Temp::new();
    static ref R11: Temp = Temp::new();
    static ref R12: Temp = Temp::new();
    static ref R13: Temp = Temp::new();
    static ref R14: Temp = Temp::new();
    static ref R15: Temp = Temp::new();

    static ref REGISTERS_MAP: HashMap<Temp, &'static str> = {
        let mut map = HashMap::new();
        map.insert(*RBP, "rbp");
        map.insert(*RSP, "rsp");
        map.insert(*RAX, "rax");
        map.insert(*RBX, "rbx");
        map.insert(*RCX, "rcx");
        map.insert(*RDX, "rdx");
        map.insert(*RDI, "rdi");
        map.insert(*RSI, "rsi");
        map.insert(*R8,  "r8");
        map.insert(*R9,  "r9");
        map.insert(*R10, "r10");
        map.insert(*R11, "r11");
        map.insert(*R12, "r12");
        map.insert(*R13, "r13");
        map.insert(*R14, "r14");
        map.insert(*R15, "r15");
        map
    };

    /// The special registers are the frame register (rbp), the stack register (rbp), and the
    /// return register (rax).
    static ref SPECIAL_REGISTERS: Vec<Temp> = vec![*RBP, *RSP, *RAX];

    static ref ARGUMENT_REGISTERS: Vec<Temp> = vec![*RDI, *RSI, *RDX, *RCX, *R8, *R9];

    static ref CALLEE_SAVES: Vec<Temp> = vec![*RBX, *R12, *R13, *R14, *R15];

    static ref CALLER_SAVES: Vec<Temp> = vec![*R10, *R11];

    static ref CALLDEF_REGISTERS: Vec<Temp> = {
        let calldef_len = CALLER_SAVES.len() + ARGUMENT_REGISTERS.len() + 1;
        let mut calldef = Vec::with_capacity(calldef_len);
        calldef.extend(&*CALLER_SAVES);
        calldef.extend(&*ARGUMENT_REGISTERS);
        calldef.push(*RAX);
        calldef
    };
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

    fn temp_map() -> &'static HashMap<Temp, &'static str> {
        &*REGISTERS_MAP
    }

    fn fp() -> Temp {
        *RBP
    }

    fn return_value() -> Temp {
        *RAX
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

    fn proc_entry_exit_2(&self, mut instructions: Vec<Instruction>) -> Vec<Instruction> {
        let mut all_regs = Vec::with_capacity(CALLEE_SAVES.len() + 2);
        all_regs.push(Self::return_value());
        all_regs.push(Self::rsp());
        all_regs.extend(Self::callee_saves());
        instructions.push(Instruction::Op {
            asm: String::new(),
            src: all_regs,
            dst: vec![],
            jmp: None,
        });
        instructions
    }

    fn proc_entry_exit_3(&self, body: Vec<Instruction>) -> Procedure {
        Procedure {
            prolog: format!("PROCEDURE {}\n", self.name),
            body,
            epilog: format!("END {}\n", self.name),
        }
    }
}

impl X86_64 {
    pub fn special_registers() -> &'static [Temp] {
        &*SPECIAL_REGISTERS
    }

    pub fn argument_registers() -> &'static [Temp] {
        &*ARGUMENT_REGISTERS
    }

    pub fn callee_saves() -> &'static [Temp] {
        &*CALLEE_SAVES
    }

    pub fn caller_saves() -> &'static [Temp] {
        &*CALLER_SAVES
    }

    pub fn calldef_registers() -> &'static [Temp] {
        &*CALLDEF_REGISTERS
    }

    pub fn rax() -> Temp {
        *RAX
    }

    pub fn rdx() -> Temp {
        *RDX
    }

    pub fn rsp() -> Temp {
        *RSP
    }

    pub fn temp_to_string(temp: Temp) -> String {
        REGISTERS_MAP
            .get(&temp)
            .map(|t| String::from(*t))
            .unwrap_or_else(|| format!("t{}", temp.as_u32()))
    }
}
