use crate::frame::X86_64;
use crate::temp::{Label, Temp};
use std::fmt;

#[derive(Debug, PartialEq, Eq)]
pub enum Instruction {
    Op {
        asm: String,
        dst: Vec<Temp>,
        src: Vec<Temp>,
        jmp: Option<Vec<Label>>,
    },
    Label {
        asm: String,
        label: Label,
    },
    Move {
        asm: String,
        dst: Vec<Temp>,
        src: Vec<Temp>,
    },
}

impl Instruction {
    pub fn is_move(&self) -> bool {
        match self {
            Self::Move { .. } => true,
            _ => false,
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Label { asm, .. } => write!(f, "{}", asm),
            Instruction::Op { asm, dst, src, .. } | Instruction::Move { asm, dst, src } => {
                let mut out = asm.clone();

                for (i, temp) in dst.iter().enumerate() {
                    out = out.replace(&format!("'d{}", i), &X86_64::temp_to_string(*temp));
                }

                for (i, temp) in src.iter().enumerate() {
                    out = out.replace(&format!("'s{}", i), &X86_64::temp_to_string(*temp));
                }

                write!(f, "{}", out)
            }
        }
    }
}
