#![allow(clippy::vec_box)]
use crate::asm::Instruction;
use crate::frame::{Frame, X86_64};
use crate::ir::{BinOp, Exp, RelOp, Stmt};
use crate::temp::Temp;
use std::fmt;

#[derive(Debug, Default)]
pub struct CodeGen {
    instructions: Vec<Instruction>,
}

impl CodeGen {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn into_instructions(self) -> Vec<Instruction> {
        self.instructions
    }

    fn emit(&mut self, inst: Instruction) {
        self.instructions.push(inst);
    }

    fn munch_args(&mut self, args: Vec<Box<Exp>>) -> Vec<Temp> {
        let mut call_temps = vec![];
        let mut args_iter = args.into_iter();

        for reg in X86_64::argument_registers() {
            match args_iter.next() {
                Some(arg) => {
                    let src_reg = self.munch_exp(*arg);
                    self.emit(Instruction::Move {
                        asm: String::from("mov 'd0, 's0"),
                        dst: vec![*reg],
                        src: vec![src_reg],
                    });
                    call_temps.push(*reg);
                }
                None => break,
            }
        }

        let stack_args = args_iter
            .map(|arg| Instruction::Op {
                asm: String::from("push 's0"),
                dst: vec![],
                src: vec![self.munch_exp(*arg)],
                jmp: None,
            })
            .rev() // Args are pushed in reversed order
            .collect::<Vec<_>>();
        self.instructions.extend(stack_args);

        call_temps
    }

    pub fn munch_stmt(&mut self, stmt: Stmt) {
        match stmt {
            Stmt::Seq(l, r) => {
                self.munch_stmt(*l);
                self.munch_stmt(*r);
            }
            Stmt::Move(dst, src) => self.munch_move(*dst, *src),
            Stmt::Label(label) => {
                self.emit(Instruction::Label {
                    asm: format!("{}:", label),
                    label,
                });
            }
            Stmt::Exp(e) => match *e {
                Exp::Const(_) => { /* Nop statement */ }
                e => {
                    self.munch_exp(e);
                }
            },
            Stmt::Jump(dst, labels) => match *dst {
                Exp::Name(dst) => {
                    self.emit(Instruction::Op {
                        asm: format!("jmp {}", dst),
                        dst: vec![],
                        src: vec![],
                        jmp: Some(labels),
                    });
                }
                d => panic!("Invalid jump destination: {:?}", d),
            },
            Stmt::CJump {
                op,
                left,
                right,
                r#true,
                r#false,
            } => {
                let left_reg = self.munch_exp(*left);
                let right_reg = self.munch_exp(*right);
                self.emit(Instruction::Op {
                    asm: String::from("cmp 's0, 's1"),
                    dst: vec![],
                    src: vec![left_reg, right_reg],
                    jmp: None,
                });

                let jmp_opcode = match op {
                    RelOp::Eq => "je",
                    RelOp::Neq => "jne",
                    RelOp::Lt => "jl",
                    RelOp::Gt => "jg",
                    RelOp::Lte => "jle",
                    RelOp::Gte => "jge",
                    RelOp::ULt => "jb",
                    RelOp::UGt => "ja",
                    RelOp::ULte => "jbe",
                    RelOp::UGte => "jae",
                };

                self.emit(Instruction::Op {
                    asm: format!("{} {}", jmp_opcode, r#true),
                    dst: vec![],
                    src: vec![],
                    // TODO: Add next instruction
                    jmp: Some(vec![r#true, r#false]),
                });
            }
        }
    }

    fn munch_exp(&mut self, exp: Exp) -> Temp {
        let out_temp = Temp::new();
        match exp {
            Exp::Const(n) => self.emit(Instruction::Op {
                asm: format!("mov 'd0, {}", n),
                dst: vec![out_temp],
                src: vec![],
                jmp: None,
            }),
            Exp::Name(name) => self.emit(Instruction::Op {
                asm: format!("mov 'd0, {}", name),
                dst: vec![out_temp],
                src: vec![],
                jmp: None,
            }),
            Exp::Temp(t) => self.emit(Instruction::Op {
                asm: String::from("mov 'd0, 's0"),
                dst: vec![out_temp],
                src: vec![t],
                jmp: None,
            }),
            // A Memory expression on the right of a Move statement (store), is handled by
            // munch_stmt, meaning this is fetch.
            Exp::Mem(e) => match *e {
                Exp::BinOp(BinOp::Plus, e1, e2) if e1.is_const() || e2.is_const() => {
                    match (*e1, *e2) {
                        (Exp::Const(n), e) | (e, Exp::Const(n)) => {
                            let src_reg = self.munch_exp(e);
                            self.emit(Instruction::Move {
                                asm: format!("mov 'd0, ['s0 + {}]", n),
                                dst: vec![out_temp],
                                src: vec![src_reg],
                            });
                        }
                        _ => unreachable!(),
                    }
                }
                Exp::Const(n) => self.emit(Instruction::Move {
                    asm: format!("mov 'd0, [{}]", n),
                    dst: vec![out_temp],
                    src: vec![],
                }),
                Exp::Temp(t) => self.emit(Instruction::Move {
                    asm: String::from("mov 'd0, ['s0]"),
                    dst: vec![out_temp],
                    src: vec![t],
                }),
                e => {
                    let src_reg = self.munch_exp(e);
                    self.emit(Instruction::Move {
                        asm: String::from("mov 'd0, ['s0]"),
                        dst: vec![out_temp],
                        src: vec![src_reg],
                    });
                }
            },
            Exp::Call { func, args } => match *func {
                Exp::Name(func_name) => {
                    let args_len = args.len();
                    let args_tmps = self.munch_args(args);
                    let args_temps_len = args_tmps.len();
                    self.emit(Instruction::Op {
                        asm: format!("call {}", func_name),
                        src: args_tmps,
                        dst: X86_64::calldef_registers().to_vec(),
                        jmp: None,
                    });

                    self.emit(Instruction::Move {
                        asm: String::from("mov 'd0, 's0"),
                        dst: vec![out_temp],
                        src: vec![X86_64::return_value()],
                    });

                    // Pop arguments from stack
                    if args_len > args_temps_len {
                        self.emit(Instruction::Op {
                            asm: format!(
                                "add 'd0, {}",
                                (args_len - args_temps_len) * X86_64::WORD_SIZE
                            ),
                            src: vec![],
                            dst: vec![X86_64::rsp()],
                            jmp: None,
                        });
                    }
                }
                e => unimplemented!("Call to nonlabel: {:?}", e),
            },
            Exp::BinOp(op, e1, e2) => self.munch_bin_op(op, *e1, *e2, out_temp),
            Exp::Eseq(_, _) => panic!("Remaining Expr::Eseq"),
        }
        out_temp
    }

    fn munch_move(&mut self, dst: Exp, src: Exp) {
        match dst {
            Exp::Mem(e) => match *e {
                Exp::BinOp(BinOp::Plus, e1, e2) if e1.is_const() || e2.is_const() => {
                    match (*e1, *e2) {
                        (Exp::Const(n), e) | (e, Exp::Const(n)) => {
                            let dst_reg = self.munch_exp(e);
                            let src_reg = self.munch_exp(src);
                            self.emit(Instruction::Move {
                                asm: format!("mov ['s0 + {}], 's1", n),
                                dst: vec![],
                                src: vec![dst_reg, src_reg],
                            });
                        }
                        _ => unreachable!(),
                    }
                }
                Exp::Temp(t) => {
                    let src_reg = self.munch_exp(src);
                    self.emit(Instruction::Move {
                        asm: String::from("mov ['s0], 's1"),
                        dst: vec![],
                        src: vec![t, src_reg],
                    });
                }
                Exp::Const(n) => {
                    let src_reg = self.munch_exp(src);
                    self.emit(Instruction::Move {
                        asm: format!("mov [{}], 's0", n),
                        dst: vec![],
                        src: vec![src_reg],
                    });
                }
                e => {
                    let dst_reg = self.munch_exp(e);
                    let src_reg = self.munch_exp(src);
                    self.emit(Instruction::Move {
                        asm: String::from("mov ['s0], 's1"),
                        dst: vec![],
                        src: vec![dst_reg, src_reg],
                    });
                }
            },
            Exp::Temp(t) => {
                let src_reg = self.munch_exp(src);
                self.emit(Instruction::Move {
                    asm: String::from("mov 'd0, 's0"),
                    dst: vec![t],
                    src: vec![src_reg],
                });
            }
            d => panic!("Wrongly created move statement: {:?}", d),
        }
    }

    fn munch_bin_op(&mut self, op: BinOp, left: Exp, right: Exp, out_temp: Temp) {
        // TODO: Optimize for constants
        match op {
            BinOp::Plus | BinOp::Minus => {
                let op = if op == BinOp::Plus { "add" } else { "sub" };
                let left_reg = self.munch_exp(left);
                let right_reg = self.munch_exp(right);
                self.emit(Instruction::Move {
                    asm: String::from("mov 'd0, 's0"),
                    src: vec![left_reg],
                    dst: vec![out_temp],
                });
                self.emit(Instruction::Op {
                    asm: format!("{} 'd0, 's0", op),
                    src: vec![out_temp, right_reg],
                    dst: vec![out_temp],
                    jmp: None,
                });
            }
            BinOp::Mul => {
                let left_reg = self.munch_exp(left);
                let right_reg = self.munch_exp(right);
                self.emit(Instruction::Move {
                    asm: String::from("mov 'd0, 's0"),
                    src: vec![left_reg],
                    dst: vec![X86_64::rax()],
                });
                self.emit(Instruction::Op {
                    asm: String::from("mul 's0"),
                    src: vec![right_reg, X86_64::rax()],
                    dst: vec![X86_64::rax(), X86_64::rdx()],
                    jmp: None,
                });
                self.emit(Instruction::Move {
                    asm: String::from("mov 'd0, 's0"),
                    src: vec![X86_64::rax()],
                    dst: vec![out_temp],
                });
            }
            BinOp::Div => {
                let left_reg = self.munch_exp(left);
                let right_reg = self.munch_exp(right);
                // RDX:RAX is the dividend, meaning we have to clear RDX.
                self.emit(Instruction::Op {
                    asm: String::from("xor 'd0, 's0"),
                    src: vec![X86_64::rdx()],
                    dst: vec![X86_64::rdx()],
                    jmp: None,
                });
                self.emit(Instruction::Move {
                    asm: String::from("mov 'd0, 's0"),
                    src: vec![left_reg],
                    dst: vec![X86_64::rax()],
                });
                self.emit(Instruction::Op {
                    asm: String::from("idiv 'd0"),
                    src: vec![right_reg, X86_64::rax(), X86_64::rdx()],
                    dst: vec![X86_64::rax(), X86_64::rdx()],
                    jmp: None,
                });
                self.emit(Instruction::Move {
                    asm: String::from("mov 'd0, 's0"),
                    src: vec![X86_64::rax()],
                    dst: vec![out_temp],
                });
            }
            op => panic!("Codegen not implemented for binary operation: {}", op),
        }
    }
}

#[derive(Debug)]
pub struct Procedure {
    pub prolog: String,
    pub body: Vec<Instruction>,
    pub epilog: String,
}

impl fmt::Display for Procedure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.prolog)?;
        for instruction in self.body.iter() {
            writeln!(f, "{}", instruction)?;
        }
        write!(f, "{}", self.epilog)
    }
}
