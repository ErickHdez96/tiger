#![allow(clippy::vec_box)]
use crate::ast;
use crate::temp::{Label, Temp};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Exp {
    /// Integer constant.
    Const(isize),

    /// Symbolic constant `n` (corresponding to an assembly language label).
    Name(Label),

    /// Similar to a register, except that temporaries are infinite.
    Temp(Temp),

    /// Application of binary operator `BinOp` to `e1` and `e2`. Subexpression `e1` is evaluated
    /// before `e2`.
    BinOp(BinOp, Box<Exp>, Box<Exp>),

    /// Contentes of `word_size` bytes of memory starting at address `e` (where `word_size` is
    /// defined in the frame module).
    /// Note: When Mem is used as the left child of a `Stmt::Move`, it means "store", but anywhere
    /// else it means "fetch".
    Mem(Box<Exp>),

    /// Procedure call: the application of function `func` to argument list `args`.
    /// The subexpression `func` is evaluated before the arguments, which are evaluated from left
    /// to right.
    Call { func: Box<Exp>, args: Vec<Box<Exp>> },

    /// The statement `s` is evaluated for side effects, then `e` is evaluated for a result.
    Eseq(Box<Stmt>, Box<Exp>),
}

impl fmt::Display for Exp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Exp::Const(n) => write!(f, "{}", n),
            Exp::Name(label) => write!(f, "{}", label),
            Exp::Temp(tmp) => write!(f, "t{}", tmp),
            Exp::BinOp(op, left, right) => write!(f, "{} {} {}", left, op, right),
            Exp::Mem(m) => write!(f, "[{}]", m),
            Exp::Call { func, args } => write!(
                f,
                "{}({})",
                func,
                args.iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
            ),
            Exp::Eseq(stmt, exp) => write!(f, "{}\n{}", stmt, exp),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// Move(Exp::Temp(t), e)
    /// Evaluate `e` and move it into temporary `t`.
    ///
    /// Move(Mem(e1), e2)
    /// Evaluate `e1`, yielding address `a`. Then evaluate `e2`, and store the result into
    /// `word_size` bytes of memory starting at `a`.
    Move(Box<Exp>, Box<Exp>),

    /// Evaluate `e` and discard the result.
    Exp(Box<Exp>),

    /// Transfer control to addres `e`. The destination `e` may be a literal label (e.g.
    /// Name(label)), or it may be an address calculated by any other kind of expression.
    ///
    /// The list of labels `labels`, specifies all the possible locations that the expression `e`
    /// can evaluate to; this is used in dataflow analysis.
    ///
    /// The common case of jumping to a known label `l` is written as `Jump(Exp::Name(l), vec![l])`.
    Jump(Box<Exp>, Vec<Label>),

    /// Evaluate `left`, `right`, in that order, yielding values `a`, `b`. Then compare `a`, `b`
    /// using the relational operator `op`. If the result is `true`, jump to `true`, otherwise
    /// jump to `false`.
    CJump {
        op: RelOp,
        left: Box<Exp>,
        right: Box<Exp>,
        r#true: Label,
        r#false: Label,
    },

    /// The statement `s1` is followed by `s2`.
    Seq(Box<Stmt>, Box<Stmt>),

    /// Define the constant value of name `n` to be the current machine code address. This is like
    /// a label definition in assembly language. The value Name(n) may be the target of jumps,
    /// calls, etc.
    Label(Label),
}

impl Stmt {
    /// Check whether the current statement is a label.
    pub fn is_label(&self) -> bool {
        match self {
            Stmt::Label(_) => true,
            _ => false,
        }
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Move(dst, src) => match dst.as_ref() {
                Exp::Temp(_) | Exp::Mem(_) => match src.as_ref() {
                    Exp::Eseq(stmt, e) => {
                        stmt.fmt(f)?;
                        write!(f, "\nmove {} ← {};", dst, e)
                    },
                    _ => write!(f, "move {} ← {};", dst, src),
                },
                s => panic!("Wrongly formed move statement, expected a temporal or memory access, found {:?}", s)
            },
            Stmt::Exp(e) => write!(f, "{};", e),
            Stmt::Jump(dst, labels) => write!(
                f,
                "jmp {} {{{}}};",
                dst,
                labels.iter().map(|l| l.to_string()).collect::<Vec<_>>().join(", "),
            ),
            Stmt::CJump { op, left, right, r#true, r#false } => {
                write!(f, "{} {} {} ? {} : {}", left, op, right, r#true, r#false)
            },
            Stmt::Seq(s1, s2) => write!(f, "{}\n{}", s1, s2),
            Stmt::Label(label) => write!(f, "{}:", label),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    /// +
    Plus,
    /// -
    Minus,
    /// *
    Mul,
    /// /
    Div,

    // Not in Tiger
    And,
    Or,
    Xor,
    LShift,
    RShift,
    ARShift,
}

impl BinOp {
    pub fn from_ast_bin_op(op: ast::BinOp) -> Option<Self> {
        use ast::BinOp::*;

        match op {
            Plus => Some(BinOp::Plus),
            Minus => Some(BinOp::Plus),
            Times => Some(BinOp::Mul),
            Div => Some(BinOp::Div),
            _ => None,
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BinOp::*;

        write!(
            f,
            "{}",
            match self {
                Plus => "+",
                Minus => "-",
                Mul => "*",
                Div => "/",
                And => "&",
                Or => "|",
                Xor => "^",
                LShift => "<<",
                RShift => ">>",
                ARShift => ">>>",
            }
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelOp {
    /// =
    Eq,

    /// <>
    Neq,

    /// signed <
    Lt,

    /// signed >
    Gt,

    /// signed <=
    Lte,

    /// signed >=
    Gte,

    /// unsigned <
    ULt,

    /// unsigned <=
    ULte,

    /// unsigned >
    UGt,

    /// unsigned >=
    UGte,
}

impl RelOp {
    pub fn from_ast_bin_op(op: ast::BinOp) -> Option<Self> {
        use ast::BinOp::*;

        match op {
            Eq => Some(RelOp::Eq),
            Neq => Some(RelOp::Neq),
            Lt => Some(RelOp::Lt),
            Gt => Some(RelOp::Gt),
            Lte => Some(RelOp::Lte),
            Gte => Some(RelOp::Gte),
            _ => None,
        }
    }

    pub fn inverse(self: RelOp) -> RelOp {
        use RelOp::*;

        match self {
            Eq => Neq,
            Neq => Eq,
            Lt => Gte,
            Gt => Lte,
            Lte => Gt,
            Gte => Lt,
            ULt => UGte,
            UGt => ULte,
            ULte => UGt,
            UGte => ULt,
        }
    }
}

impl fmt::Display for RelOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RelOp::*;

        write!(
            f,
            "{}",
            match self {
                Eq => "=",
                Neq => "<>",
                Lt => "<",
                Gt => ">",
                Lte => "≤",
                Gte => "≥",
                ULt => "u<",
                ULte => "u≤",
                UGt => "u>",
                UGte => "u≥",
            }
        )
    }
}

#[macro_export]
macro_rules! exp {
    (const $n:expr) => {
        Box::new(Exp::Const($n))
    };
    (name $label:expr) => {
        Box::new(Exp::Name($label))
    };
    (temp) => {
        Box::new(Exp::Temp(Temp::new()))
    };
    (temp $tmp:expr) => {
        Box::new(Exp::Temp($tmp))
    };
    (mem $e:expr) => {
        Box::new(Exp::Mem($e))
    };
    (binop $op:expr, $left:expr, $right:expr) => {
        Box::new(Exp::BinOp($op, $left, $right))
    };
    (call $fn:expr, $args:expr) => {
        Box::new(Exp::Call {
            func: $fn,
            args: $args,
        })
    };
    (+ $left:expr, $right:expr) => {
        exp!(BinOp::Plus, $left, $right)
    };
    (- $left:expr, $right:expr) => {
        exp!(BinOp::Minus, $left, $right)
    };
    (* $left:expr, $right:expr) => {
        exp!(BinOp::Mul, $left, $right)
    };
    (/ $left:expr, $right:expr) => {
        exp!(BinOp::Div, $left, $right)
    };
    ($op:expr, $left:expr, $right:expr) => {
        Box::new(Exp::BinOp($op, $left, $right))
    };
}

#[macro_export]
macro_rules! stmt {
    (move $e1:expr, $e2:expr) => {
        Box::new(Stmt::Move($e1, $e2))
    };
    (exp $e:expr) => {
        Box::new(Stmt::Exp($e))
    };
    (exp $($t:tt)+) => {
        Box::new(Stmt::Exp(exp!($($t)+)))
    };
    (jmp $exp:expr, $($label:expr),+ $(,)?) => {
        stmt!(jmp $exp, vec vec![$($label),+])
    };
    (jmp $exp:expr, vec $label:expr $(,)?) => {
        Box::new(Stmt::Jump($exp, $label))
    };
    (label) => {
        Box::new(Stmt::Label(Label::new()))
    };
    (label $label:expr) => {
        Box::new(Stmt::Label($label))
    };
    (cjmp <, $left:expr, $right:expr, $true:expr, $false:expr) => {
        stmt!(cjmp RelOp::Lt, $left, $right, $true, $false)
    };
    (cjmp >, $left:expr, $right:expr, $true:expr, $false:expr) => {
        stmt!(cjmp RelOp::Gt, $left, $right, $true, $false)
    };
    (cjmp =, $left:expr, $right:expr, $true:expr, $false:expr) => {
        stmt!(cjmp RelOp::Eq, $left, $right, $true, $false)
    };
    (cjmp <=, $left:expr, $right:expr, $true:expr, $false:expr) => {
        stmt!(cjmp RelOp::Lte, $left, $right, $true, $false)
    };
    (cjmp $op:expr, $left:expr, $right:expr, $true:expr, $false:expr) => {
        Box::new(Stmt::CJump {
            op: $op,
            left: $left,
            right: $right,
            r#true: $true,
            r#false: $false,
        })
    };
}

#[macro_export]
macro_rules! eseq {
    ($stmt:expr; $exp:expr) => {
        Box::new(Exp::Eseq($stmt, $exp))
    };
}

#[macro_export]
macro_rules! seq {
    ($stmt1:expr; $stmt2:expr $(;)?) => {
        Box::new(Stmt::Seq($stmt1, $stmt2))
    };
    ($stmt1:expr; $stmt2:expr; $($stmt:expr);+ $(;)?) => {
        seq!(seq!($stmt1; $stmt2); $($stmt);+)
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exp_macro() {
        let exp = exp!(const 1);

        match exp.as_ref() {
            Exp::Const(n) => {
                assert_eq!(*n, 1);
            }
            s => panic!("Wrongly expanded to {:?}", s),
        }

        let exp = exp!(temp);

        match exp.as_ref() {
            Exp::Temp(_) => {}
            s => panic!("Wrongly expanded to {:?}", s),
        }
    }

    #[test]
    fn test_stmt_macro() {
        let stmt = stmt!(move exp!(temp), exp!(const 1));

        match stmt.as_ref() {
            Stmt::Move(e1, e2) => {
                match e1.as_ref() {
                    Exp::Temp(_) => {}
                    e => panic!("Wrongly expanded to {:?}", e),
                }

                match e2.as_ref() {
                    Exp::Const(n) => {
                        assert_eq!(*n, 1);
                    }
                    e => panic!("Wrongly expanded to {:?}", e),
                }
            }
            s => panic!("Wrongly expanded to {:?}", s),
        }
    }

    #[test]
    fn test_eseq_macro() {
        let temp = exp!(temp);
        let exp = eseq!(
            stmt!(move temp.clone(), exp!(const 1));
            temp
        );

        match exp.as_ref() {
            Exp::Eseq(stmt, exp) => {
                let temp = match stmt.as_ref() {
                    Stmt::Move(t, _) => match t.as_ref() {
                        Exp::Temp(t) => t,
                        s => panic!("Wrongly expanded to {:?}", s),
                    },
                    s => panic!("Wrongly expanded to {:?}", s),
                };

                let temp2 = match exp.as_ref() {
                    Exp::Temp(t) => t,
                    e => panic!("Wrongly expanded to {:?}", e),
                };
                assert_eq!(temp, temp2, "Expected same temporals");
            }
            s => panic!("Wrongly expanded to {:?}", s),
        }
    }

    #[test]
    fn test_seq_macro() {
        let seq = seq!(
            stmt!(exp const 1);
            stmt!(exp const 2);
            stmt!(exp const 3);
        );

        match seq.as_ref() {
            Stmt::Seq(s1, s2) => {
                match s1.as_ref() {
                    Stmt::Seq(s1, s2) => {
                        match s1.as_ref() {
                            Stmt::Exp(e) => match e.as_ref() {
                                Exp::Const(1) => {}
                                s => panic!("Wrongly expanded to {:?}", s),
                            },
                            s => panic!("Wrongly expanded to {:?}", s),
                        }
                        match s2.as_ref() {
                            Stmt::Exp(e) => match e.as_ref() {
                                Exp::Const(2) => {}
                                s => panic!("Wrongly expanded to {:?}", s),
                            },
                            s => panic!("Wrongly expanded to {:?}", s),
                        }
                    }
                    s => panic!("Wrongly expanded to {:?}", s),
                }
                match s2.as_ref() {
                    Stmt::Exp(e) => match e.as_ref() {
                        Exp::Const(3) => {}
                        s => panic!("Wrongly expanded to {:?}", s),
                    },
                    s => panic!("Wrongly expanded to {:?}", s),
                }
            }
            s => panic!("Wrongly expanded to {:?}", s),
        }
    }
}
