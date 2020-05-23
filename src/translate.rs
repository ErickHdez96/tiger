pub mod translators;

use crate::frame::{Fragment, Frame};
use crate::ir::{Exp, RelOp, Stmt};
use crate::temp::{Label, Temp};
use crate::{eseq, exp, seq, stmt};
use std::cell::RefCell;
use std::cmp;
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Access<F: Frame>(Rc<Level<F>>, F::Access);

impl<F: Frame> Access<F> {
    /// Get the level of the current access.
    pub fn level(&self) -> &Rc<Level<F>> {
        &self.0
    }

    /// Get the frame access of the current level access.
    pub fn frame_access(&self) -> F::Access {
        self.1
    }
}

#[derive(Debug, Clone)]
pub struct Level<F: Frame> {
    frame: Rc<RefCell<F>>,
    parent: Option<Rc<Level<F>>>,
}

impl<F: Frame + PartialEq> cmp::PartialEq for Level<F> {
    fn eq(&self, other: &Self) -> bool {
        self.frame == other.frame
    }
}

impl<F: Frame> Level<F> {
    pub fn new(parent: &Rc<Level<F>>, name: Label, formals: &[bool]) -> Rc<Level<F>> {
        let mut new_formals = Vec::with_capacity(formals.len());
        new_formals.push(true);
        new_formals.extend(formals);

        Rc::new(Self {
            frame: Rc::new(RefCell::new(F::new(name, &new_formals))),
            parent: Some(Rc::clone(parent)),
        })
    }

    pub fn frame(&self) -> &Rc<RefCell<F>> {
        &self.frame
    }

    pub fn formals(self: &Rc<Self>) -> Vec<Access<F>> {
        self.frame
            .borrow()
            .formals()
            .iter()
            .map(|access| Access::<F>(Rc::clone(&self), *access))
            .collect()
    }

    pub fn allocate_local(self: &Rc<Self>, escapes: bool) -> Access<F> {
        let new_access = self.frame.borrow_mut().allocate_local(escapes);
        Access(Rc::clone(self), new_access)
    }
}

pub fn outermost<F: Frame>() -> Rc<Level<F>> {
    Rc::new(Level {
        frame: Rc::new(RefCell::new(F::new(Label::new(), &[]))),
        parent: None,
    })
}

pub enum ExpKind {
    /// Expression represented as an [`ir::Exp`].
    Ex(Box<Exp>),

    /// No result, represented as an [`ir::Stmt`].
    Nx(Box<Stmt>),

    /// Conditional, represented as a function from label-pair to statement.
    /// If you pass a true-destination and a false-destination, it will make a statement that
    /// evaluates some conditionals and then jumps to one of the destinations.
    Cx(Box<dyn FnOnce(Label, Label) -> Box<Stmt>>),
}

impl fmt::Debug for ExpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpKind::Ex(e) => f.debug_tuple("Ex").field(e).finish(),
            ExpKind::Nx(n) => f.debug_tuple("Nx").field(n).finish(),
            ExpKind::Cx(_) => f.debug_tuple("Cx").finish(),
        }
    }
}

impl cmp::PartialEq for ExpKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ExpKind::Ex(e1), ExpKind::Ex(e2)) => e1 == e2,
            (ExpKind::Nx(s1), ExpKind::Nx(s2)) => s1 == s2,
            _ => false,
        }
    }
}

impl fmt::Display for ExpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpKind::Ex(e) => e.fmt(f),
            ExpKind::Nx(n) => n.fmt(f),
            ExpKind::Cx(_) => write!(f, "{{closure}}"),
        }
    }
}

#[derive(Debug, Default)]
pub struct Gen<F: Frame> {
    pub fragments: Vec<Fragment<F>>,
}

impl<F: Frame> Gen<F> {
    pub fn new() -> Self {
        Self { fragments: vec![] }
    }
}

/// Transform an ExpKind into an intermediate Exp.
pub fn un_ex(e: ExpKind) -> Box<Exp> {
    match e {
        ExpKind::Ex(e) => e,
        ExpKind::Nx(stmt) => eseq!(stmt; exp!(const 0)),
        ExpKind::Cx(gen_stmt) => {
            let r = exp!(temp);
            let t = Label::new();
            let f = Label::new();
            let stmt: Box<Stmt> = gen_stmt(t, f);

            eseq!(
                seq!(
                    stmt!(move r.clone(), exp!(const 1));
                    stmt;
                    stmt!(label f);
                    stmt!(move r.clone(), exp!(const 0));
                    stmt!(label t);
                );
                r
            )
        }
    }
}

/// Transform an ExpKind into an intermediate Stmt.
pub fn un_nx(e: ExpKind) -> Box<Stmt> {
    match e {
        ExpKind::Ex(e) => stmt!(exp e),
        ExpKind::Nx(s) => s,
        ExpKind::Cx(gen_stmt) => {
            let label = Label::new();
            gen_stmt(label, label)
        }
    }
}

/// Transform an ExpKind into an intermediate Stmt.
pub fn un_cx(e: ExpKind) -> Box<dyn FnOnce(Label, Label) -> Box<Stmt>> {
    match e {
        ExpKind::Ex(e) => match e.as_ref() {
            // Always jump to the false label
            Exp::Const(0) => Box::new(|_, label| stmt!(jmp exp!(name label), label)),
            // Always jump to the true label
            Exp::Const(_) => Box::new(|label, _| stmt!(jmp exp!(name label), label)),
            // If the expression yields 0, jump to the false label,
            // otherwise jump to the true label
            // TODO: Check if it actually makes sense to have them in that order
            _ => Box::new(|r#true, r#false| stmt!(cjmp =, e, exp!(const 0), r#false, r#true)),
        },
        ExpKind::Nx(s) => panic!(
            "This is a bug in the compiler, unexpected no result expression {:?}",
            s
        ),
        ExpKind::Cx(gen_stmt) => gen_stmt,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frame::{x86_64::Access as xAccess, X86_64};
    use crate::ir::BinOp;

    macro_rules! expect {
        (eseq, $stmt:expr) => {
            match $stmt.as_ref() {
                Exp::Eseq(s, e) => (s, e),
                s => panic!("Expected statement sequence, got {:?}", s),
            }
        };
        (seq, $stmt:expr) => {
            match $stmt.as_ref() {
                Stmt::Seq(s1, s2) => (s1, s2),
                s => panic!("Expected expression sequence, got {:?}", s),
            }
        };
        (label, $stmt:expr) => {
            match $stmt.as_ref() {
                Stmt::Label(l) => l,
                s => panic!("Expected label, got {:?}", s),
            }
        };
        (temp, $exp:expr) => {
            match $exp.as_ref() {
                Exp::Temp(t) => t,
                s => panic!("Expected temporal, got {:?}", s),
            }
        };
        (move, $stmt:expr) => {
            match $stmt.as_ref() {
                Stmt::Move(e1, e2) => (e1, e2),
                s => panic!("Expected move, got {:?}", s),
            }
        };
        (mem, $exp:expr) => {
            match $exp.as_ref() {
                Exp::Mem(e) => e,
                s => panic!("Expected a memory access, got {:?}", s),
            }
        };
        (const, $exp:expr) => {
            match $exp.as_ref() {
                Exp::Const(c) => c,
                s => panic!("Expected a const expression, got {:?}", s),
            }
        };
        (binop, $op:pat, $exp:expr) => {
            match $exp.as_ref() {
                Exp::BinOp($op, l, r) => (l, r),
                s => panic!("Expected an arithmetic expression, got {:?}", s),
            }
        };
        (+, $exp:expr) => {
            expect!(binop, BinOp::Plus, $exp)
        };
    }

    #[test]
    fn test_un_ex() {
        let exp = ExpKind::Ex(exp!(const 0));
        assert_eq!(
            un_ex(exp),
            exp!(const 0),
            "Expected un_ex to only unwrap the expression"
        );

        let label = Label::new();
        let stmt = ExpKind::Nx(stmt!(label label));
        assert_eq!(
            un_ex(stmt),
            eseq!(stmt!(label label); exp!(const 0)),
            "Expected un_ex to create an expression sequence"
        );

        // a > b | c < d
        // given: a = 0, b = 1, c = 2, d = 3
        let jmp = ExpKind::Cx(Box::new(|t, f| {
            let label = Label::new();
            seq!(
                stmt!(cjmp >, exp!(const 0), exp!(const 1), t, label);
                stmt!(label label);
                stmt!(cjmp <, exp!(const 2), exp!(const 3), t , f);
            )
        }));

        let jmp = un_ex(jmp);
        let (stmts, exp) = expect!(eseq, jmp);

        let (s1, s2) = expect!(seq, stmts);
        let t_label = expect!(label, s2);

        let (s1, s2) = expect!(seq, s1);
        let (move_e1, move_e2) = expect!(move, s2);
        assert_eq!(move_e1, exp);
        assert_eq!(move_e2, &exp!(const 0));

        let (s1, s2) = expect!(seq, s1);
        let f_label = expect!(label, s2);

        let (s1, s2) = expect!(seq, s1);
        let (move_e1, move_e2) = expect!(move, s1);
        assert_eq!(move_e1, exp);
        assert_eq!(move_e2, &exp!(const 1));

        let (gs1, cjmp) = expect!(seq, s2);
        assert_eq!(
            cjmp,
            &stmt!(cjmp <, exp!(const 2), exp!(const 3), *t_label, *f_label)
        );
        let (cjmp, label) = expect!(seq, gs1);
        let label = expect!(label, label);
        assert_eq!(
            cjmp,
            &stmt!(cjmp >, exp!(const 0), exp!(const 1), *t_label, *label)
        );
    }

    #[test]
    fn test_following_static_links_x86_64() {
        let outer_level = Level::<X86_64>::new(&outermost(), Label::new(), &[true]);
        let escaped_variable = &outer_level.allocate_local(true);
        let inner_level = Level::<X86_64>::new(&outer_level, Label::new(), &[]);

        let frame_access = escaped_variable.frame_access();
        let var = translators::simple_var(&escaped_variable, &inner_level);
        let var = un_ex(var);

        // We are expecting a structure similar to
        //
        // Mem(
        //  BinOp(
        //      +,
        //      Const(escaped_variable offset),
        //      Mem(
        //          BinOp(
        //              +,
        //              Const(offset to the static link in inner_level pointing to outer_level),
        //              Temp(fp)
        //          )
        //      )
        //  )
        // )

        dbg!(&var);
        let mem = expect!(mem, var);
        let (left, right) = expect!(+, mem);
        let left = expect!(const, left);
        // This should be the offset of the variable in `level`.
        match frame_access {
            xAccess::InFrame(n) => assert_eq!(*left, n),
            xAccess::InReg(_) => panic!("Expected variable to be in frame"),
        }

        let mem = expect!(mem, right);
        let (left, right) = expect!(+, mem);
        let left = expect!(const, left);
        // This should be the static link from the inner_level to level.
        assert_eq!(*left, -(X86_64::WORD_SIZE as isize));
        // TODO: Test actual fp
        let _temp = expect!(temp, right);
    }
}
