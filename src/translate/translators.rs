use super::{un_cx, un_ex, un_nx, Access, ExpKind, Gen, Level};
use crate::frame::{Fragment, Frame};
use crate::ir::{BinOp, Exp, RelOp, Stmt};
use crate::temp::{Label, Temp};
use crate::{ast, Symbol};
use crate::{eseq, exp, seq, stmt};
use std::rc::Rc;

/// Translate an integer into an ExpKind.
pub fn constant(n: usize) -> ExpKind {
    ExpKind::Ex(exp!(const n as isize))
}

pub fn unary_op(exp: ExpKind) -> ExpKind {
    ExpKind::Ex(exp!(-exp!(const 0), un_ex(exp)))
}

pub fn binary_op(op: ast::BinOp, left: ExpKind, right: ExpKind) -> ExpKind {
    if let Some(op) = BinOp::from_ast_bin_op(op) {
        ExpKind::Ex(exp!(binop op, un_ex(left), un_ex(right)))
    } else if let Some(op) = RelOp::from_ast_bin_op(op) {
        ExpKind::Cx(Box::new(
            move |r#true, r#false| stmt!(cjmp op, un_ex(left), un_ex(right), r#true, r#false),
        ))
    } else if op == ast::BinOp::Or {
        let left = un_cx(left);
        let right = un_cx(right);
        ExpKind::Cx(Box::new(|r#true, r#false| {
            let z = Label::new();
            seq!(
                left(r#true, z);
                stmt!(label z);
                right(r#true, r#false);
            )
        }))
    } else {
        let left = un_cx(left);
        let right = un_cx(right);
        ExpKind::Cx(Box::new(|r#true, r#false| {
            let z = Label::new();
            seq!(
                left(z, r#false);
                stmt!(label z);
                right(r#true, r#false);
            )
        }))
    }
}

pub fn assignment(lvalue: ExpKind, rvalue: ExpKind) -> ExpKind {
    ExpKind::Nx(stmt!(move un_ex(lvalue), un_ex(rvalue)))
}

pub fn fn_call<F: Frame + PartialEq>(
    label: Label,
    args: Vec<ExpKind>,
    fn_level: &Rc<Level<F>>,
    current_level: &Rc<Level<F>>,
) -> ExpKind {
    let parent_level: &Rc<Level<F>> = match &fn_level.parent {
        Some(p) => p,
        None => fn_level,
    };
    let mut link = exp!(temp F::fp());
    let mut current = current_level;

    // If fn_level is defined inside the current level
    // function a() =
    //          ^-a_level
    //  let
    //      function b(): int = 0
    //               ^-b_level
    //  in
    //      b()
    //      ^-current_level = a_level | fn_level = b_level
    //  end
    // We pass the the current frame pointer
    // parent_frame = a_level
    // parent_frame == current_level
    //  * static_link is fp
    //
    // If the function is a recursive call
    // function fact(n: int): int =
    //  let
    //      function fact_helper(n: int, acc: int): int =
    //          if n = 0
    //          then acc
    //          else fact_helper(n - 1, n * acc)
    //               ^-current_level = fact_helper | fn_level = fact_helper
    //  in
    //      fact_helper(n, 1)
    //  end
    // parent_frame = fact_level
    // current_level = fact_helper_level
    // Will only run once, returning a `mem` instruction to retrieve the current's static link.
    //
    // Retrieve the common parent's static link
    // function a() =
    //  let
    //      function d() = print("Hello")
    //
    //      function b() =
    //          let
    //              function c() = d()
    //                             ^- current_level = c_level | fn_level = d_level
    //                                c should pass a's frame pointer as the static link
    //          in c() end
    //      in b() end
    //  in a() end
    // parent_frame = a_level
    // current_level = c_level
    // First iteration will fetch c's static link, which is b's fp
    // Second iteration (current_level = b_level) will fetch b's static link, which is a's fp
    // Third iteration (current_level = a_level == parent_level)
    while current != parent_level {
        let current_link = current.frame.borrow().formals()[0];
        link = current.frame.borrow().exp(current_link, link);

        let parent = current
            .parent
            .as_ref()
            .expect("Compiler bug: Reached top frame without a match");
        current = parent;
    }

    let mut new_args = Vec::with_capacity(args.len() + 1);
    new_args.push(*link);
    for arg in args {
        new_args.push(*un_ex(arg));
    }
    ExpKind::Ex(exp!(call exp!(name label), new_args))
}

pub fn new_name() -> ExpKind {
    ExpKind::Ex(exp!(name Label::new()))
}

pub fn if_stmt(cond: ExpKind, then_branch: ExpKind) -> ExpKind {
    let cond = un_cx(cond);
    let then_label = Label::new();
    let end = Label::new();
    ExpKind::Nx(seq!(
        cond(then_label, end);
        stmt!(label then_label);
        un_nx(then_branch);
        stmt!(label end)
    ))
}

pub fn if_exp(cond: ExpKind, then_branch: ExpKind, else_branch: ExpKind) -> ExpKind {
    let cond = un_cx(cond);
    let end = Label::new();
    let result = exp!(temp);
    let then_label = Label::new();
    let else_label = Label::new();

    // TODO: Optimize this
    let th = un_ex(then_branch);
    let el = un_ex(else_branch);
    ExpKind::Ex(eseq!(
        seq!(
            cond(then_label, else_label);
            stmt!(label then_label);
            stmt!(move result.clone(), th);
            stmt!(jmp exp!(name end), end);
            stmt!(label else_label);
            stmt!(move result.clone(), el);
            stmt!(jmp exp!(name end), end);
            stmt!(label end);
        );
        result
    ))
}

/// Turn a variable expression (access and level) into an expression representing either its
/// places in memory, or in a register.
pub fn simple_var<F: Frame + PartialEq>(a: &Access<F>, l: &Rc<Level<F>>) -> ExpKind {
    let access_level = a.level();
    let mut current_level = l;
    let mut inner = exp!(temp F::fp());

    // Resolve all static links
    // The static link is sent as a first paramater to the function
    while access_level != current_level {
        inner = current_level
            .frame
            .borrow()
            .exp(current_level.formals()[0].frame_access(), inner);

        let parent = current_level
            .parent
            .as_ref()
            .expect("Compiler bug: Could not find variable's access level");
        current_level = parent;
    }
    // Resolve the actual offset of the variable
    inner = current_level.frame.borrow().exp(a.frame_access(), inner);

    ExpKind::Ex(inner)
}

pub fn array_access<F: Frame>(arr: ExpKind, exp: ExpKind) -> ExpKind {
    ExpKind::Ex(exp!(mem exp!(
            + un_ex(arr),
            exp!(
                * un_ex(exp),
                exp!(const F::WORD_SIZE as isize)
            )
        )
    ))
}

pub fn record_access<F: Frame>(record: ExpKind, member: usize) -> ExpKind {
    ExpKind::Ex(exp!(mem exp!(
            + un_ex(record),
            exp!(const (member * F::WORD_SIZE) as isize)
        )
    ))
}

pub fn record_creation<F: Frame>(members: Vec<ExpKind>) -> ExpKind {
    let result = Temp::new();
    let malloc = F::external_call(
        "malloc",
        &[exp!(const (members.len() * F::WORD_SIZE) as isize)],
    );

    let init = members.into_iter().enumerate().fold(
        stmt!(move exp!(temp result), malloc),
        |acc, (i, value)| {
            seq!(
                acc;
                stmt!(
                    move
                    exp!(mem exp!(+ exp!(temp result), exp!(const (i * F::WORD_SIZE) as isize))),
                    un_ex(value)
                )
            )
        },
    );

    ExpKind::Ex(eseq!(init; exp!(temp result)))
}

pub fn array_creation<F: Frame>(len: ExpKind, init: ExpKind) -> ExpKind {
    let result = Temp::new();
    let init = un_ex(init);
    let len = un_ex(len);
    let malloc = F::external_call(
        "malloc",
        &[exp!(*len.clone(), exp!(const F::WORD_SIZE as isize))],
    );
    let init_array = F::external_call("initArray", &[exp!(temp result), len, init]);

    ExpKind::Ex(eseq!(
        seq!(
            stmt!(move exp!(temp result), malloc);
            stmt!(exp init_array);
        );
        exp!(temp result)
    ))
}

pub fn exps(e1: ExpKind, e2: ExpKind) -> ExpKind {
    ExpKind::Ex(eseq!(
        stmt!(exp un_ex(e1));
        un_ex(e2)
    ))
}

pub fn while_exp<F: Frame>(cond: ExpKind, do_exp: ExpKind, done: Label) -> ExpKind {
    let test = Label::new();
    let body = Label::new();
    let cond = un_cx(cond);
    let do_exp = un_nx(do_exp);

    ExpKind::Nx(seq!(
        stmt!(label test);
        cond(body, done);
        stmt!(label body);
        do_exp;
        stmt!(jmp exp!(name test), test);
        stmt!(label done);
    ))
}

pub fn for_exp<F: Frame>(
    i: ExpKind,
    from: ExpKind,
    to: ExpKind,
    body: ExpKind,
    done: Label,
) -> ExpKind {
    let limit = Temp::new();
    let body_lbl = Label::new();
    let test = Label::new();
    let i = un_ex(i);

    ExpKind::Nx(seq!(
        stmt!(move i.clone(), un_ex(from));
        stmt!(move exp!(temp limit), un_ex(to));
        stmt!(label test);
        stmt!(cjmp <=, i, exp!(temp limit), body_lbl, done);
        stmt!(label body_lbl);
        stmt!(exp un_ex(body));
        stmt!(jmp exp!(name test), test);
        stmt!(label done);
    ))
}

pub fn break_exp(label: Label) -> ExpKind {
    ExpKind::Nx(stmt!(jmp exp!(name label), label))
}

pub fn let_exp(decs: ExpKind, exps: ExpKind) -> ExpKind {
    ExpKind::Ex(eseq!(
        un_nx(decs);
        un_ex(exps)
    ))
}

pub fn decs(decs: Vec<ExpKind>) -> ExpKind {
    ExpKind::Nx(decs.into_iter().fold(
        stmt!(exp exp!(const 0)),
        |stmts, stmt| seq!(stmts; un_nx(stmt)),
    ))
}

pub fn init_var<F: Frame>(access: &Access<F>, level: &Level<F>, exp: ExpKind) -> ExpKind {
    let var = level
        .frame
        .borrow()
        .exp(access.frame_access(), exp!(temp F::fp()));
    ExpKind::Nx(stmt!(move var, un_ex(exp)))
}

pub fn fn_dec<F: Frame>(body: ExpKind) -> ExpKind {
    ExpKind::Ex(eseq!(
        stmt!(move exp!(temp F::rv()), un_ex(body));
        exp!(temp F::rv())
    ))
}

impl<F: Frame> Gen<F> {
    pub fn proc_entry_exit(&mut self, level: &Rc<Level<F>>, body: ExpKind) {
        self.fragments.push(Fragment::new_procedure(
            un_nx(body),
            Rc::clone(&level.frame),
        ));
    }

    pub fn string(&mut self, symbol: Symbol) -> ExpKind {
        let label = Label::new();
        self.fragments.push(Fragment::new_string(label, symbol));
        ExpKind::Ex(exp!(name label))
    }

    pub fn into_result(self) -> Vec<Fragment<F>> {
        self.fragments
    }
}
