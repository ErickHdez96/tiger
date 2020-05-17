use crate::ast::{Dec, Exp, LValue, VarDec};
use crate::env::Env;
use crate::Item;
use std::cell::RefCell;

type EscapeEnv<'a, 'b> = Env<'a, (usize, RefCell<&'b mut bool>)>;

/// Find all escaping variable declarations.
pub fn find_escape(item: &mut Item) {
    let env = Env::new();

    match item {
        Item::Exp(ref mut exp) => traverse_exp(&env, 0, exp),
        Item::Decs(ref mut decs) => {
            traverse_decs(&env, 0, decs);
        }
    }
}

fn traverse_exp<'a, 'b>(env: &EscapeEnv<'a, 'b>, depth: usize, exp: &'b mut Exp) {
    match exp {
        Exp::LetExp {
            ref mut decs,
            ref mut exps,
            ..
        } => {
            let env = traverse_decs(&env, depth, decs);
            for exp in exps {
                traverse_exp(&env, depth, exp);
            }
        }
        Exp::IfExp {
            ref mut cond,
            ref mut then_branch,
            ref mut else_branch,
            ..
        } => {
            traverse_exp(&env, depth, cond);
            traverse_exp(&env, depth, then_branch);
            if let Some(e) = else_branch {
                traverse_exp(&env, depth, e);
            }
        }
        Exp::WhileExp { cond, do_exp, .. } => {
            traverse_exp(&env, depth, cond);
            traverse_exp(&env, depth, do_exp);
        }
        Exp::ForExp {
            id,
            ref mut id_escapes,
            from,
            to,
            do_exp,
            ..
        } => {
            let mut env = Env::with_parent(&env);
            env.insert(id.id(), (depth, RefCell::new(id_escapes)));
            traverse_exp(&env, depth, from);
            traverse_exp(&env, depth, to);
            traverse_exp(&env, depth, do_exp);
        }
        Exp::NewArrayExp { length, init, .. } => {
            traverse_exp(&env, depth, length);
            traverse_exp(&env, depth, init);
        }
        Exp::NewRecordExp { members, .. } => {
            for member in members {
                traverse_exp(&env, depth, &mut member.exp);
            }
        }
        Exp::Exps { ref mut exps, .. } => {
            for exp in exps.iter_mut() {
                traverse_exp(&env, depth, exp);
            }
        }
        Exp::AssignExp {
            ref mut lvalue,
            ref mut exp,
            ..
        } => {
            traverse_lvalue(&env, depth, lvalue);
            traverse_exp(&env, depth, exp);
        }
        Exp::FnCall { ref mut args, .. } => {
            for arg in args.iter_mut() {
                traverse_exp(&env, depth, arg);
            }
        }
        Exp::BinExp {
            ref mut left,
            ref mut right,
            ..
        } => {
            traverse_exp(&env, depth, left);
            traverse_exp(&env, depth, right);
        }
        Exp::UnaryExp { ref mut exp, .. } => traverse_exp(&env, depth, exp),
        Exp::LValue(lvalue) => traverse_lvalue(env, depth, lvalue),
        _ => {}
    }
}

fn traverse_lvalue<'a, 'b>(env: &EscapeEnv<'a, 'b>, depth: usize, lvalue: &'b mut LValue) {
    match lvalue {
        LValue::Identifier(id) => {
            if let Some((d, escapes)) = env.get(id.id()) {
                if depth > *d {
                    **escapes.borrow_mut() = true;
                }
            }
        }
        LValue::ArrayAccess {
            ref mut lvalue,
            ref mut exp,
            ..
        } => {
            traverse_exp(&env, depth, exp);
            traverse_lvalue(&env, depth, lvalue);
        }
        LValue::MemberAccess { .. } => {}
    }
}

fn traverse_decs<'a, 'b>(
    env: &'a EscapeEnv<'a, 'b>,
    depth: usize,
    decs: &'b mut [Dec],
) -> EscapeEnv<'a, 'b> {
    let mut env = Env::with_parent(&env);

    for dec in decs {
        if let Dec::VarDec(v) = dec {
            match v.as_mut() {
                VarDec::Var {
                    id,
                    ref mut escapes,
                    ..
                } => {
                    env.insert(id.id(), (depth, RefCell::new(escapes)));
                }
                VarDec::Fn { params, body, .. } => {
                    for param in params {
                        env.insert(param.id.id(), (depth, RefCell::new(&mut param.escapes)));
                    }
                    traverse_exp(&env, depth + 1, body.as_mut());
                }
                _ => {}
            }
        }
    }

    env
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse, tokenize};

    #[test]
    fn test_single_scape() {
        let input = r"
        let
            var a := 1
            primitive print_int(n: int)
            function print_a() = print_int(a)
        in
            print_a()
        end
        ";
        let mut item = parse(tokenize(&input).0).0.expect("Could not parse input");
        find_escape(&mut item);

        match item {
            Item::Exp(e) => match e.as_ref() {
                Exp::LetExp { decs, .. } => {
                    assert!(!decs.is_empty());
                    match &decs[0] {
                        Dec::VarDec(v) => match v.as_ref() {
                            VarDec::Var { id, escapes, .. } => {
                                // Assert variable a escapes
                                assert_eq!(
                                    *escapes,
                                    true,
                                    "Expected variable {} to escape",
                                    id.id().as_str()
                                );
                            }
                            v => panic!("Parsed wrong declaration: {:?}", v),
                        },
                        d => panic!("Parsed wrong declaration: {:?}", d),
                    }
                }
                e => panic!("Parsed wrong expression: {:?}", e),
            },
            i => panic!("Parsed wrong item: {:?}", i),
        }
    }
}
