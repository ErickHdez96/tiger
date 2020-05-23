#![allow(clippy::too_many_arguments)]
use super::{ExpType, Semant, TResult, TranslateError, Types, Vars};
use crate::ast::{Dec, Exp, Identifier, LValue, Member};
use crate::env::Env;
use crate::frame::Frame;
use crate::temp::Label;
use crate::translate::{translators as tr, Level};
use crate::types::{TigerType, VarFnDestructured, VarType};
use crate::{terr, ty, Span};
use std::collections::HashSet;
use std::rc::Rc;

impl<F: Frame + PartialEq> Semant<F> {
    pub fn translate_exp(
        &mut self,
        vars: &Vars<F>,
        types: &Types,
        level: &Rc<Level<F>>,
        exp: &Exp,
    ) -> TResult<ExpType> {
        match exp {
            Exp::IntegerExp { value, span } => {
                Ok(ExpType::new(tr::constant(*value), ty!(self, int), *span))
            }
            Exp::StringExp { value, span } => {
                Ok(ExpType::new(self.gen.string(*value), ty!(self, str), *span))
            }
            Exp::NilExp { span } => Ok(ExpType::new(tr::constant(0), ty!(self, nil), *span)),
            Exp::LValue(lvalue) => self.translate_lvalue_exp(vars, types, level, lvalue),
            Exp::BinExp {
                op,
                left,
                right,
                span,
                op_span,
            } => {
                let left = self.translate_exp(vars, types, &level, left)?;
                let right = self.translate_exp(vars, types, level, right)?;
                if left.ty.check_op_operation(&right.ty, *op) {
                    Ok(ExpType::new(
                        tr::binary_op(*op, left.exp, right.exp),
                        ty!(self, int),
                        *span,
                    ))
                } else {
                    terr!(
                        format!(
                            "Operator `{}` cannot be used between types `{}` and `{}`",
                            op, left.ty, right.ty
                        ),
                        *span,
                        *op_span
                    )
                }
            }
            Exp::IfExp {
                cond,
                then_branch,
                else_branch,
                span,
            } => self.translate_if_exp(
                vars,
                types,
                level,
                &cond,
                &then_branch,
                else_branch.as_ref().map(|x| x.as_ref()),
                *span,
            ),
            Exp::WhileExp { cond, do_exp, span } => {
                self.translate_while_exp(vars, types, level, &cond, &do_exp, *span)
            }
            Exp::UnaryExp { exp, span } => {
                self.translate_unary_exp(vars, types, level, &exp, *span)
            }
            Exp::ForExp {
                id,
                id_escapes,
                from,
                to,
                do_exp,
                span,
            } => self.translate_for_exp(
                vars,
                types,
                level,
                *id,
                *id_escapes,
                &from,
                &to,
                &do_exp,
                *span,
            ),
            Exp::FnCall { lvalue, args, span } => {
                self.translate_fn_call(vars, types, level, lvalue, &args, *span)
            }
            Exp::NewExp { span, .. } => terr!(
                "Object extension is not yet built",
                *span,
                Span::new(span.offset(), 3)
            ),
            Exp::LetExp { decs, exps, span } => {
                self.translate_let_exp(vars, types, level, decs, exps, *span)
            }
            Exp::NewRecordExp { id, members, span } => {
                self.translate_new_record(vars, types, level, id, members, *span)
            }
            Exp::NewArrayExp {
                id,
                length,
                init,
                span,
            } => self.translate_new_array(vars, types, level, id, length, init, *span),
            Exp::AssignExp { lvalue, exp, span } => {
                let exp = self.translate_exp(vars, types, &level, exp)?;
                let lvalue = self.translate_lvalue_exp(vars, types, level, lvalue)?;
                Ok(ExpType::new(
                    tr::assignment(lvalue.exp, exp.exp),
                    lvalue.ty,
                    *span,
                ))
            }
            Exp::Exps { exps, .. } => self.translate_exps(vars, types, level, exps),
            Exp::BreakExp { span } => match self.loop_labels.last() {
                Some(l) => Ok(ExpType::new(tr::break_exp(*l), ty!(self, unit), *span)),
                None => terr!("`break` is not inside of a loop", *span, *span),
            },
        }
    }

    fn translate_if_exp(
        &mut self,
        vars: &Vars<F>,
        types: &Types,
        level: &Rc<Level<F>>,
        cond: &Exp,
        then_branch: &Exp,
        else_branch: Option<&Exp>,
        span: Span,
    ) -> TResult<ExpType> {
        let cond = self.translate_exp(vars, types, &level, &cond)?;
        if !cond.ty.is_int() {
            return terr!(
                format!("Condition of `if` must be `int`, found `{}`", cond.ty),
                span,
                cond.span
            );
        }

        let then = self.translate_exp(vars, types, &level, &then_branch)?;
        match else_branch {
            Some(e) => {
                let e = self.translate_exp(vars, types, level, &e)?;
                if then.ty == e.ty {
                    Ok(ExpType::new(
                        tr::if_exp(cond.exp, then.exp, e.exp),
                        then.ty,
                        span,
                    ))
                } else {
                    terr!(
                        format!(
                            "Else branch expected to have type `{}`, found `{}`",
                            then.ty, e.ty
                        ),
                        span,
                        e.span
                    )
                }
            }
            None => Ok(ExpType::new(
                tr::if_stmt(cond.exp, then.exp),
                ty!(self, unit),
                span,
            )),
        }
    }

    fn translate_while_exp(
        &mut self,
        vars: &Vars<F>,
        types: &Types,
        level: &Rc<Level<F>>,
        cond: &Exp,
        do_exp: &Exp,
        span: Span,
    ) -> TResult<ExpType> {
        let cond = self.translate_exp(vars, types, &level, &cond)?;
        let end_label = Label::new();
        self.loop_labels.push(end_label);
        let do_exp = self.translate_exp(vars, types, level, &do_exp)?;
        self.loop_labels.pop();

        if cond.ty.is_int() {
            Ok(ExpType::new(
                tr::while_exp::<F>(cond.exp, do_exp.exp, end_label),
                ty!(self, unit),
                span,
            ))
        } else {
            terr!(
                format!("Condition of `while` must be `int`, found `{}`", cond.ty),
                span,
                cond.span
            )
        }
    }

    fn translate_for_exp(
        &mut self,
        vars: &Vars<F>,
        types: &Types,
        level: &Rc<Level<F>>,
        id: Identifier,
        id_escapes: bool,
        from: &Exp,
        to: &Exp,
        do_exp: &Exp,
        span: Span,
    ) -> TResult<ExpType> {
        let from = self.translate_exp(vars, types, &level, &from)?;
        let to = self.translate_exp(vars, types, &level, &to)?;

        if !from.ty.is_int() {
            return terr!(
                format!("Expected type `int`, found `{}`", from.ty),
                span,
                from.span
            );
        }
        if !to.ty.is_int() {
            return terr!(
                format!("Expected type `int`, found `{}`", to.ty),
                span,
                to.span
            );
        }

        let mut vars = Env::with_parent(vars);
        let var_access = level.allocate_local(id_escapes);
        let i = tr::simple_var(&var_access, &level);
        let new_var = VarType::new_var(ty!(self, int), var_access);
        vars.insert(id.id(), new_var);
        let end_label = Label::new();
        self.loop_labels.push(end_label);
        let do_exp = self.translate_exp(&vars, types, &level, do_exp)?;
        self.loop_labels.pop();
        Ok(ExpType::new(
            tr::for_exp::<F>(i, from.exp, to.exp, do_exp.exp, end_label),
            ty!(self, unit),
            span,
        ))
    }

    fn translate_unary_exp(
        &mut self,
        vars: &Vars<F>,
        types: &Types,
        level: &Rc<Level<F>>,
        exp: &Exp,
        span: Span,
    ) -> TResult<ExpType> {
        let exp = self.translate_exp(vars, types, level, &exp)?;

        if exp.ty.is_int() {
            Ok(ExpType::new(tr::unary_op(exp.exp), ty!(self, int), span))
        } else {
            terr!(
                format!("Operator `-` cannot be appliet to type `{}`", exp.ty),
                span,
                exp.span
            )
        }
    }

    fn translate_lvalue_exp(
        &mut self,
        vars: &Vars<F>,
        types: &Types,
        level: &Rc<Level<F>>,
        lvalue: &LValue,
    ) -> TResult<ExpType> {
        match lvalue {
            LValue::Identifier(ident) => match vars.get(ident.id()) {
                Some(ty) => match ty {
                    VarType::Var { ty, access } => Ok(ExpType::new(
                        tr::simple_var(access, level),
                        Rc::clone(ty),
                        lvalue.span(),
                    )),
                    VarType::Fn { .. } => terr!(
                        format!("Expected a variable, found function `{}`", lvalue),
                        lvalue.span(),
                        lvalue.span()
                    ),
                },
                None => terr!(
                    format!("`{}` is not defined", ident.id().as_str()),
                    ident.span(),
                    ident.span()
                ),
            },
            LValue::ArrayAccess { lvalue, exp, span } => {
                let exp = self.translate_exp(vars, types, &level, &exp)?;
                if !exp.ty.is_int() {
                    return terr!(
                        format!("Expected `int`, found `{}`", exp.ty),
                        *span,
                        exp.span
                    );
                }

                let lvalue = self.translate_lvalue_exp(vars, types, level, &lvalue)?;
                match lvalue.ty.as_ref() {
                    TigerType::Array(ty) => Ok(ExpType::new(
                        tr::array_access::<F>(lvalue.exp, exp.exp),
                        Rc::clone(ty),
                        lvalue.span,
                    )),
                    ty => terr!(
                        format!("Expected an array, found `{}`", ty),
                        lvalue.span,
                        lvalue.span
                    ),
                }
            }
            LValue::MemberAccess {
                lvalue,
                member,
                span,
            } => {
                let lvalue = self.translate_lvalue_exp(vars, types, level, lvalue)?;
                match lvalue.ty.as_ref() {
                    TigerType::Record(members) => {
                        for (i, mem) in members.iter().enumerate() {
                            if member.id() == mem.name() {
                                return Ok(ExpType::new(
                                    tr::record_access::<F>(lvalue.exp, i),
                                    Rc::clone(mem.ty()),
                                    *span,
                                ));
                            }
                        }
                        terr!(
                            format!(
                                "Member `{}` does not exist in type `{}`",
                                member.id().as_str(),
                                lvalue.ty
                            ),
                            *span,
                            *span
                        )
                    }
                    ty => terr!(format!("Expected a record, found `{}`", ty), *span, *span),
                }
            }
        }
    }

    fn translate_fn_lvalue_exp<'env>(
        &mut self,
        vars: &'env Vars<F>,
        lvalue: &LValue,
    ) -> TResult<VarFnDestructured<'env, F>> {
        match lvalue {
            LValue::Identifier(ident) => match vars.get(ident.id()) {
                Some(ty) => match ty {
                    VarType::Fn {
                        formals,
                        ty,
                        level,
                        label,
                    } => Ok((formals, ty, level, *label)),
                    VarType::Var { .. } => terr!(
                        format!("Expected a function, found `{}`", lvalue),
                        ident.span(),
                        ident.span()
                    ),
                },
                None => terr!(
                    format!("`{}` is not defined", ident.id().as_str()),
                    ident.span(),
                    ident.span()
                ),
            },
            LValue::ArrayAccess { span, .. } | LValue::MemberAccess { span, .. } => terr!(
                format!("Expected a function, found `{}`", lvalue),
                *span,
                *span
            ),
        }
    }

    fn translate_fn_call(
        &mut self,
        vars: &Vars<F>,
        types: &Types,
        level: &Rc<Level<F>>,
        lvalue: &LValue,
        args: &[Exp],
        span: Span,
    ) -> TResult<ExpType> {
        let (params, ret_type, fn_level, label) = self.translate_fn_lvalue_exp(vars, &lvalue)?;

        if params.len() != args.len() {
            return terr!(
                format!(
                    "Function {} expectes {} arguments, {} given",
                    lvalue,
                    params.len(),
                    args.len()
                ),
                span,
                span
            );
        }

        let mut fn_args = Vec::with_capacity(args.len());
        for (param, arg) in params.iter().zip(args.iter()) {
            let arg = self.translate_exp(vars, types, &level, arg)?;
            if !arg.ty.is_assignable_to(param) {
                return terr!(
                    format!("Expected type `{}`, found `{}`", param, arg.ty),
                    span,
                    arg.span
                );
            }
            fn_args.push(arg.exp);
        }
        Ok(ExpType::new(
            tr::fn_call(label, fn_args, fn_level, level),
            Rc::clone(ret_type),
            span,
        ))
    }

    fn translate_let_exp(
        &mut self,
        vars: &Vars<F>,
        types: &Types,
        level: &Rc<Level<F>>,
        decs: &[Dec],
        exps: &[Exp],
        span: Span,
    ) -> TResult<ExpType> {
        let (vars, types, decs) = self.translate_decs(vars, types, &level, decs)?;
        let exps = self.translate_exps(&vars, &types, level, exps)?;
        Ok(ExpType::new(tr::let_exp(decs, exps.exp), exps.ty, span))
    }

    fn translate_exps(
        &mut self,
        vars: &Vars<F>,
        types: &Types,
        level: &Rc<Level<F>>,
        exps: &[Exp],
    ) -> TResult<ExpType> {
        // nop
        let mut last_exp = ExpType::new(tr::constant(0), ty!(self, unit), Span::new(0, 1));
        let mut curr_exp = last_exp.exp;

        for exp in exps {
            last_exp = self.translate_exp(vars, types, &level, exp)?;
            curr_exp = tr::exps(curr_exp, last_exp.exp);
        }

        last_exp.exp = curr_exp;
        Ok(last_exp)
    }

    fn translate_new_record(
        &mut self,
        vars: &Vars<F>,
        types: &Types,
        level: &Rc<Level<F>>,
        id: &Identifier,
        members: &[Member],
        span: Span,
    ) -> TResult<ExpType> {
        let record_type = ty!(types, id.id(), span, id.span())?;

        match &**record_type {
            TigerType::Record(expected_members) => {
                let mut used = HashSet::new();
                let mut missing = HashSet::new();
                let mut exps = vec![];

                for expected_member in expected_members {
                    missing.insert(expected_member.name());
                }

                for member in members {
                    if used.contains(&member.id.id()) {
                        return terr!("Member duplicated", span, member.id.span());
                    }
                    let exp = self.translate_exp(vars, types, &level, &member.exp)?;

                    match expected_members.iter().find(|m| m.name() == member.id.id()) {
                        Some(expected_member) if exp.ty.is_assignable_to(expected_member.ty()) => {
                            used.insert(member.id.id());
                            missing.remove(&member.id.id());
                        }
                        Some(expected_member) => {
                            return terr!(
                                format!(
                                    "Expected type `{}`, found `{}`",
                                    expected_member.ty(),
                                    exp.ty
                                ),
                                span,
                                exp.span
                            );
                        }
                        None => {
                            return terr!(
                                format!(
                                    "Member `{}` does not exist in `{}`",
                                    member.id.id().as_str(),
                                    id.id().as_str()
                                ),
                                span,
                                member.id.span()
                            )
                        }
                    }
                    exps.push(exp.exp);
                }

                if let Some(expected) = missing.iter().next() {
                    let error_span = if !members.is_empty() {
                        members[0].span.extend(members.iter().last().unwrap().span)
                    } else {
                        span
                    };

                    return terr!(
                        format!("Missing member `{}`", expected.as_str()),
                        span,
                        error_span
                    );
                }

                Ok(ExpType::new(
                    tr::record_creation::<F>(exps),
                    Rc::clone(record_type),
                    span,
                ))
            }
            ty => terr!(
                format!("Expected record type, found `{}`", ty),
                span,
                id.span()
            ),
        }
    }

    fn translate_new_array(
        &mut self,
        vars: &Vars<F>,
        types: &Types,
        level: &Rc<Level<F>>,
        id: &Identifier,
        length: &Exp,
        init: &Exp,
        span: Span,
    ) -> TResult<ExpType> {
        let ty = ty!(types, id.id(), span, id.span())?;
        let length = self.translate_exp(vars, types, &level, length)?;
        if !length.ty.is_int() {
            return terr!(
                format!("Expected `int`, found `{}`", length.ty),
                span,
                length.span
            );
        }
        let init = self.translate_exp(vars, types, level, init)?;

        match &**ty {
            TigerType::Array(arr_ty) if init.ty.is_assignable_to(arr_ty) => Ok(ExpType::new(
                tr::array_creation::<F>(length.exp, init.exp),
                Rc::clone(ty),
                span,
            )),
            TigerType::Array(ty) => terr!(
                format!("Expected type `{}`, found `{}`", ty, init.ty),
                span,
                init.span
            ),
            ty => terr!(
                format!("Expected array type, found `{}`", ty),
                span,
                id.span()
            ),
        }
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::ast::BinOp;
//     use crate::frame::{X86_64, Fragment};
//     use crate::ir;
//     use crate::translate::ExpKind;
//     use crate::types::TigerType;
//     use crate::{translate, Item, Span, Symbol, IK};
//
//     macro_rules! item {
//         ($exp:expr) => {
//             Item::Exp(Box::new($exp))
//         };
//     }
//
//     fn t(item: Item) -> TResult<Vec<Fragment<X86_64>>> {
//         translate::<X86_64>(item)
//     }
//
//     #[test]
//     fn test_simple_exp_translations() {
//         let expty = t(item![IK![int, 3, 0, 1]]).expect("Could not translate expression");
//
//         assert_eq!(
//             expty,
//             ExpType {
//                 exp: ExpKind::Ex(Box::new(ir::Exp::Const(3))),
//                 ty: ty!(int),
//                 span: Span::new(0, 1)
//             }
//         );
//
//         let expty = t(item![IK![str, Symbol::intern("Hello"), 0, 7]])
//             .expect("Could not translate expression");
//
//         match expty.exp {
//             ExpKind::Ex(ex) => match ex.as_ref() {
//                 ir::Exp::Name(_) => {}
//                 s => panic!("Expected a label: {:?}", s),
//             },
//             s => panic!("Expected an ex: {:?}", s),
//         }
//
//         assert_eq!(expty.ty, ty!(str));
//
//         assert_eq!(expty.span, Span::new(0, 7));
//
//         let expty = t(item!(IK![nil, 0])).expect("Could not translate expression");
//
//         assert_eq!(
//             expty,
//             ExpType {
//                 exp: ExpKind::Ex(Box::new(ir::Exp::Const(0))),
//                 ty: ty!(nil),
//                 span: Span::new(0, 3)
//             }
//         );
//     }
//
//     #[test]
//     fn test_arithmetic_expression() {
//         let l = IK![int, 1, 0, 1];
//         let r = IK![int, 2, 4, 1];
//         let expty = t(item!(IK![+, l, r, 0, 5, 2])).expect("Could not translate expression");
//
//         assert_eq!(
//             expty,
//             ExpType {
//                 exp: ExpKind::Ex(Box::new(ir::Exp::BinOp(
//                     ir::BinOp::Plus,
//                     Box::new(ir::Exp::Const(1)),
//                     Box::new(ir::Exp::Const(2)),
//                 ))),
//                 ty: ty!(int),
//                 span: Span::new(0, 5)
//             }
//         );
//     }
//
//     #[test]
//     fn test_invalid_expressions() {
//         let l = IK![int, 1, 0, 1];
//         let r = IK![str, Symbol::intern("Hi"), 4, 4];
//         let expty = t(item!(IK![+, l, r, 0, 8, 2])).expect_err("Could not translate expression");
//
//         assert_eq!(
//             expty.msg,
//             "Operator `+` cannot be used between types `int` and `string`"
//         );
//
//         let l = IK![str, Symbol::intern("Hi"), 0, 1];
//         let r = IK![int, 1, 0, 1];
//         let expty = t(item!(IK![-, l, r, 0, 1, 2])).expect_err("Could not translate expression");
//
//         assert_eq!(
//             expty.msg,
//             "Operator `-` cannot be used between types `string` and `int`"
//         );
//
//         let l = IK![str, Symbol::intern("Hi"), 0, 1];
//         let r = IK![nil, 1];
//         let expty = t(item!(IK![*, l, r, 0, 1, 2])).expect_err("Could not translate expression");
//
//         assert_eq!(
//             expty.msg,
//             "Operator `*` cannot be used between types `string` and `nil`"
//         );
//
//         let l = IK![int, 3, 0, 1];
//         let r = IK![nil, 1];
//         let expty =
//             t(item!(IK![BinOp::Eq, l, r, 0, 1, 2])).expect_err("Could not translate expression");
//
//         assert_eq!(
//             expty.msg,
//             "Operator `=` cannot be used between types `int` and `nil`"
//         );
//     }
// }
