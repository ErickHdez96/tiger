#![allow(clippy::too_many_arguments)]
use super::{ExpType, TResult, TranslateError, Translator, Types, Vars};
use crate::ast::{Dec, Exp, Identifier, LValue, Member};
use crate::env::Env;
use crate::types::{TigerType, VarType};
use crate::{terr, ty, Span};
use std::collections::HashSet;
use std::rc::Rc;

impl Translator {
    pub fn translate_exp(&self, vars: &Vars, types: &Types, exp: &Exp) -> TResult<ExpType> {
        match exp {
            Exp::IntegerExp { span, .. } => Ok(ExpType::new(ty!(self, int), *span)),
            Exp::StringExp { span, .. } => Ok(ExpType::new(ty!(self, str), *span)),
            Exp::NilExp { span } => Ok(ExpType::new(ty!(self, nil), *span)),
            Exp::LValue(lvalue) => {
                let value = self.translate_lvalue_exp(vars, types, lvalue)?;
                Ok(ExpType::new(value.get_type(), lvalue.span()))
            }
            Exp::Identifier(id) => match vars.get(id.id()) {
                Some(ty) => Ok(ExpType::new(ty.get_type(), id.span())),
                None => terr!(
                    format!("`{}` is not defined", id.id().as_str()),
                    id.span(),
                    id.span()
                ),
            },
            Exp::BinExp {
                op,
                left,
                right,
                span,
                op_span,
            } => {
                let left = self.translate_exp(vars, types, left)?;
                let right = self.translate_exp(vars, types, right)?;
                if left.ty.check_op_operation(&right.ty, *op) {
                    Ok(ExpType::new(ty!(self, int), *span))
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
                &cond,
                &then_branch,
                else_branch.as_ref().map(|x| x.as_ref()),
                *span,
            ),
            Exp::WhileExp { cond, do_exp, span } => {
                self.translate_while_exp(vars, types, &cond, &do_exp, *span)
            }
            Exp::UnaryExp { exp, span } => self.translate_unary_exp(vars, types, &exp, *span),
            Exp::ForExp {
                id,
                from,
                to,
                do_exp,
                span,
                ..
            } => self.translate_for_exp(vars, types, *id, &from, &to, &do_exp, *span),
            Exp::FnCall { lvalue, args, span } => {
                self.translate_fn_call(vars, types, lvalue, &args, *span)
            }
            Exp::NewExp { span, .. } => terr!(
                "Object extension is not yet built",
                *span,
                Span::new(span.offset(), 3)
            ),
            Exp::LetExp { decs, exps, span } => {
                self.translate_let_exp(vars, types, decs, exps, *span)
            }
            Exp::NewRecordExp { id, members, span } => {
                self.translate_new_record(vars, types, id, members, *span)
            }
            Exp::NewArrayExp {
                id,
                length,
                init,
                span,
            } => self.translate_new_array(vars, types, id, length, init, *span),
            Exp::AssignExp { lvalue, exp, span } => {
                let exp = self.translate_exp(vars, types, exp)?;
                match self.translate_lvalue_exp(vars, types, lvalue)? {
                    VarType::Var(v) if exp.ty.is_assignable_to(v) => {
                        Ok(ExpType::new(Rc::clone(v), *span))
                    }
                    VarType::Var(v) => terr!(
                        format!("Expected type `{}`, found `{}`", v, exp.ty),
                        *span,
                        exp.span
                    ),
                    _ => terr!("Functions cannot be assigned to", *span, lvalue.span()),
                }
            }
            Exp::Exps { exps, .. } => self.translate_exps(vars, types, exps),
            e => {
                dbg!(e);
                todo!();
            }
        }
    }

    fn translate_if_exp(
        &self,
        vars: &Vars,
        types: &Types,
        cond: &Exp,
        then_branch: &Exp,
        else_branch: Option<&Exp>,
        span: Span,
    ) -> TResult<ExpType> {
        let cond = self.translate_exp(vars, types, &cond)?;
        if !cond.ty.is_int() {
            return terr!(
                format!("Condition of `if` must be `int`, found `{}`", cond.ty),
                span,
                cond.span
            );
        }

        let then = self.translate_exp(vars, types, &then_branch)?;
        match else_branch {
            Some(e) => {
                let e = self.translate_exp(vars, types, &e)?;
                if then.ty == e.ty {
                    Ok(ExpType::new(then.ty, span))
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
            None => Ok(ExpType::new(ty!(self, unit), span)),
        }
    }

    fn translate_while_exp(
        &self,
        vars: &Vars,
        types: &Types,
        cond: &Exp,
        do_exp: &Exp,
        span: Span,
    ) -> TResult<ExpType> {
        let cond = self.translate_exp(vars, types, &cond)?;
        self.translate_exp(vars, types, &do_exp)?;

        if cond.ty.is_int() {
            Ok(ExpType::new(ty!(self, unit), span))
        } else {
            terr!(
                format!("Condition of `while` must be `int`, found `{}`", cond.ty),
                span,
                cond.span
            )
        }
    }

    fn translate_for_exp(
        &self,
        vars: &Vars,
        types: &Types,
        id: Identifier,
        from: &Exp,
        to: &Exp,
        do_exp: &Exp,
        span: Span,
    ) -> TResult<ExpType> {
        let from = self.translate_exp(vars, types, &from)?;
        let to = self.translate_exp(vars, types, &to)?;

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
        vars.insert(id.id(), VarType::Var(ty!(self, int)));
        self.translate_exp(&vars, types, do_exp)?;
        Ok(ExpType::new(ty!(self, unit), span))
    }

    fn translate_unary_exp(
        &self,
        vars: &Vars,
        types: &Types,
        exp: &Exp,
        span: Span,
    ) -> TResult<ExpType> {
        let exp = self.translate_exp(vars, types, &exp)?;

        if exp.ty.is_int() {
            Ok(ExpType::new(ty!(self, int), span))
        } else {
            terr!(
                format!("Operator `-` cannot be appliet to type `{}`", exp.ty),
                span,
                exp.span
            )
        }
    }

    fn translate_lvalue_exp<'a>(
        &self,
        vars: &'a Vars,
        types: &Types,
        lvalue: &LValue,
    ) -> TResult<&'a VarType> {
        match lvalue {
            LValue::Identifier(ident) => match vars.get(ident.id()) {
                Some(ty) => Ok(ty),
                None => terr!(
                    format!("`{}` is not defined", ident.id().as_str()),
                    ident.span(),
                    ident.span()
                ),
            },
            LValue::ArrayAccess { lvalue, exp, span } => {
                let exp = self.translate_exp(vars, types, &exp)?;
                if !exp.ty.is_int() {
                    return terr!(
                        format!("Expected `int`, found `{}`", exp.ty),
                        *span,
                        exp.span
                    );
                }

                self.translate_lvalue_exp(vars, types, &lvalue)
            }
            LValue::MemberAccess { .. } => todo!("Classes are not yet supported"),
        }
    }

    fn translate_fn_call(
        &self,
        vars: &Vars,
        types: &Types,
        lvalue: &LValue,
        args: &[Exp],
        span: Span,
    ) -> TResult<ExpType> {
        let var_name = lvalue.to_string();
        let var_span = lvalue.span();
        let func = self.translate_lvalue_exp(vars, types, &lvalue)?;
        let (params, ret_type) = match func {
            VarType::Var(v) => {
                return terr!(
                    format!("Variable {} of type `{}` is not callable", var_name, v),
                    span,
                    var_span
                )
            }
            VarType::Fn(params, ty) => (params, ty),
        };

        for (param, arg) in params.iter().zip(args.iter()) {
            let arg = self.translate_exp(vars, types, arg)?;
            if !arg.ty.is_assignable_to(param) {
                return terr!(
                    format!("Expected type `{}`, found `{}`", param, arg.ty),
                    span,
                    arg.span
                );
            }
        }
        Ok(ExpType::new(Rc::clone(ret_type), span))
    }

    fn translate_let_exp(
        &self,
        vars: &Vars,
        types: &Types,
        decs: &[Dec],
        exps: &[Exp],
        _span: Span,
    ) -> TResult<ExpType> {
        let (vars, types) = self.translate_decs(vars, types, decs)?;
        self.translate_exps(&vars, &types, exps)
    }

    fn translate_exps(&self, vars: &Vars, types: &Types, exps: &[Exp]) -> TResult<ExpType> {
        let mut last_exp = ExpType::new(ty!(self, unit), Span::new(0, 1));

        for exp in exps {
            last_exp = self.translate_exp(vars, types, exp)?;
        }

        Ok(last_exp)
    }

    fn translate_new_record(
        &self,
        vars: &Vars,
        types: &Types,
        id: &Identifier,
        members: &[Member],
        span: Span,
    ) -> TResult<ExpType> {
        let record_type = ty!(types, id.id(), span, id.span())?;

        match &**record_type {
            TigerType::Record(expected_members) => {
                let mut used = HashSet::new();
                let mut missing = HashSet::new();

                for expected_member in expected_members {
                    missing.insert(expected_member.name());
                }

                for member in members {
                    if used.contains(&member.id.id()) {
                        return terr!("Member duplicated", span, member.id.span());
                    }
                    let exp = self.translate_exp(vars, types, &member.exp)?;

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

                Ok(ExpType::new(Rc::clone(record_type), span))
            }
            ty => terr!(
                format!("Expected record type, found `{}`", ty),
                span,
                id.span()
            ),
        }
    }

    fn translate_new_array(
        &self,
        vars: &Vars,
        types: &Types,
        id: &Identifier,
        length: &Exp,
        init: &Exp,
        span: Span,
    ) -> TResult<ExpType> {
        let ty = ty!(types, id.id(), span, id.span())?;
        let length = self.translate_exp(vars, types, length)?;
        if !length.ty.is_int() {
            return terr!(
                format!("Expected `int`, found `{}`", length.ty),
                span,
                length.span
            );
        }
        let init = self.translate_exp(vars, types, init)?;

        match &**ty {
            TigerType::Array(ty) if init.ty.is_assignable_to(ty) => {
                Ok(ExpType::new(Rc::clone(ty), span))
            }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::BinOp;
    use crate::types::TigerType;
    use crate::{translate, Item, Span, Symbol, IK};

    macro_rules! item {
        ($exp:expr) => {
            Item::Exp(Box::new($exp))
        };
    }

    #[test]
    fn test_simple_exp_translations() {
        let expty = translate(item![IK![int, Symbol::intern("3"), 0, 1]])
            .expect("Could not translate expression");

        assert_eq!(
            expty,
            ExpType {
                exp: (),
                ty: ty!(int),
                span: Span::new(0, 1)
            }
        );

        let expty = translate(item![IK![str, Symbol::intern("Hello"), 0, 7]])
            .expect("Could not translate expression");

        assert_eq!(
            expty,
            ExpType {
                exp: (),
                ty: ty!(str),
                span: Span::new(0, 7)
            }
        );

        let expty = translate(item!(IK![nil, 0])).expect("Could not translate expression");

        assert_eq!(
            expty,
            ExpType {
                exp: (),
                ty: ty!(nil),
                span: Span::new(0, 3)
            }
        );
    }

    #[test]
    fn test_arithmetic_expression() {
        let l = IK![int, Symbol::intern("1"), 0, 1];
        let r = IK![int, Symbol::intern("2"), 4, 1];
        let expty =
            translate(item!(IK![+, l, r, 0, 5, 2])).expect("Could not translate expression");

        assert_eq!(
            expty,
            ExpType {
                exp: (),
                ty: ty!(int),
                span: Span::new(0, 5)
            }
        );
    }

    #[test]
    fn test_invalid_expressions() {
        let l = IK![int, Symbol::intern("1"), 0, 1];
        let r = IK![str, Symbol::intern("Hi"), 4, 4];
        let expty =
            translate(item!(IK![+, l, r, 0, 8, 2])).expect_err("Could not translate expression");

        assert_eq!(
            expty.msg,
            "Operator `+` cannot be used between types `int` and `string`"
        );

        let l = IK![str, Symbol::intern("Hi"), 0, 1];
        let r = IK![int, Symbol::intern("1"), 0, 1];
        let expty =
            translate(item!(IK![-, l, r, 0, 1, 2])).expect_err("Could not translate expression");

        assert_eq!(
            expty.msg,
            "Operator `-` cannot be used between types `string` and `int`"
        );

        let l = IK![str, Symbol::intern("Hi"), 0, 1];
        let r = IK![nil, 1];
        let expty =
            translate(item!(IK![*, l, r, 0, 1, 2])).expect_err("Could not translate expression");

        assert_eq!(
            expty.msg,
            "Operator `*` cannot be used between types `string` and `nil`"
        );

        let l = IK![int, Symbol::intern("3"), 0, 1];
        let r = IK![nil, 1];
        let expty = translate(item!(IK![BinOp::Eq, l, r, 0, 1, 2]))
            .expect_err("Could not translate expression");

        assert_eq!(
            expty.msg,
            "Operator `=` cannot be used between types `int` and `nil`"
        );
    }
}
