use super::{Semant, TResult, TranslateError, Types, Vars};
use crate::ast::{Dec, TypeDec, VarDec};
use crate::env::Env;
use crate::frame::Frame;
use crate::temp::Label;
use crate::translate::{translators as tr, ExpKind, Level};
use crate::types::VarType;
use crate::{terr, ty, Span};
use std::rc::Rc;

impl<F: Frame + PartialEq> Semant<F> {
    pub fn translate_decs<'env>(
        &mut self,
        vars: &'env Vars<F>,
        types: &'env Types,
        level: &Rc<Level<F>>,
        decs: &[Dec],
    ) -> TResult<(Vars<'env, F>, Types<'env>, ExpKind)> {
        let mut vars = Env::with_parent(vars);
        let mut types = Env::with_parent(types);
        let mut stmts = vec![];

        for dec in decs {
            let dec = self.translate_dec(&mut vars, &mut types, &level, dec)?;
            if let Some(dec) = dec {
                stmts.push(dec);
            }
        }

        Ok((vars, types, tr::decs(stmts)))
    }

    fn translate_dec<'env>(
        &mut self,
        vars: &'env mut Vars<F>,
        types: &mut Types,
        level: &Rc<Level<F>>,
        dec: &Dec,
    ) -> TResult<Option<ExpKind>> {
        match dec {
            Dec::VarDec(var_dec) => self.translate_var_dec(vars, types, level, var_dec),
            Dec::Class { span, .. } => terr!(
                "Object extesion is not yet built",
                *span,
                Span::new(span.offset(), 5)
            ),
            Dec::TypeDec(type_dec) => self.translate_type_dec(types, type_dec).and(Ok(None)),
            _ => todo!("{}", dec),
        }
    }

    fn translate_var_dec<'env>(
        &mut self,
        vars: &'env mut Vars<F>,
        types: &mut Types,
        level: &Rc<Level<F>>,
        var_dec: &VarDec,
    ) -> TResult<Option<ExpKind>> {
        match var_dec {
            VarDec::Var {
                id,
                exp,
                opt_type,
                span,
                escapes,
            } => {
                let exp = self.translate_exp(vars, types, &level, exp)?;
                let ty = match opt_type {
                    Some(expected_ty) => match types.get(expected_ty.id()) {
                        Some(ty) if !exp.ty.is_assignable_to(ty) => terr!(
                            format!(
                                "Expected type `{}`, found `{}`",
                                expected_ty.id().as_str(),
                                exp.ty
                            ),
                            *span,
                            exp.span
                        ),
                        Some(ty) => Ok(ty),
                        None => terr!(
                            format!("Type `{}` is not defined", expected_ty.id().as_str()),
                            *span,
                            expected_ty.span()
                        ),
                    },
                    None if exp.ty.is_nil() => terr!(
                        "Cannot infer type for `nil`, a type annotation is necessary",
                        *span,
                        exp.span
                    ),
                    None => Ok(&exp.ty),
                }?;
                let access = level.allocate_local(*escapes);
                let var = tr::init_var::<F>(&access, &level, exp.exp);
                vars.insert(id.id(), VarType::new_var(Rc::clone(ty), access));
                Ok(Some(var))
            }
            VarDec::Fn {
                id,
                params,
                ret_type,
                body,
                span,
            } => {
                let mut formals = vec![];
                let mut new_vars = vec![];
                let mut formal_escapes = vec![];

                for param in params {
                    match types.get(param.type_id.id()) {
                        Some(ty) => {
                            new_vars.push((param.id.id(), param.escapes, Rc::clone(ty)));
                            formals.push(Rc::clone(ty));
                            formal_escapes.push(param.escapes);
                        }
                        None => {
                            return terr!(
                                format!("Type `{}` is not defined", param.type_id.id().as_str()),
                                *span,
                                param.type_id.span()
                            )
                        }
                    }
                }

                let ret_type = match ret_type {
                    Some(ret_ty) => match types.get(ret_ty.id()) {
                        Some(ty) => Rc::clone(ty),
                        None => {
                            return terr!(
                                format!("Type `{}` is not defined", ret_ty.id().as_str()),
                                *span,
                                ret_ty.span()
                            )
                        }
                    },
                    None => ty!(self, unit),
                };
                vars.insert(
                    id.id(),
                    VarType::new_fn(formals, ret_type, &level, Label::new()),
                );
                let level = Level::new(&level, Label::new(), &formal_escapes);
                let mut body_vars = Env::with_parent(vars);

                for (id, escapes, ty) in new_vars {
                    body_vars.insert(id, VarType::new_var(ty, level.allocate_local(escapes)));
                }

                let body = self.translate_exp(&body_vars, types, &level, body)?;
                self.gen.proc_entry_exit(&level, body.exp);
                Ok(None)
            }
            VarDec::Primitive {
                id,
                params,
                ret_type,
                span,
            } => {
                let mut formals = vec![];

                for param in params {
                    match types.get(param.type_id.id()) {
                        Some(ty) => formals.push(Rc::clone(ty)),
                        None => {
                            return terr!(
                                format!("Type `{}` is not defined", param.type_id.id().as_str()),
                                *span,
                                param.type_id.span()
                            )
                        }
                    }
                }

                let ret_type = match ret_type {
                    Some(ret_ty) => match types.get(ret_ty.id()) {
                        Some(ty) => Rc::clone(ty),
                        None => {
                            return terr!(
                                format!("Type `{}` is not defined", ret_ty.id().as_str()),
                                *span,
                                ret_ty.span()
                            )
                        }
                    },
                    None => ty!(self, unit),
                };

                vars.insert(
                    id.id(),
                    VarType::new_fn(formals, ret_type, level, Label::with_name(id.id())),
                );

                Ok(None)
            }
        }
    }

    fn translate_type_dec(&mut self, types: &mut Types, type_dec: &TypeDec) -> TResult<()> {
        let ty = self.translate_type(types, type_dec)?;

        match type_dec {
            TypeDec::Name { id, .. } | TypeDec::Array { id, .. } | TypeDec::Record { id, .. } => {
                types.insert(id.id(), ty)
            }
            TypeDec::Class { span, .. } => {
                return terr!(
                    "Object extension is not yet built",
                    *span,
                    Span::new(span.offset(), 5)
                )
            }
        }

        Ok(())
    }
}
