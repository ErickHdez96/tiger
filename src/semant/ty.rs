use super::{Semant, TResult, TranslateError, Types};
use crate::ast::TypeDec;
use crate::frame::Frame;
use crate::types::{RecordMember, TigerType};
use crate::{terr, Span};
use std::rc::Rc;

impl<F: Frame + PartialEq> Semant<F> {
    pub fn translate_type<'env>(
        &self,
        types: &'env Types,
        type_dec: &TypeDec,
    ) -> TResult<Rc<TigerType>> {
        match type_dec {
            TypeDec::Name { type_id, span, .. } => match types.get(type_id.id()) {
                Some(ty) => Ok(Rc::clone(ty)),
                None => terr!(
                    format!("`{}` is not defined", type_id.id().as_str()),
                    *span,
                    type_id.span()
                ),
            },
            TypeDec::Record { fields, span, .. } => {
                // TODO: Allow recursive records
                let mut members = vec![];

                for field in fields {
                    match types.get(field.type_id.id()) {
                        Some(ty) => members.push(RecordMember::new(field.id.id(), ty)),
                        None => {
                            return terr!(
                                format!("Type `{}` is not defined", field.type_id.id().as_str()),
                                *span,
                                field.span
                            )
                        }
                    }
                }
                Ok(Rc::new(TigerType::Record(members)))
            }
            TypeDec::Array { type_id, span, .. } => match types.get(type_id.id()) {
                Some(ty) => Ok(Rc::new(TigerType::Array(Rc::clone(&ty)))),
                None => terr!(
                    format!("Type `{}` is not defined", type_id.id().as_str()),
                    *span,
                    type_id.span()
                ),
            },
            TypeDec::Class { span, .. } => {
                terr!("Object extension is not yet built", *span, Span::new(0, 5))
            }
        }
    }
}
