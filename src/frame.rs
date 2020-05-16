mod x86_64;

use crate::temp::Label;
use std::fmt::Debug;
pub use x86_64::X86_64;

pub trait Frame {
    type Access: Debug + Copy + Clone;

    fn new(name: Label, formals: &[bool]) -> Self;
    fn name(&self) -> Label;
    fn formals(&self) -> &[Self::Access];
    fn allocate_local(&mut self, escapes: bool) -> Self::Access;
}
