use crate::frame::Frame;
use crate::temp::Label;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Access<F: Frame>(Level<F>, F::Access);

#[derive(Debug)]
pub struct InnerLevel<F: Frame> {
    frame: F,
    parent: Option<Level<F>>,
}

pub type Level<F> = Rc<RefCell<InnerLevel<F>>>;

impl<F: Frame> InnerLevel<F> {
    pub fn new(parent: Level<F>, name: Label, formals: &[bool]) -> Level<F> {
        let mut new_formals = Vec::with_capacity(formals.len());
        new_formals.push(true);
        new_formals.extend(formals);

        Rc::new(RefCell::new(Self {
            frame: F::new(name, &new_formals),
            parent: Some(parent),
        }))
    }

    #[allow(dead_code)]
    pub fn formals(level: Level<F>) -> Vec<Access<F>> {
        level
            .borrow()
            .frame
            .formals()
            .iter()
            .map(|access| Access::<F>(Rc::clone(&level), *access))
            .collect()
    }

    pub fn allocate_local(level: Level<F>, escapes: bool) -> Access<F> {
        let new_access = level.borrow_mut().frame.allocate_local(escapes);
        Access(level, new_access)
    }
}

pub fn outermost<F: Frame>() -> Level<F> {
    Rc::new(RefCell::new(InnerLevel {
        frame: F::new(Label::new(), &[]),
        parent: None,
    }))
}
