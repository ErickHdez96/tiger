//! # Canon
//!
//! This modules rewrites an [`ir`] tree into a canonical form.
//!
//! A canonical tree has the following properties:
//!
//!  * No [`Stmt::Seq`] or [`Exp::Eseq`]
//!  * The parent of each [`Exp::Call`] is either [`Exp`] or [`Stmt::Move`]([`Exp::Temp` t, ..).
#![allow(dead_code)]
#![allow(clippy::vec_box)]
use crate::ir::{Exp, Stmt};
use crate::temp::Label;
use crate::temp::Temp;
use crate::{exp, seq, stmt, Symbol};

/// Remove Eseqs and move Calls to top level.
pub fn linearize(stmt: Stmt) -> Vec<Box<Stmt>> {
    linear(do_stmt(stmt), vec![])
}

/// Group statements into sequences of straight-line code.
pub fn basic_blocks(stmts: Vec<Box<Stmt>>) -> (Vec<Vec<Box<Stmt>>>, Label) {
    let done_label = Label::with_name(Symbol::intern("done"));

    (BlocksBuilder::new(stmts, done_label).build(), done_label)
}

#[derive(Debug)]
struct BlocksBuilder {
    done_label: Label,
    stmts: Vec<Box<Stmt>>,
    blocks: Vec<Vec<Box<Stmt>>>,
}

impl BlocksBuilder {
    fn new(stmts: Vec<Box<Stmt>>, done_label: Label) -> Self {
        Self {
            done_label,
            stmts,
            blocks: vec![],
        }
    }

    fn build(mut self) -> Vec<Vec<Box<Stmt>>> {
        let mut stmts = self.stmts.into_iter().peekable();
        let mut previous_label = None;

        'outer: loop {
            let start = match previous_label.take() {
                Some(label) => label,
                None => stmts
                    .peek()
                    .and_then(|s| match s.as_ref() {
                        Stmt::Label(label) => Some(stmt!(label * label)),
                        _ => None,
                    })
                    .unwrap_or_else(|| stmt!(label)),
            };
            let mut block = vec![start];

            loop {
                let next = match stmts.next() {
                    Some(stmt) => stmt,
                    None => {
                        block.push(stmt!(jmp exp!(name self.done_label), self.done_label));
                        self.blocks.push(block);
                        break 'outer;
                    }
                };

                match next.as_ref() {
                    Stmt::Label(label) => {
                        if block.len() == 1 {
                            block[0] = next;
                        } else {
                            block.push(stmt!(jmp exp!(name *label), *label));
                            previous_label = Some(next);
                            break;
                        }
                    }
                    Stmt::Jump(_, _) | Stmt::CJump { .. } => {
                        block.push(next);
                        break;
                    }
                    _ => block.push(next),
                }
            }

            self.blocks.push(block);
        }

        self.blocks
    }
}

#[derive(Debug)]
struct Trace(Vec<Vec<Box<Stmt>>>, bool);

impl Trace {
    fn is_marked(&self) -> bool {
        self.1
    }

    fn into_blocks(self) -> Vec<Vec<Box<Stmt>>> {
        self.0
    }
}

/// Get the label from a block.
fn get_label(block: &[Box<Stmt>]) -> Label {
    match block[0].as_ref() {
        Stmt::Label(label) => *label,
        _ => panic!("Compiler bug: The given block does not start with a label"),
    }
}

fn get_jumping_labels(block: &[Box<Stmt>]) -> Option<Vec<Label>> {
    let last = block
        .iter()
        .last()
        .expect("Block does not end in a jump statement");
    match last.as_ref() {
        Stmt::Jump(_, labels) => Some(labels.clone()),
        Stmt::CJump {
            r#true, r#false, ..
        } => Some(vec![*r#true, *r#false]),
        _ => None,
    }
}

fn get_cjmp_labels(block: &[Box<Stmt>]) -> Option<(Label, Label)> {
    let last = block
        .iter()
        .last()
        .expect("Block does not end in a jump statement");
    match last.as_ref() {
        Stmt::CJump {
            r#true, r#false, ..
        } => Some((*r#true, *r#false)),
        _ => None,
    }
}

fn find_block_starting_with_label(blocks: &[Vec<Box<Stmt>>], label: Label) -> Option<usize> {
    for (i, block) in blocks.iter().enumerate() {
        if get_label(block) == label {
            return Some(i);
        }
    }
    None
}

/// Order blocks so that every Cjmp is followed by its `False` label.
pub fn trace_schedule(mut blocks: Vec<Vec<Box<Stmt>>>, done_label: Label) -> Vec<Box<Stmt>> {
    let mut start = 0;
    let mut pos;
    let mut traces = vec![];
    let mut marked_blocks = vec![false; blocks.len()];

    while start < blocks.len() {
        let mut trace = vec![];
        let mut block = &blocks[start];
        pos = start;
        // Find the next unmarked block
        start = marked_blocks
            .iter()
            .enumerate()
            .find(|(_, b)| !(**b))
            .map(|r| r.0)
            .unwrap_or_else(|| blocks.len());
        while !marked_blocks[pos] {
            marked_blocks[pos] = true;
            trace.push(pos);
            if let Some(labels) = get_jumping_labels(block) {
                for label in labels {
                    match find_block_starting_with_label(&blocks[start..], label) {
                        Some(i) if !marked_blocks[i] => {
                            pos = i;
                            block = &blocks[pos];
                        }
                        _ => {}
                    }
                }
            }
        }
        traces.push(trace);
    }

    fix_cjmps(&traces, &mut blocks);

    let stmts_count = blocks.iter().fold(0, |acc, block| acc + block.len());
    let mut stmts: Vec<Box<Stmt>> = Vec::with_capacity(stmts_count + 1);
    for trace in traces {
        for block_pos in trace {
            stmts.extend(std::mem::take(&mut blocks[block_pos]))
        }
    }
    stmts.push(stmt!(label done_label));

    stmts
}

fn fix_cjmps(traces: &[Vec<usize>], blocks: &mut Vec<Vec<Box<Stmt>>>) {
    for trace in traces.iter() {
        for &i in trace {
            if let Some((r#true, r#false)) = get_cjmp_labels(&blocks[i]) {
                match blocks.get(i + 1) {
                    // Any cjmp followed by its true label, change the labels, and invert the
                    // operator.
                    Some(next_block) if get_label(next_block) == r#true => {
                        match unsafe {
                            blocks
                                .get_unchecked_mut(i)
                                .iter_mut()
                                .last()
                                .unwrap()
                                .as_mut()
                        } {
                            Stmt::CJump { ref mut op, .. } => *op = op.inverse(),
                            _ => unreachable!(),
                        }
                        // Find the block starting with the false label.
                        let false_label_block =
                            find_block_starting_with_label(&blocks, r#false).unwrap();
                        let leftmost_block = std::cmp::min(false_label_block, i + 1);
                        let rightmost_block = std::cmp::max(false_label_block, i + 1);
                        let (left, right) = blocks.split_at_mut(leftmost_block + 1);
                        // Swap the labels
                        std::mem::swap(
                            &mut left[leftmost_block][0],
                            &mut right[rightmost_block - leftmost_block - 1][0],
                        );
                    }
                    // Any cjmp followed by its false label, we leave alone.
                    Some(next_block) if get_label(next_block) == r#false => {}
                    // Any cjmp not followed by any of its labels, we create a new false label so
                    // that every cjmp is followed by its false label, and then append an jmp to
                    // the previous false label.
                    _ => match blocks.get_mut(i) {
                        Some(block) => {
                            let new_false_label = Label::new();
                            match block.iter_mut().last().unwrap().as_mut() {
                                Stmt::CJump {
                                    ref mut r#false, ..
                                } => *r#false = new_false_label,
                                _ => unreachable!(),
                            }
                            block.push(stmt!(label new_false_label));
                            block.push(stmt!(jmp exp!(name r#false), r#false));
                        }
                        _ => unreachable!(),
                    },
                }
            }
        }
    }
}

/// Estimate whether two expressions commute.
///
/// Two expressions commute if it is not possible for the stmt to have side effects affecting the
/// expression.
///
/// Rules:
///
/// * An empty Statement (i.e. Stmt::Exp(Exp::Const(_))), commutes with anything.
/// * Exp::Const(_) commutes with anything.
/// * Exp::Name(_) commutes with anything.
/// * Anything else is assumed to not commute.
fn commutes(stmt: &Stmt, exp: &Exp) -> bool {
    match (stmt, exp) {
        (Stmt::Exp(e), _) => match e.as_ref() {
            Exp::Const(_) => true,
            _ => false,
        },
        (_, Exp::Name(_)) => true,
        (_, Exp::Const(_)) => true,
        _ => false,
    }
}

fn linear(stmt: Box<Stmt>, mut rest: Vec<Box<Stmt>>) -> Vec<Box<Stmt>> {
    match *stmt {
        Stmt::Seq(s, s2) => linear(s, linear(s2, rest)),
        _ => {
            rest.insert(0, stmt);
            rest
        }
    }
}

fn do_stmt(stmt: Stmt) -> Box<Stmt> {
    match stmt {
        Stmt::Jump(exps, labels) => {
            reorder_stmt(vec![exps], move |mut exps| stmt!(jmp exps.remove(0), vec labels))
        },
        Stmt::CJump {
            op,
            left,
            right,
            r#true,
            r#false,
        } => {
            reorder_stmt(vec![left, right], move |mut exps| stmt!(cjmp op, exps.remove(0), exps.remove(0), r#true, r#false))
        },
        Stmt::Exp(e) => match *e {
            Exp::Call { func, args } => {
                let mut el = args;
                el.insert(0, func);
                reorder_stmt(el, move |mut exps| {
                    let func = exps.remove(0);
                    stmt!(exp exp!(call func, exps))
                })
            },
            _ => reorder_stmt(vec![e], move |mut exps| stmt!(exp exps.remove(0)))
        },
        Stmt::Seq(s1, s2) => reorder_stmt(vec![], move |_| seq!(do_stmt(*s1); do_stmt(*s2))),
        Stmt::Label(label) => reorder_stmt(vec![], move |_| stmt!(label label)),
        Stmt::Move(dst, src) => match *dst {
            Exp::Temp(_) => match *src {
                Exp::Call { func, args } => {
                    let mut el = args;
                    el.insert(0, func);
                    reorder_stmt(el, move |mut exps| {
                        let func = exps.remove(0);
                        stmt!(move dst, exp!(call func, exps))
                    })
                },
                _ => reorder_stmt(vec![src], move |mut exps| stmt!(move dst, exps.remove(0))),
            },
            Exp::Mem(e) => reorder_stmt(vec![e, src], move |mut exps| stmt!(move exp!(mem exps.remove(0)), exps.remove(1))),
            Exp::Eseq(s, e) => do_stmt(*seq!(s; stmt!(move e, src))),
            s => panic!("Compiler bug: Only a temporary or a memory location can be on the left hand side of a load, found {:?}", s),
        },
    }
}

fn do_exp(exp: Exp) -> (Box<Stmt>, Box<Exp>) {
    match exp {
        Exp::Const(n) => reorder_exp(vec![], move |_| exp!(const n)),
        Exp::Name(label) => reorder_exp(vec![], move |_| exp!(name label)),
        Exp::Temp(tmp) => reorder_exp(vec![], move |_| exp!(temp tmp)),
        Exp::BinOp(op, left, right) => reorder_exp(vec![left, right], move |mut exps| {
            exp!(op, exps.remove(0), exps.remove(0))
        }),
        Exp::Mem(e) => reorder_exp(vec![e], move |mut exps| exp!(mem exps.remove(0))),
        Exp::Call { func, args } => {
            let mut el = args;
            el.insert(0, func);
            reorder_exp(el, move |mut exps| {
                let func = exps.remove(0);
                exp!(call func, exps)
            })
        }
        Exp::Eseq(s1, e) => {
            let s1 = do_stmt(*s1);
            let (s2, e) = do_exp(*e);
            (seq!(s1; s2), e)
        }
    }
}

fn reorder_stmt<F>(exps: Vec<Box<Exp>>, build: F) -> Box<Stmt>
where
    F: FnOnce(Vec<Box<Exp>>) -> Box<Stmt>,
{
    let (s, exps) = reorder(exps);
    seq!(s; build(exps))
}

fn reorder_exp<F>(exps: Vec<Box<Exp>>, build: F) -> (Box<Stmt>, Box<Exp>)
where
    F: FnOnce(Vec<Box<Exp>>) -> Box<Exp>,
{
    let (s, exps) = reorder(exps);
    (s, build(exps))
}

fn reorder(mut exps: Vec<Box<Exp>>) -> (Box<Stmt>, Vec<Box<Exp>>) {
    if exps.is_empty() {
        return (stmt!(exp exp!(const 0)), vec![]);
    }

    let e = exps.remove(0);
    let (s, e) = do_exp(*e);
    let (s2, mut exps) = reorder(exps);

    if commutes(&s2, &e) {
        exps.insert(0, e);
        (seq!(s; s2), exps)
    } else {
        let t = Temp::new();
        exps.insert(0, exp!(temp t));
        (seq!(s; stmt!(move exp!(temp t), e); s2), exps)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BinOp, RelOp};

    #[test]
    fn test_linearize_simple_expressions() {
        let stmt = stmt!(exp exp!(+ exp!(const 1), exp!(const 2)));
        let expected = vec![
            // One nop for each node
            stmt!(exp exp!(const 0)),
            stmt!(exp exp!(const 0)),
            stmt!(exp exp!(const 0)),
            stmt!(exp exp!(const 0)),
            stmt.clone(),
        ];

        assert_eq!(linearize(*stmt), expected);
    }

    type Blocks = Vec<Vec<Box<Stmt>>>;
    fn assert_eq_blocks(built_blocks: Blocks, expected_blocks: Blocks, label_done: Label) {
        assert_eq!(
            built_blocks.len(),
            expected_blocks.len(),
            "Built and expected blocks have different length"
        );

        for (built, expected) in built_blocks.into_iter().zip(expected_blocks.into_iter()) {
            assert_eq!(
                built.len(),
                expected.len(),
                "Built and expected block have different length"
            );

            match built[0].as_ref() {
                Stmt::Label(label) if *label == label_done => {}
                Stmt::Label(_) => match built.iter().last() {
                    Some(stmt) => match stmt.as_ref() {
                        Stmt::Jump(_, _) | Stmt::CJump { .. } => {}
                        _ => panic!("Block does not end with a jump statement"),
                    },
                    _ => panic!("Block does not end with a jump statement"),
                },
                _ => panic!("Block does not start with a label"),
            }

            for (built_stmt, expected_stmt) in built.into_iter().zip(expected.into_iter()) {
                match (*built_stmt, *expected_stmt) {
                    (Stmt::Label(b_label), Stmt::Label(e_label)) => match (b_label, e_label) {
                        // Make testing easier by ignoring equality between anonymous labels.
                        (Label::Num(_), Label::Num(_)) => {}
                        _ => assert_eq!(b_label, e_label, "Expected labels to be equal"),
                    },
                    (b, e) => assert_eq!(b, e, "Expected statements to be equal"),
                }
            }
        }
    }

    #[test]
    fn test_blocks_simple_blocks() {
        let stmts = vec![];
        let (built_blocks, done) = basic_blocks(stmts);
        let expected = vec![vec![stmt!(label), stmt!(jmp exp!(name done), done)]];

        assert_eq_blocks(built_blocks, expected, done);

        let stmts = vec![stmt!(exp exp!(const 0))];
        let (built_blocks, done) = basic_blocks(stmts);
        let expected = vec![vec![
            stmt!(label),
            stmt!(exp exp!(const 0)),
            stmt!(jmp exp!(name done), done),
        ]];

        assert_eq_blocks(built_blocks, expected, done);

        let stmts = vec![
            stmt!(exp exp!(const 0)),
            stmt!(exp exp!(const 1)),
            stmt!(exp exp!(const 2)),
            stmt!(exp exp!(const 3)),
            stmt!(exp exp!(const 4)),
        ];
        let (built_blocks, done) = basic_blocks(stmts);
        let expected = vec![vec![
            stmt!(label),
            stmt!(exp exp!(const 0)),
            stmt!(exp exp!(const 1)),
            stmt!(exp exp!(const 2)),
            stmt!(exp exp!(const 3)),
            stmt!(exp exp!(const 4)),
            stmt!(jmp exp!(name done), done),
        ]];

        assert_eq_blocks(built_blocks, expected, done);
    }

    #[test]
    fn test_blocks_with_matching_jmps_and_labels() {
        let lbl1 = Label::with_name(Symbol::intern("lbl1"));
        let lbl2 = Label::with_name(Symbol::intern("lbl2"));
        let lbl3 = Label::with_name(Symbol::intern("lbl3"));

        let stmts = vec![
            stmt!(jmp exp!(name lbl1), lbl1),
            stmt!(label lbl1),
            stmt!(jmp exp!(name lbl2), lbl2),
            stmt!(label lbl2),
            stmt!(jmp exp!(name lbl3), lbl3),
            stmt!(label lbl3),
        ];
        let (built_blocks, done) = basic_blocks(stmts);
        let expected = vec![
            vec![stmt!(label), stmt!(jmp exp!(name lbl1), lbl1)],
            vec![stmt!(label lbl1), stmt!(jmp exp!(name lbl2), lbl2)],
            vec![stmt!(label lbl2), stmt!(jmp exp!(name lbl3), lbl3)],
            vec![stmt!(label lbl3), stmt!(jmp exp!(name done), done)],
        ];

        assert_eq_blocks(built_blocks, expected, done);
    }

    #[test]
    fn test_blocks_with_cjmps() {
        let r#true = Label::with_name(Symbol::intern("true"));
        let r#false = Label::with_name(Symbol::intern("false"));
        let endjmp = Label::with_name(Symbol::intern("endjmp"));

        let stmts = vec![
            stmt!(cjmp <, exp!(const 0), exp!(const 1), r#true, r#false),
            stmt!(label r#true),
            stmt!(exp exp!(const 10)),
            stmt!(jmp exp!(name endjmp), endjmp),
            stmt!(label r#false),
            stmt!(exp exp!(const 11)),
            stmt!(jmp exp!(name endjmp), endjmp),
            stmt!(label endjmp),
        ];
        let (built_blocks, done) = basic_blocks(stmts);
        let expected = vec![
            vec![
                stmt!(label),
                stmt!(cjmp <, exp!(const 0), exp!(const 1), r#true, r#false),
            ],
            vec![
                stmt!(label r#true),
                stmt!(exp exp!(const 10)),
                stmt!(jmp exp!(name endjmp), endjmp),
            ],
            vec![
                stmt!(label r#false),
                stmt!(exp exp!(const 11)),
                stmt!(jmp exp!(name endjmp), endjmp),
            ],
            vec![stmt!(label endjmp), stmt!(jmp exp!(name done), done)],
        ];

        assert_eq_blocks(built_blocks, expected, done);
    }

    #[test]
    fn test_simple_trace() {
        let done_label = Label::with_name(Symbol::intern("done"));
        let blocks = vec![vec![
            stmt!(label),
            stmt!(jmp exp!(name done_label), done_label),
        ]];

        let mut expected_blocks = blocks.clone().into_iter().flatten().collect::<Vec<_>>();
        expected_blocks.push(stmt!(label done_label));

        assert_eq!(trace_schedule(blocks, done_label), expected_blocks);
    }

    #[test]
    fn test_swap_trace() {
        let lbl2 = Label::new();
        let lbl3 = Label::new();
        let done_label = Label::with_name(Symbol::intern("done"));
        let blocks = vec![
            vec![stmt!(label), stmt!(jmp exp!(name lbl3), lbl3)],
            vec![
                stmt!(label lbl2),
                stmt!(jmp exp!(name done_label), done_label),
            ],
            vec![stmt!(label lbl3), stmt!(jmp exp!(name lbl2), lbl2)],
        ];

        let mut expected_blocks = blocks.clone();
        expected_blocks.swap(1, 2);
        expected_blocks.push(vec![stmt!(label done_label)]);
        let expected_blocks = expected_blocks.into_iter().flatten().collect::<Vec<_>>();

        assert_eq!(trace_schedule(blocks, done_label), expected_blocks);
    }

    #[test]
    fn test_fix_cjmp_followed_by_false_label() {
        let r#true = Label::with_name(Symbol::intern("true"));
        let r#false = Label::with_name(Symbol::intern("false"));
        let endcjmp = Label::with_name(Symbol::intern("endcjmp"));
        let done_label = Label::with_name(Symbol::intern("done"));

        let mut blocks = vec![
            vec![
                stmt!(label),
                stmt!(cjmp =, exp!(const 0), exp!(const 0), r#true, r#false),
            ],
            vec![
                stmt!(label r#false),
                stmt!(exp exp!(const 10)),
                stmt!(jmp exp!(name endcjmp), endcjmp),
            ],
            vec![
                stmt!(label r#true),
                stmt!(exp exp!(const 20)),
                stmt!(jmp exp!(name endcjmp), endcjmp),
            ],
            vec![
                stmt!(label endcjmp),
                stmt!(exp exp!(const 30)),
                stmt!(jmp exp!(name done_label), done_label),
            ],
        ];
        let trace = vec![vec![0, 1, 2, 3]];

        let expected_blocks = blocks.clone();
        fix_cjmps(&trace, &mut blocks);

        assert_eq!(blocks, expected_blocks);
    }

    #[test]
    fn test_fix_cjmp_followed_by_true_label() {
        let r#true = Label::with_name(Symbol::intern("true"));
        let r#false = Label::with_name(Symbol::intern("false"));
        let endcjmp = Label::with_name(Symbol::intern("endcjmp"));
        let done_label = Label::with_name(Symbol::intern("done"));

        let mut blocks = vec![
            vec![
                stmt!(label),
                stmt!(cjmp =, exp!(const 0), exp!(const 0), r#true, r#false),
            ],
            vec![
                stmt!(label r#true),
                stmt!(exp exp!(const 10)),
                stmt!(jmp exp!(name endcjmp), endcjmp),
            ],
            vec![
                stmt!(label r#false),
                stmt!(exp exp!(const 20)),
                stmt!(jmp exp!(name endcjmp), endcjmp),
            ],
            vec![
                stmt!(label endcjmp),
                stmt!(exp exp!(const 30)),
                stmt!(jmp exp!(name done_label), done_label),
            ],
        ];
        let trace = vec![vec![0, 1, 2, 3]];

        let mut expected_blocks = blocks.clone();
        if let Stmt::CJump { ref mut op, .. } = expected_blocks[0][1].as_mut() {
            *op = RelOp::Neq;
        }
        let (left, right) = expected_blocks.split_at_mut(2);
        std::mem::swap(&mut left[1][0], &mut right[0][0]);
        fix_cjmps(&trace, &mut blocks);

        assert_eq!(blocks, expected_blocks);
    }

    #[test]
    fn test_fix_cjmp_followed_neither_label() {
        let r#true = Label::with_name(Symbol::intern("true"));
        let r#false = Label::with_name(Symbol::intern("false"));
        let endcjmp = Label::with_name(Symbol::intern("endcjmp"));
        let done_label = Label::with_name(Symbol::intern("done"));

        let mut blocks = vec![
            vec![
                stmt!(label r#true),
                stmt!(exp exp!(const 10)),
                stmt!(jmp exp!(name endcjmp), endcjmp),
            ],
            vec![
                stmt!(label r#false),
                stmt!(exp exp!(const 20)),
                stmt!(jmp exp!(name endcjmp), endcjmp),
            ],
            vec![
                stmt!(label),
                stmt!(cjmp =, exp!(const 0), exp!(const 0), r#true, r#false),
            ],
            vec![
                stmt!(label endcjmp),
                stmt!(exp exp!(const 30)),
                stmt!(jmp exp!(name done_label), done_label),
            ],
        ];
        let trace = vec![vec![0, 1, 2, 3]];

        let expected_blocks = blocks.clone();
        fix_cjmps(&trace, &mut blocks);

        assert_eq!(blocks[0], expected_blocks[0]);
        assert_eq!(blocks[1], expected_blocks[1]);
        assert_eq!(blocks[3], expected_blocks[3]);

        assert_eq!(blocks[2][0], expected_blocks[2][0]);

        let new_false_label = match blocks[2][1].as_ref() {
            Stmt::CJump {
                op,
                left,
                right,
                r#true: ctrue,
                r#false: cfalse,
            } => {
                assert_eq!(*op, RelOp::Eq);
                assert_eq!(left, &exp!(const 0));
                assert_eq!(right, &exp!(const 0));
                assert_eq!(*ctrue, r#true);
                cfalse
            }
            _ => unreachable!(),
        };

        match blocks[2][2].as_ref() {
            Stmt::Label(label) => assert_eq!(label, new_false_label),
            s => panic!("Unexpected statement: {:?}", s),
        }

        match blocks[2][3].as_ref() {
            Stmt::Jump(e, labels) => match e.as_ref() {
                Exp::Name(label) => {
                    assert_eq!(*label, r#false);
                    assert_eq!(labels.len(), 1);
                    assert_eq!(labels[0], r#false);
                }
                s => panic!("Unexpected statement: {:?}", s),
            },
            s => panic!("Unexpected statement: {:?}", s),
        }
    }
}
