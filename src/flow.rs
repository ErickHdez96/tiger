use crate::asm::Instruction;
use crate::graph::Graph;
use crate::temp::{Label, Temp};
use std::collections::{HashMap, HashSet};

#[derive(Debug, PartialEq, Eq)]
pub struct FlowNode {
    definitions: HashSet<Temp>,
    asm: String,
    uses: HashSet<Temp>,
    is_move: bool,
}

impl FlowNode {
    pub fn definitions(&self) -> &HashSet<Temp> {
        &self.definitions
    }

    pub fn uses(&self) -> &HashSet<Temp> {
        &self.uses
    }

    pub fn is_move(&self) -> bool {
        self.is_move
    }
}

#[derive(Debug)]
pub struct FlowGraph {
    control: Graph<FlowNode>,
}

impl FlowGraph {
    pub fn new(control: Graph<FlowNode>) -> Self {
        Self { control }
    }

    pub fn control(&self) -> &Graph<FlowNode> {
        &self.control
    }
}

/// Build a mapping between a label and its position inside the instructions slice.
fn build_label_map(instructions: &[Instruction]) -> HashMap<Label, usize> {
    instructions
        .iter()
        .enumerate()
        .filter_map(|(i, inst)| match inst {
            Instruction::Label { label, .. } => Some((*label, i)),
            _ => None,
        })
        .collect()
}

pub fn instructions_to_graph(instructions: &[Instruction]) -> FlowGraph {
    let labels_map = build_label_map(&instructions);
    let mut flow_graph = FlowGraph::new(Graph::new());
    let mut pending_instructions = vec![0];
    let mut predecesors = vec![];
    let mut visited = HashSet::new();

    while !pending_instructions.is_empty() {
        let i = pending_instructions.pop().unwrap();
        if visited.contains(&i) {
            predecesors.pop();
            continue;
        }

        let instruction: &Instruction = match instructions.get(i) {
            Some(inst) => inst,
            None => {
                predecesors.pop();
                continue;
            }
        };

        let node = FlowNode {
            definitions: get_definitions(&instruction),
            asm: format!("{}", instruction),
            uses: get_uses(&instruction),
            is_move: instruction.is_move(),
        };
        visited.insert(i);
        let entry = flow_graph.control.new_node(node);

        if let Some(pred) = predecesors.pop() {
            flow_graph.control.make_edge(pred, entry);
        }

        if let Instruction::Op { asm, jmp, .. } = instruction {
            if let Some(labels) = jmp {
                for label in labels {
                    let next_instruction = labels_map
                        .get(label)
                        .expect("Jump label not in current instruction list");
                    pending_instructions.push(*next_instruction);
                    predecesors.push(entry);
                }
            }

            if asm.starts_with("jmp") {
                continue;
            }
        }
        pending_instructions.push(i + 1);
        predecesors.push(entry);
    }

    flow_graph
}

fn get_definitions(instruction: &Instruction) -> HashSet<Temp> {
    match instruction {
        Instruction::Label { .. } => HashSet::new(),
        Instruction::Op { dst, .. } | Instruction::Move { dst, .. } => {
            dst.iter().cloned().collect()
        }
    }
}

fn get_uses(instruction: &Instruction) -> HashSet<Temp> {
    match instruction {
        Instruction::Label { .. } => HashSet::new(),
        Instruction::Op { src, .. } | Instruction::Move { src, .. } => {
            src.iter().cloned().collect()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen::CodeGen;
    use crate::ir::{BinOp, Exp, RelOp, Stmt};
    use crate::{exp, stmt};

    #[test]
    fn test_basic_flow_graph() {
        // Similar test to src/codegen.rs:test_basic_codegen
        let a = Temp::new();
        let b = Temp::new();
        let c = Temp::new();
        let loop_label = Label::with_name("loop");
        let end_label = Label::with_name("end");
        let mut gen = CodeGen::new();

        // a := 0
        gen.munch_stmt(*stmt!(move exp!(temp a), exp!(const 0)));
        // loop:
        gen.munch_stmt(*stmt!(label loop_label));
        // b := a + 1
        gen.munch_stmt(*stmt!(move exp!(temp b), exp!(+ exp!(temp a), exp!(const 1))));
        // c := c + b
        gen.munch_stmt(*stmt!(move exp!(temp c), exp!(+ exp!(temp c), exp!(temp b))));
        // a := b * 2
        gen.munch_stmt(*stmt!(move exp!(temp a), exp!(* exp!(temp b), exp!(const 2))));
        // a := b * 2
        gen.munch_stmt(*stmt!(cjmp <, exp!(temp a), exp!(const 10), loop_label, end_label));
        // end:
        gen.munch_stmt(*stmt!(label end_label));

        let instructions = gen.into_instructions();
        let flow_graph = instructions_to_graph(&instructions);
        let nodes = flow_graph.control.nodes();

        assert_eq!(nodes.len(), 13);

        // a := 0
        assert_eq!(
            nodes[0].element(),
            &FlowNode {
                definitions: [a].iter().cloned().collect(),
                asm: instructions[0].to_string(),
                uses: [].iter().cloned().collect(),
                is_move: false,
            }
        );

        // loop:
        assert_eq!(
            nodes[1].element(),
            &FlowNode {
                definitions: HashSet::new(),
                asm: instructions[1].to_string(),
                uses: HashSet::new(),
                is_move: false,
            }
        );

        // tmp := a + 1
        let tmp = match &instructions[2] {
            Instruction::Op { dst, .. } => dst[0],
            s => panic!("Expected a op instruction {:?}", s),
        };
        assert_eq!(
            nodes[2].element(),
            &FlowNode {
                definitions: [tmp].iter().cloned().collect(),
                asm: instructions[2].to_string(),
                uses: [a].iter().cloned().collect(),
                is_move: false,
            }
        );

        // b := tmp
        assert_eq!(
            nodes[3].element(),
            &FlowNode {
                definitions: [b].iter().cloned().collect(),
                asm: instructions[3].to_string(),
                uses: [tmp].iter().cloned().collect(),
                is_move: true,
            }
        );

        // tmp := c + b
        let tmp = match &instructions[4] {
            Instruction::Op { dst, .. } => dst[0],
            s => panic!("Expected a op instruction {:?}", s),
        };
        assert_eq!(
            nodes[4].element(),
            &FlowNode {
                definitions: [tmp].iter().cloned().collect(),
                asm: instructions[4].to_string(),
                uses: [c, b].iter().cloned().collect(),
                is_move: false,
            }
        );

        // c := tmp
        assert_eq!(
            nodes[5].element(),
            &FlowNode {
                definitions: [c].iter().cloned().collect(),
                asm: instructions[5].to_string(),
                uses: [tmp].iter().cloned().collect(),
                is_move: true,
            }
        );

        // tmp := b * 2
        let tmp = match &instructions[6] {
            Instruction::Op { dst, .. } => dst[0],
            s => panic!("Expected a op instruction {:?}", s),
        };
        assert_eq!(
            nodes[6].element(),
            &FlowNode {
                definitions: [tmp].iter().cloned().collect(),
                asm: instructions[6].to_string(),
                uses: [b].iter().cloned().collect(),
                is_move: false,
            }
        );

        // a := tmp
        assert_eq!(
            nodes[7].element(),
            &FlowNode {
                definitions: [a].iter().cloned().collect(),
                asm: instructions[7].to_string(),
                uses: [tmp].iter().cloned().collect(),
                is_move: true,
            }
        );

        // tmp1 := a
        let tmp1 = match &instructions[8] {
            Instruction::Move { dst, .. } => dst[0],
            s => panic!("Expected a op instruction {:?}", s),
        };
        assert_eq!(
            nodes[8].element(),
            &FlowNode {
                definitions: [tmp1].iter().cloned().collect(),
                asm: instructions[8].to_string(),
                uses: [a].iter().cloned().collect(),
                is_move: true,
            }
        );

        // tmp2 := 10
        let tmp2 = match &instructions[9] {
            Instruction::Move { dst, .. } => dst[0],
            s => panic!("Expected a op instruction {:?}", s),
        };
        assert_eq!(
            nodes[9].element(),
            &FlowNode {
                definitions: [tmp2].iter().cloned().collect(),
                asm: instructions[9].to_string(),
                uses: [].iter().cloned().collect(),
                is_move: true,
            }
        );

        // cmp tmp1, tmp2
        assert_eq!(
            nodes[10].element(),
            &FlowNode {
                definitions: [].iter().cloned().collect(),
                asm: instructions[10].to_string(),
                uses: [tmp1, tmp2].iter().cloned().collect(),
                is_move: false,
            }
        );

        // jl loop # if tmp1 < tmp2, jmp loop
        assert_eq!(
            nodes[11].element(),
            &FlowNode {
                definitions: [].iter().cloned().collect(),
                asm: instructions[11].to_string(),
                uses: [].iter().cloned().collect(),
                is_move: false,
            }
        );

        // end:
        assert_eq!(
            nodes[12].element(),
            &FlowNode {
                definitions: [].iter().cloned().collect(),
                asm: instructions[12].to_string(),
                uses: [].iter().cloned().collect(),
                is_move: false,
            }
        );
    }
}
