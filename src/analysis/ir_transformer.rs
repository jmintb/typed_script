use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::control_flow_graph;
use crate::ir::{Block, Instruction, IrProgram, Variable, SSAID};
use crate::parser::AccessModes;
use crate::typed_ast::Type;
use crate::{control_flow_graph::ControlFlowGraph, ir::BlockId, parser::TSIdentifier};
use anyhow::Result;

use super::borrow_checker::VariableState;

#[derive(Clone, Debug)]
pub struct IrScope {
    pub blocks: BTreeMap<BlockId, Block>,
}

#[derive(Clone, Debug)]
pub struct IrInterpreter {
    scope: IrScope,
    control_flow_graph: ControlFlowGraph<BlockId>,
    pub ssa_variables: BTreeMap<SSAID, Variable>,
    pub access_modes: BTreeMap<SSAID, AccessModes>,
}

pub struct IrBlockIterator {
    queue: VecDeque<BlockId>,
    visited_blocks: BTreeSet<BlockId>,
    control_flow_graph: ControlFlowGraph<BlockId>,
}

impl IrBlockIterator {
    fn new(control_flow_graph: ControlFlowGraph<BlockId>) -> Self {
        let mut queue = VecDeque::new();
        queue.push_back(control_flow_graph.entry_point);
        Self {
            control_flow_graph,
            queue,
            visited_blocks: BTreeSet::new(),
        }
    }
}

impl Iterator for IrBlockIterator {
    type Item = BlockId;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next = self.queue.pop_front()?;
        for predecessor in self.control_flow_graph.predecessors(&next.clone()) {
            if !self.visited_blocks.contains(&predecessor) {
                if self.control_flow_graph.dominates(next, predecessor) {
                    // TODO: remove predecssor from grandchildren, as we end up visiting it again.
                    // This logic tricky, as we need to ensure we revisit the dominated block after visting the dominator.
                    self.queue.push_front(next);
                    self.queue.push_front(predecessor);
                    next = predecessor;
                    continue; // TODO: Continuing probably doesn't make sense here as we could have multiple unvisited predecessors I think.
                } else {
                    todo!("this should not be possible, but how do we handle it?");
                }
            }
        }

        for &grand_child in self
            .control_flow_graph
            .graph
            .get(&next)
            .unwrap_or(&Vec::new())
        {
            if !self.visited_blocks.contains(&grand_child) {
                self.queue.push_back(grand_child);
            }
        }

        self.visited_blocks.insert(next);

        Some(next)
    }
}

impl IntoIterator for ControlFlowGraph<BlockId> {
    type Item = BlockId;

    type IntoIter = IrBlockIterator;

    fn into_iter(self) -> Self::IntoIter {
        IrBlockIterator::new(self)
    }
}

pub struct TransformContext {
    pub scope: IrScope,
    pub ssa_variables: BTreeMap<SSAID, Variable>,
    pub access_modes: BTreeMap<SSAID, AccessModes>,
    pub variable_states: BTreeMap<SSAID, VariableState>,
}

type TransformFn = dyn FnMut(usize, &mut TransformContext, &BlockId) -> Result<usize>;

impl IrInterpreter {
    pub fn new(control_flow_graph: ControlFlowGraph<BlockId>, program: IrProgram) -> Self {
        let scope = IrScope {
            blocks: program.blocks,
        };
        Self {
            control_flow_graph,
            scope,
            ssa_variables: program.ssa_variables,
            access_modes: program.access_modes,
        }
    }

    pub fn transform(mut self, transform_fn: &mut TransformFn) -> Result<()> {
        let mut ctx = TransformContext {
            scope: self.scope.clone(),
            ssa_variables: self.ssa_variables.clone(),
            access_modes: self.access_modes.clone(),
            variable_states: BTreeMap::new(),
        };
        for block in self.control_flow_graph.clone() {
            self.transform_block(block, transform_fn, &mut ctx)?;
        }
        Ok(())
    }

    fn transform_block(
        &mut self,
        block_id: BlockId,
        transform_fn: &mut TransformFn,
        ctx: &mut TransformContext,
    ) -> Result<()> {
        let mut block = self.scope.blocks.get_mut(&block_id).unwrap();
        let mut instruction_counter = 0;

        loop {
            instruction_counter = transform_fn(instruction_counter, ctx, &block_id)?;

            if instruction_counter == 0 {
                break;
            }
        }

        Ok(())
    }
}
