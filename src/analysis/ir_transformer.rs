use std::collections::{BTreeMap, BTreeSet, VecDeque};


use crate::ir::{Block, IrProgram, Variable, SSAID};
use crate::parser::AccessModes;

use crate::{control_flow_graph::ControlFlowGraph, ir::BlockId};
use anyhow::Result;
use tracing::debug;

use super::borrow_checker::VariableState;

#[derive(Clone, Debug)]
pub struct IrScope {
    pub blocks: BTreeMap<BlockId, Block>,
    pub control_flow_graph: ControlFlowGraph<BlockId>,
}

#[derive(Clone, Debug)]
pub struct IrInterpreter<Ctx> {
    scope: IrScope,
    control_flow_graph: ControlFlowGraph<BlockId>,
    pub ssa_variables: BTreeMap<SSAID, Variable>,
    pub access_modes: BTreeMap<SSAID, AccessModes>,
    context: Ctx,
}

pub struct IrBlockIterator {
    queue: VecDeque<BlockId>,
    visited_blocks: BTreeSet<BlockId>,
    control_flow_graph: ControlFlowGraph<BlockId>,
    visit_again: BTreeSet<BlockId>,
}

impl IrBlockIterator {
    fn new(control_flow_graph: ControlFlowGraph<BlockId>) -> Self {
        let mut queue = VecDeque::new();
        queue.push_back(control_flow_graph.entry_point);
        Self {
            control_flow_graph,
            queue,
            visited_blocks: BTreeSet::new(),
            visit_again: BTreeSet::new(),
        }
    }
}

impl Iterator for IrBlockIterator {
    type Item = BlockId;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next = self.queue.pop_front()?;
        while self.visited_blocks.contains(&next) && !self.visit_again.contains(&next) {
            next = self.queue.pop_front()?;
        }

        self.visited_blocks.remove(&next);

        debug!("next: {}, queue {:?}", next.0, self.queue);
        for predecessor in self.control_flow_graph.predecessors(&next.clone()) {
            if !self.visited_blocks.contains(&predecessor) {
                if self.control_flow_graph.dominates(next, predecessor) {
                    // TODO: remove predecssor from grandchildren, as we end up visiting it again.
                    // This logic tricky, as we need to ensure we revisit the dominated block after visting the dominator.
                    self.queue.push_front(predecessor);
                    self.queue.push_front(next);
                    next = predecessor;
                    self.visit_again.insert(next);
                    continue; // TODO: Continuing probably doesn't make sense here as we could have multiple unvisited predecessors I think.
                } else {
                    // todo!(
                    //     "this should not be possible, but how do we handle it? ,{:#?} {} {}",
                    //     self.control_flow_graph,
                    //     predecessor.0,
                    //     next.0
                    // );
                }
            }
        }
        debug!("processing block: {}", next.0);

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

type TransformFn<Ctx> =
    dyn FnMut(usize, &mut TransformContext, &BlockId, &mut Ctx) -> Result<usize>;

impl<Ctx: Clone + Default> IrInterpreter<Ctx> {
    pub fn new(control_flow_graph: ControlFlowGraph<BlockId>, program: IrProgram) -> Self {
        let scope = IrScope {
            blocks: program.blocks,
            control_flow_graph: control_flow_graph.clone(),
        };
        Self {
            control_flow_graph,
            scope,
            ssa_variables: program.ssa_variables,
            access_modes: program.access_modes,
            context: Ctx::default(),
        }
    }

    pub fn transform(mut self, transform_fn: &mut TransformFn<Ctx>) -> Result<Ctx> {
        let mut ctx = TransformContext {
            scope: self.scope.clone(),
            ssa_variables: self.ssa_variables.clone(),
            access_modes: self.access_modes.clone(),
            variable_states: BTreeMap::new(),
        };
        for block in self.control_flow_graph.clone() {
            self.transform_block(block, transform_fn, &mut ctx)?;
        }
        Ok(self.context)
    }

    fn transform_block(
        &mut self,
        block_id: BlockId,
        transform_fn: &mut TransformFn<Ctx>,
        ctx: &mut TransformContext,
    ) -> Result<()> {
        let _block = self.scope.blocks.get_mut(&block_id).unwrap();
        let mut instruction_counter = 0;

        loop {
            instruction_counter =
                transform_fn(instruction_counter, ctx, &block_id, &mut self.context)?;

            if instruction_counter == 0 {
                break;
            }
        }

        Ok(())
    }
}
