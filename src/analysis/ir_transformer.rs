use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::ir::{Block, IrProgram, Variable, SSAID};
use crate::ast::nodes::AccessModes;

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
    block_states: BTreeMap<BlockId, Ctx>,
    pub ssa_variables: BTreeMap<SSAID, Variable>,
    pub access_modes: BTreeMap<SSAID, AccessModes>,
    context: Ctx,
    reverse_traversel: bool,
}

pub struct ReverseCycleAwareBlockIterator {
    qeueue: Vec<Vec<BlockId>>,
}

impl ReverseCycleAwareBlockIterator {
    fn new(control_flow_graph: ControlFlowGraph<BlockId>) -> Self {
        Self {
            qeueue: {
                let mut successors = control_flow_graph
                    .cycle_aware_successors(&control_flow_graph.entry_point)
                    .unwrap();
                successors.insert(0, vec![control_flow_graph.entry_point]);
                successors
            },
        }
    }
}

impl Iterator for ReverseCycleAwareBlockIterator {
    type Item = Vec<BlockId>;

    fn next(&mut self) -> Option<Self::Item> {
        self.qeueue.pop()
    }
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

        // self.visited_blocks.remove(&next);

        debug!("next: {}, queue {:?}", next.0, self.queue);

        // TODO: cycles  seem to be handled , but we need a rigorous test and to avoid the extra visits currently happening.
        if !self.visited_blocks.contains(&next) {
            for predecessor in self.control_flow_graph.direct_predecessors(&next.clone()) {
                if !self.visited_blocks.contains(&predecessor) {
                    if self.control_flow_graph.dominates(next, predecessor) {
                        let predecessors_preds = self
                            .control_flow_graph
                            .predecessors(&predecessor)
                            .unwrap()
                            .into_iter()
                            .flatten()
                            .collect::<Vec<Self::Item>>();

                        debug!(
                            "pred preds: {:?} \n  {} {}",
                            predecessors_preds, predecessor, next
                        );

                        let Some(loop_start_pos) =
                            predecessors_preds.iter().position(|pred| *pred == next)
                        else {
                            break;
                        };

                        let mut loop_blocks = predecessors_preds;
                        loop_blocks.split_off(loop_start_pos);
                        loop_blocks.reverse();
                        loop_blocks.push(predecessor);

                        debug!("cycle blocks: {:?}", loop_blocks);
                        assert!(!loop_blocks.contains(&next));

                        let mut loop_successors: Vec<BlockId> = self
                            .control_flow_graph
                            .successors(&loop_blocks[0])
                            .unwrap()
                            .into_iter()
                            .flatten()
                            .collect();

                        let cycle_completetion_position = loop_successors
                            .iter()
                            .position(|pred| *pred == next)
                            .unwrap();

                        loop_successors.split_off(cycle_completetion_position);

                        // loop_successors
                        //     .clone()
                        //     .into_iter()
                        //     .for_each(|block| loop_blocks.push(block));

                        self.visited_blocks.insert(next);
                        self.visit_again.insert(next);
                        if loop_blocks.len() == 1 {
                            self.queue.push_front(loop_blocks[0]);
                            self.queue.push_front(next);
                            self.visit_again.insert(loop_blocks[0]);
                            next = loop_blocks[0];
                            continue;
                        }

                        let (loop_start, loop_blocks) = loop_blocks.split_first().unwrap();
                        debug!(
                            "loop successor blocks: {:?} {:?} {} {}",
                            loop_successors, loop_blocks, loop_start, predecessor
                        );
                        let mut loop_blocks = loop_blocks.to_vec().clone();

                        loop_blocks.reverse();

                        self.queue.push_front(*loop_start);
                        for loop_predecessor in loop_blocks.clone() {
                            self.queue.push_front(loop_predecessor);
                            self.visit_again.insert(loop_predecessor);
                        }

                        self.queue.push_front(next);
                        self.queue.push_front(*loop_start);
                        self.visit_again.insert(*loop_start);
                        for loop_predecessor in loop_blocks {
                            self.queue.push_front(loop_predecessor);
                        }
                        debug!("skipping {next} {loop_start}");

                        // TODO: remove predecssor from grandchildren, as we end up visiting it again.
                        // This logic tricky, as we need to ensure we revisit the dominated block after visting the dominator.
                        next = *loop_start;
                        break; // TODO: Continuing probably doesn't make sense here as we could have multiple unvisited predecessors I think.
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

        // sleep(Duration::from_secs(1));

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

impl ControlFlowGraph<BlockId> {
    fn into_reverse_cycle_aware_iterator(self) -> ReverseCycleAwareBlockIterator {
        ReverseCycleAwareBlockIterator::new(self)
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
            block_states: BTreeMap::new(),
            context: Ctx::default(),
            reverse_traversel: false,
        }
    }

    pub fn new_reversed(control_flow_graph: ControlFlowGraph<BlockId>, program: IrProgram) -> Self {
        let scope = IrScope {
            blocks: program.blocks,
            control_flow_graph: control_flow_graph.clone(),
        };
        Self {
            control_flow_graph,
            scope,
            ssa_variables: program.ssa_variables,
            access_modes: program.access_modes,
            block_states: BTreeMap::new(),
            context: Ctx::default(),
            reverse_traversel: true,
        }
    }

    pub fn transform(mut self, transform_fn: &mut TransformFn<Ctx>) -> Result<Ctx> {
        let mut ctx = TransformContext {
            scope: self.scope.clone(),
            ssa_variables: self.ssa_variables.clone(),
            access_modes: self.access_modes.clone(),
            variable_states: BTreeMap::new(),
        };

        if self.reverse_traversel {
            for block in self
                .control_flow_graph
                .clone()
                .into_reverse_cycle_aware_iterator()
                .flatten()
            {
                self.transform_block(block, transform_fn, &mut ctx)?;
            }
        } else {
            // for block in self.control_flow_graph.clone() {
            //     debug!("block order {}", block);
            // }
            for block in self.control_flow_graph.clone() {
                self.transform_block(block, transform_fn, &mut ctx)?;
            }
        }

        Ok(self.context)
    }

    fn transform_block(
        &mut self,
        block_id: BlockId,
        transform_fn: &mut TransformFn<Ctx>,
        ctx: &mut TransformContext,
    ) -> Result<()> {
        let block = self.scope.blocks.get_mut(&block_id).unwrap();
        if block.instructions.is_empty() && self.reverse_traversel {
            return Ok(());
        }

        let mut instruction_counter = if self.reverse_traversel {
            block.instructions.len() - 1
        } else {
            0
        };

        loop {
            instruction_counter =
                transform_fn(instruction_counter, ctx, &block_id, &mut self.context)?;

            if (instruction_counter == 0 && !self.reverse_traversel)
                || (self.reverse_traversel && instruction_counter == block.instructions.len())
            {
                break;
            }
        }

        Ok(())
    }
}
