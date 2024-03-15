use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::ir::BlockId;

#[derive(Clone, Debug)]
pub struct ControlFlowGraph<T> {
    pub graph: BTreeMap<T, Vec<T>>,
    blocks: BTreeSet<T>,
    pub entry_point: T,
}

impl<T> ControlFlowGraph<T>
where
    T: Copy + Ord + Eq + PartialEq + PartialOrd,
{
    pub fn new(entry_point: T) -> Self {
        Self {
            graph: BTreeMap::new(),
            entry_point,
            blocks: BTreeSet::new(),
        }
    }

    pub fn insert_edge(&mut self, parent: T, child: T) {
        self.blocks.insert(parent);
        self.blocks.insert(child);
        self.graph
            .entry(parent)
            .and_modify(|children| children.push(child))
            .or_insert(vec![child]);
    }

    pub fn dominates(&self, node_a: T, node_b: T) -> bool {
        // TODO: We don't need a vecdeque.
        let mut child_queue = VecDeque::from(self.graph.get(&node_b).cloned().unwrap_or_default());
        let mut visited_nodes = BTreeSet::new();

        while let Some(child) = child_queue.pop_front() {
            // Found a loop that is not dominated.
            if visited_nodes.contains(&child) {
                return false;
            }
            visited_nodes.insert(child);

            let grand_children = self.graph.get(&child).cloned().unwrap_or_default();
            if child != node_a && !grand_children.is_empty() {
                for grand_child in grand_children {
                    child_queue.push_back(grand_child);
                }
            } else if child != node_a && grand_children.is_empty() {
                // Found a dead end
                return false;
            }

            // At this point we have found our way back to the parent and simply clear it from the queue.
        }

        true
    }

    pub fn predecessors<'a>(&'a self, id: &'a T) -> impl Iterator<Item = T> + 'a {
        self.graph
            .clone()
            .into_iter()
            .filter(|(_, children)| children.contains(id))
            .map(|(predecessor_id, _)| predecessor_id)
    }

    pub fn is_in_cycle(&self, id: &T) -> bool {
        let mut child_queue = VecDeque::from(self.graph.get(id).cloned().unwrap_or_default());
        let mut visited_nodes = BTreeSet::new();

        while let Some(child) = child_queue.pop_front() {
            if &child == id {
                return true;
            }

            if visited_nodes.contains(&child) {
                continue;
            }

            visited_nodes.insert(child);

            let grand_children = self.graph.get(&child).cloned().unwrap_or_default();
            for grand_child in grand_children {
                child_queue.push_back(grand_child);
            }

            // At this point we have found our way back to the parent and simply clear it from the queue.
        }

        false
    }

    pub fn find_cycle_successor(&self, block_id: &T) -> Option<&T> {
        let predecessors = self.predecessors(block_id);

        for predecessor in predecessors {
            if predecessor != *block_id && self.dominates(predecessor, *block_id) {
                return self.graph.get(&predecessor).unwrap().iter().find(|child| {
                    *child != block_id && !self.predecessors(block_id).any(|pred| **child == pred)
                });
            }
        }

        None
    }

    pub fn contains(&self, node: &T) -> bool {
        self.blocks.contains(node)
    }
}

impl ControlFlowGraph<BlockId> {
    pub fn into_ordered_iterator(self) -> ControlFlowGraphOrderedIterator {
        ControlFlowGraphOrderedIterator::new(self)
    }
}

pub struct ControlFlowGraphOrderedIterator {
    queue: VecDeque<BlockId>,
    visited_blocks: BTreeSet<BlockId>,
    control_flow_graph: ControlFlowGraph<BlockId>,
}

impl ControlFlowGraphOrderedIterator {
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

impl Iterator for ControlFlowGraphOrderedIterator {
    type Item = BlockId;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.queue.pop_front()?;

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
