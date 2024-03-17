use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt::Debug,
    fmt::Display,
};

use crate::ir::BlockId;
use anyhow::{bail, Result};
use tracing::debug;

#[derive(Clone, Debug)]
pub struct ControlFlowGraph<T> {
    pub graph: BTreeMap<T, Vec<T>>,
    blocks: BTreeSet<T>,
    pub entry_point: T,
}

impl<T> ControlFlowGraph<T>
where
    T: Copy + Ord + Eq + PartialEq + PartialOrd + Display + Debug,
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

    pub fn direct_predecessors<'a>(&'a self, id: &'a T) -> impl Iterator<Item = T> + 'a {
        self.graph
            .clone()
            .into_iter()
            .filter(|(_, children)| children.contains(id))
            .map(|(predecessor_id, _)| predecessor_id)
    }

    pub fn predecessors<'a>(&'a self, id: &'a T) -> Result<Vec<Vec<T>>> {
        debug!("finding predecessors for {id}");
        if !self.contains(id) {
            bail!(format!("{} is not in this control flow graph", id));
        }

        let direct_predecessors = |ids: Vec<T>| {
            ids.iter()
                .map(|id| {
                    self.graph
                        .clone()
                        .into_iter()
                        .filter(|(_parent, children)| children.contains(id))
                        .map(|(parent, _)| parent)
                })
                .flatten()
                .collect()
        };

        let mut queue: Vec<Vec<T>> = vec![direct_predecessors(vec![*id])];
        let mut predecessors = Vec::new();
        let mut seen_before = BTreeSet::new();

        while let Some(parents) = queue.pop() {
            debug!("parents {:?}", parents);
            let new_parents: Vec<T> = parents
                .clone()
                .into_iter()
                .filter(|parent| seen_before.insert(parent.clone()))
                .collect();

            if !new_parents.is_empty() {
                predecessors.push(new_parents.clone());
            }

            let direct_predecessors: Vec<T> = direct_predecessors(new_parents)
                .into_iter()
                .filter(|parent| !seen_before.contains(parent))
                .collect();

            if !direct_predecessors.is_empty() {
                queue.push(direct_predecessors);
            }
        }

        Ok(predecessors)
    }

    pub fn successors<'a>(&'a self, id: &'a T) -> Result<Vec<Vec<T>>> {
        if !self.contains(id) {
            bail!(format!("{} is not in this control flow graph", id));
        }

        let starting_point = self.graph.get(id).cloned().unwrap_or(Vec::new());
        let mut queue = vec![starting_point];
        let mut successors = Vec::new();
        let mut seen_before = BTreeSet::new();

        let direct_children = |ids: Vec<T>| {
            ids.into_iter()
                .filter_map(|id| self.graph.get(&id).cloned())
                .flatten()
        };

        while let Some(children) = queue.pop() {
            let new_children: Vec<T> = children
                .clone()
                .into_iter()
                .filter(|child| seen_before.insert(child.clone()))
                .collect();

            if !new_children.is_empty() {
                successors.push(new_children.clone());
            }

            let direct_successors: Vec<T> = direct_children(new_children.clone())
                .filter(|parent| !seen_before.contains(parent))
                .collect();

            if !direct_successors.is_empty() {
                queue.push(direct_successors.clone());
            }
        }

        Ok(successors)
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

    pub fn find_cycle_successor(&self, block_id: &T) -> Option<T> {
        debug!("finding cycle successor for {block_id}");

        let predecessors: Vec<T> = self
            .predecessors(block_id)
            .unwrap()
            .into_iter()
            .flatten()
            .collect();

        debug!("predecessors: {:?}", predecessors);

        for predecessor in predecessors.clone() {
            if predecessor != *block_id && self.dominates(predecessor.clone(), *block_id) {
                debug!("dominating predecessor {predecessor}");
                return self
                    .graph
                    .get(&predecessor)
                    .unwrap()
                    .into_iter()
                    .find(|child| !predecessors.contains(child))
                    .cloned();
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

impl<T: Display + Copy> Display for ControlFlowGraph<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("entry point: {}\n", self.entry_point))?;
        for (predecessor, successors) in self.graph.clone() {
            let display_successors: String = successors
                .iter()
                .fold("".to_string(), |acc, next| format!("{}{}, ", acc, next));

            f.write_str(&format!("{} -> [{}]\n", predecessor, display_successors))?;
        }

        Ok(())
    }
}
