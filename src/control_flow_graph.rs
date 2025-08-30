use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt::Debug,
    fmt::Display,
};

use crate::ir::BlockId;
use anyhow::{anyhow, bail, Result};

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

    pub fn dominates_2(&self, node_a: T, node_b: T) -> bool {
        // TODO: We don't need a vecdeque.
        let mut child_queue = VecDeque::from(self.graph.get(&node_b).cloned().unwrap_or_default());
        let mut visited_nodes = BTreeSet::new();

        while let Some(child) = child_queue.pop_front() {
            // Found a loop that is not dominated.
            if visited_nodes.contains(&child) {
                debug!("{} does not dominate {}", node_a, node_b);
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
                debug!("{} does not dominate {}", node_a, node_b);
                return false;
            }

            // At this point we have found our way back to the parent and simply clear it from the queue.
        }

        debug!("{} does dominate {}", node_a, node_b);
        true
    }

    pub fn dominates3(&self, dominator: T, dominatee: T) -> bool {
        let successors = self.cycle_aware_successors(&dominatee).unwrap();

        successors
            .iter()
            .filter(|successor_generation| successor_generation.len() == 1)
            .flatten()
            .any(|successor| *successor == dominator)
    }

    pub fn dominates(&self, node_a: T, node_b: T) -> bool {
        let mut visisted_nodes = BTreeSet::new();
        let mut paths: VecDeque<T> = self.direct_predecessors(&node_b).collect();
        if paths.is_empty() {
            return false;
        }

        debug!("direct predecessors for {} {:?}", node_b, paths);
        if paths.len() == 1 && paths[0] == node_a {
            return true;
        }

        while let Some(path) = paths.pop_back() {
            debug!("paths for {} {} {:?} {}", node_a, node_b, paths, path);
            if path == node_a {
                continue;
            }
            if visisted_nodes.contains(&path) {
                debug!("{} does not dominate {}", node_a, node_b);
                return false;
            }

            visisted_nodes.insert(path);

            let direct_predecssors: Vec<T> = self.direct_predecessors(&path).collect();
            if !direct_predecssors.is_empty() {
                direct_predecssors.into_iter().for_each(|path| {
                    if !paths.contains(&path) {
                        paths.push_front(path)
                    }
                });
            } else {
                debug!("{} does not dominate {}", node_a, node_b);
                return false;
            }
        }

        debug!("{} does dominate {}", node_a, node_b);
        true
    }

    pub fn direct_predecessors<'a>(&'a self, id: &'a T) -> impl Iterator<Item = T> + 'a {
        self.graph
            .clone()
            .into_iter()
            .filter(|(_, children)| children.contains(id))
            .map(|(predecessor_id, _)| predecessor_id)
    }

    pub fn is_direct_predecessor(&self, child: &T, potential_parent: &T) -> bool {
        assert!(self.contains(child));
        assert!(self.contains(potential_parent));
        debug!(
            "calcuating if {} is a direct predecessors of {}",
            potential_parent, child
        );

        self.graph
            .get(potential_parent)
            .map(|children| children.contains(child))
            .unwrap_or(false)
            || (self.is_in_cycle(potential_parent)
                && &self.find_cycle_successor(potential_parent).unwrap() == child
                && self.distance(potential_parent, child).unwrap() == 2)
    }

    pub fn distance(&self, parent: &T, child: &T) -> Result<usize> {
        let distance = self
            .successors(parent)?
            .iter()
            .inspect(|successors| debug!("found successors for {} {:?}", parent, successors))
            .position(|successor| successor.iter().any(|successor| successor == child))
            .map(|position| position + 1)
            .ok_or(anyhow!("child was not a successor".to_string()));

        debug!("distance between {parent} and {child} is {:?}", distance);

        distance
    }

    pub fn predecessors<'a>(&'a self, id: &'a T) -> Result<Vec<Vec<T>>> {
        debug!("finding predecessors for {id}");
        if !self.contains(id) {
            bail!(format!("{} is not in this control flow graph", id));
        }

        let direct_predecessors = |ids: Vec<T>| {
            ids.iter()
                .flat_map(|id| {
                    self.graph
                        .clone()
                        .into_iter()
                        .filter(|(_parent, children)| children.contains(id))
                        .map(|(parent, _)| parent)
                })
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
                .filter(|parent| seen_before.insert(*parent))
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

        debug!("predecessors for {} {:?}", id, predecessors);

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
                .filter(|child| seen_before.insert(*child))
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

    pub fn reachable_nodes<'a>(&'a self, id: &'a T) -> Result<Vec<T>> {
        self.cycle_aware_successors(id).map(|successors| successors.into_iter().flatten().collect())
    }

    pub fn cycle_aware_successors<'a>(&'a self, id: &'a T) -> Result<Vec<Vec<T>>> {
        if !self.contains(id) {
            bail!(format!("{} is not in this control flow graph", id));
        }

        let starting_point = self.graph.get(id).cloned().unwrap_or(Vec::new());
        let mut queue = VecDeque::from(vec![starting_point]);
        let mut successors = Vec::new();
        let mut seen_before = BTreeSet::new();

        let direct_children = |ids: Vec<T>| {
            ids.into_iter()
                .filter_map(|id| self.graph.get(&id).cloned())
                .flatten()
        };

        while let Some(children) = queue.pop_front() {
            let new_children: Vec<T> = BTreeSet::from_iter(children.clone().into_iter())
                .into_iter()
                .filter(|child| !seen_before.contains(child))
                .collect();

            // let cycle_successors: Vec<T> = new_children
            //     .iter()
            //     .filter_map(|child| {
            //         self.find_cycle_successor(child)
            //         // .map(|cycle_successor| (cycle_successor, child))
            //     })
            //     .filter(|cycle_successor| cycle_found.insert(*cycle_successor))
            //     .collect();

            // let new_children: Vec<T> = new_children
            //     .into_iter()
            //     .filter(|child| !cycle_successors.contains(child))
            //     .collect();
            debug!(
                "finding cycle aware successors: {:?} {:?} {:?}",
                new_children, queue, successors
            );

            // if !cycle_successors.is_empty() {
            //     assert!(cycle_successors.len() == 1);

            //     queue.push_front(cycle_successors);
            //     queue.push_front(children);
            //     continue;
            // }

            if !new_children.is_empty() {
                new_children.iter().for_each(|child| {
                    seen_before.insert(*child);
                });
                successors.push(new_children.clone());
            }

            let direct_successors: Vec<T> = direct_children(new_children.clone())
                .filter(|parent| !seen_before.contains(parent))
                .collect();

            for direct_successor in direct_successors.clone() {
                debug!(
                    "children is in  cycle: {:?} {:?} {:?}",
                    self.is_in_cycle(&direct_successor),
                    self.find_cycle_successor(&direct_successor),
                    direct_successor
                );
            }

            if direct_successors.iter().any(|child| {
                self.is_in_cycle(child)
                    && self
                        .find_cycle_entry(child)
                        .map(|entry| entry == new_children[0])
                        .unwrap_or(false)
            }) {
                assert!(new_children.len() == 1);
                let mut children_in_cycles: Vec<T> = direct_successors
                    .clone()
                    .into_iter()
                    .filter(|child| {
                        self.is_in_cycle(child) && self.dominates(new_children[0], *child)
                    })
                    .collect();
                debug!(
                    "children in cycle: {:?} {:?}",
                    children_in_cycles, direct_successors
                );
                // assert!(children_in_cycles.len() == 1);
                queue.push_back(children_in_cycles.clone());

                while !children_in_cycles.contains(&new_children[0]) {
                    children_in_cycles = children_in_cycles
                        .iter()
                        .flat_map(|child| self.graph.get(child).cloned().unwrap_or(Vec::new()))
                        .collect();

                    queue.push_back(children_in_cycles.clone());
                }

                // TODO: What happens if we somehow break out of the cycle here?
                // we are assuming that we can "consume" ever block "inside" the cycle.

                for direct_successor in direct_successors {
                    if !self.is_in_cycle(&direct_successor) {
                        queue.push_back(vec![direct_successor]);
                    }
                }
            } else if !direct_successors.is_empty() {
                queue.push_back(direct_successors.clone());
            }
        }

        Ok(successors)
    }

    pub fn is_in_cycle(&self, id: &T) -> bool {
        let mut child_queue = VecDeque::from(self.graph.get(id).cloned().unwrap_or_default());
        let mut visited_nodes = BTreeSet::new();

        while let Some(child) = child_queue.pop_front() {
            if &child == id {
                debug!("{} is in cycle", id);
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

        debug!("{} is not in cycle", id);

        false
    }


    // TODO: Test nested cycles

    pub fn find_first_common_successor(&self, block_id_a: &T, block_id_b: &T) -> Option<T> {
        let cycle_successor_a = self.find_cycle_successor(block_id_a);
        let cycle_successor_b = self.find_cycle_successor(block_id_b);

        // In this case we find the closest common successor in the cycle.
        // They are in the same cycle.
        if cycle_successor_a.is_some() && cycle_successor_b.is_some() {
              let mut predecessor = cycle_successor_a.unwrap();  

              loop {
                  let prev_predecessor = predecessor;
                  let mut next_predecessors = self.direct_predecessors(&prev_predecessor);
                  let next_predeccesor = next_predecessors.next();

                  if next_predecessors.next().is_some()  {
                      break;
                  }

                  predecessor = next_predeccesor.unwrap();

              }

              return Some(predecessor);

              }


        // In normal case must find first successor which domninates both.
        let successors = self.successors(block_id_a).unwrap();
        
        for successor_gen in successors {
            for successor in successor_gen {
                if self.dominates(successor, *block_id_a) 
                   && self.dominates(successor, *block_id_b) {
                     
                }
            }
        }

        

        None
    
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
            if predecessor != *block_id && self.dominates(predecessor, *block_id) {
                debug!("dominating predecessor {predecessor}");
                if let Some(successor) = self
                    .graph
                    .get(&predecessor)
                    .unwrap()
                    .iter()
                    .find(|child| !predecessors.contains(child))
                    .cloned()
                {
                    return Some(successor);
                }
            }
        }

        None
    }

    pub fn find_cycle_entry(&self, block_id: &T) -> Option<T> {
        let predecessors: Vec<T> = self
            .predecessors(block_id)
            .unwrap()
            .into_iter()
            .flatten()
            .collect();

        for predecessor in predecessors.clone() {
            if predecessor != *block_id && self.dominates(predecessor, *block_id) {
                debug!("found cycle entry for {} {}", block_id, predecessor);
                return Some(predecessor);
            }
        }

        debug!("failed to find cycle entry for {}", block_id);

        None
    }

    pub fn contains(&self, node: &T) -> bool {
        self.blocks.contains(node) || self.entry_point == *node
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
