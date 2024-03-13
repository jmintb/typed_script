use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Debug)]
pub struct ControlFlowGraph<T> {
    pub graph: BTreeMap<T, Vec<T>>,

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
        }
    }

    pub fn insert_edge(&mut self, parent: T, child: T) {
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
}
