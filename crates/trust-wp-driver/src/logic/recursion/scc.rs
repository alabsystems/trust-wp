// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generic Tarjan SCC (strongly connected components) utility.
//!
//! Provides graph-generic strongly connected component analysis and
//! self-edge detection, independent of the logic-function domain.

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

pub(super) fn has_self_edge<T>(graph: &HashMap<T, HashSet<T>>, node: T) -> bool
where
    T: Eq + Hash + Copy,
{
    graph
        .get(&node)
        .is_some_and(|callees| callees.contains(&node))
}

pub(super) fn strongly_connected_components<T>(graph: &HashMap<T, HashSet<T>>) -> Vec<Vec<T>>
where
    T: Eq + Hash + Copy,
{
    struct Tarjan<'a, T>
    where
        T: Eq + Hash + Copy,
    {
        graph: &'a HashMap<T, HashSet<T>>,
        index: usize,
        indices: HashMap<T, usize>,
        lowlink: HashMap<T, usize>,
        stack: Vec<T>,
        on_stack: HashSet<T>,
        components: Vec<Vec<T>>,
    }

    impl<'a, T> Tarjan<'a, T>
    where
        T: Eq + Hash + Copy,
    {
        fn new(graph: &'a HashMap<T, HashSet<T>>) -> Self {
            Self {
                graph,
                index: 0,
                indices: HashMap::new(),
                lowlink: HashMap::new(),
                stack: Vec::new(),
                on_stack: HashSet::new(),
                components: Vec::new(),
            }
        }

        fn run(mut self) -> Vec<Vec<T>> {
            for node in self.graph.keys().copied() {
                if !self.indices.contains_key(&node) {
                    self.strong_connect(node);
                }
            }
            self.components
        }

        fn strong_connect(&mut self, node: T) {
            let current_index = self.index;
            self.index += 1;
            self.indices.insert(node, current_index);
            self.lowlink.insert(node, current_index);
            self.stack.push(node);
            self.on_stack.insert(node);

            if let Some(callees) = self.graph.get(&node) {
                for callee in callees {
                    if !self.graph.contains_key(callee) {
                        continue;
                    }

                    if !self.indices.contains_key(callee) {
                        self.strong_connect(*callee);
                        let callee_lowlink = *self
                            .lowlink
                            .get(callee)
                            .expect("callee lowlink missing after DFS visit");
                        let node_lowlink = self
                            .lowlink
                            .get_mut(&node)
                            .expect("node lowlink missing during DFS backtrack");
                        *node_lowlink = (*node_lowlink).min(callee_lowlink);
                    } else if self.on_stack.contains(callee) {
                        let callee_index = *self
                            .indices
                            .get(callee)
                            .expect("callee index missing for in-stack node");
                        let node_lowlink = self
                            .lowlink
                            .get_mut(&node)
                            .expect("node lowlink missing during back-edge processing");
                        *node_lowlink = (*node_lowlink).min(callee_index);
                    }
                }
            }

            if self.lowlink.get(&node) == self.indices.get(&node) {
                let mut component = Vec::new();
                while let Some(stack_node) = self.stack.pop() {
                    self.on_stack.remove(&stack_node);
                    component.push(stack_node);
                    if stack_node == node {
                        break;
                    }
                }
                self.components.push(component);
            }
        }
    }

    Tarjan::new(graph).run()
}
