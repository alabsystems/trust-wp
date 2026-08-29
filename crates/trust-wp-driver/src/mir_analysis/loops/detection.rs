// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop detection via DFS-based back edge analysis.

use std::collections::{HashMap, HashSet};

use rustc_middle::mir::{BasicBlock, Body};

/// Information about a detected loop in MIR.
#[derive(Debug, Clone)]
pub(crate) struct LoopInfo {
    /// The header block of the loop (entry point)
    pub(crate) header: BasicBlock,
    /// All blocks in the loop body
    pub(crate) body_blocks: HashSet<BasicBlock>,
}

/// Result of analyzing a function for loops.
#[derive(Debug, Clone)]
pub(crate) struct LoopAnalysis {
    /// All detected loops (may be nested)
    pub(crate) loops: Vec<LoopInfo>,
    /// True if the function contains loops
    pub(crate) has_loops: bool,
}

/// Detect loops in a MIR function body.
///
/// Uses a DFS-based approach to find back edges in the CFG.
/// A back edge is an edge from a node to one of its dominators (ancestors in DFS).
///
/// # Notes
///
/// - Only analyzes blocks reachable from the entry block (bb0)
/// - Unreachable blocks (dead code) are ignored
/// - Nested loops are detected as separate `LoopInfo` entries
///
/// # Returns
///
/// `LoopAnalysis` containing all detected loops and their structure.
#[allow(clippy::items_after_statements)]
pub(crate) fn detect_loops(body: &Body<'_>) -> LoopAnalysis {
    // Precompute predecessor map for O(1) predecessor lookups
    let mut predecessors: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();
    for bb in body.basic_blocks.indices() {
        let bb_data = &body.basic_blocks[bb];
        for succ in bb_data.terminator().successors() {
            predecessors.entry(succ).or_default().push(bb);
        }
    }

    let mut visited = HashSet::new();
    let mut in_stack = HashSet::new();
    let mut back_edges: Vec<(BasicBlock, BasicBlock)> = Vec::new();

    // DFS to find back edges
    fn dfs(
        body: &Body<'_>,
        bb: BasicBlock,
        visited: &mut HashSet<BasicBlock>,
        in_stack: &mut HashSet<BasicBlock>,
        back_edges: &mut Vec<(BasicBlock, BasicBlock)>,
    ) {
        if visited.contains(&bb) {
            return;
        }
        visited.insert(bb);
        in_stack.insert(bb);

        let bb_data = &body.basic_blocks[bb];
        for succ in bb_data.terminator().successors() {
            if in_stack.contains(&succ) {
                // Back edge found: bb -> succ where succ is an ancestor
                back_edges.push((bb, succ));
            } else if !visited.contains(&succ) {
                dfs(body, succ, visited, in_stack, back_edges);
            }
        }

        in_stack.remove(&bb);
    }

    // Start DFS from entry block
    dfs(
        body,
        BasicBlock::from_u32(0),
        &mut visited,
        &mut in_stack,
        &mut back_edges,
    );

    // Group back edges by their target (loop header)
    let mut header_to_edges: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();
    for (from, to) in &back_edges {
        header_to_edges.entry(*to).or_default().push(*from);
    }

    // Build loop info for each detected loop
    let mut loops = Vec::new();
    for (header, edges) in header_to_edges {
        // Compute loop body: all blocks that can reach a back edge source
        // without going through the header
        let mut body_blocks = HashSet::new();
        body_blocks.insert(header);

        for &back_edge_src in &edges {
            // Work backwards from the back edge source to find all loop body blocks
            let mut worklist = vec![back_edge_src];
            while let Some(block) = worklist.pop() {
                if body_blocks.insert(block) {
                    // Add predecessors using precomputed map (O(1) lookup)
                    if let Some(preds) = predecessors.get(&block) {
                        for &pred_bb in preds {
                            if pred_bb != header {
                                worklist.push(pred_bb);
                            }
                        }
                    }
                }
            }
        }

        loops.push(LoopInfo {
            header,
            body_blocks,
        });
    }

    LoopAnalysis {
        has_loops: !loops.is_empty(),
        loops,
    }
}

/// Build a predecessor map for the given MIR body.
pub(super) fn predecessor_map(body: &Body<'_>) -> HashMap<BasicBlock, Vec<BasicBlock>> {
    let mut predecessors: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();
    for bb in body.basic_blocks.indices() {
        for succ in body.basic_blocks[bb].terminator().successors() {
            predecessors.entry(succ).or_default().push(bb);
        }
    }
    predecessors
}
