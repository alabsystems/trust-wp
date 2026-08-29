// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mutable borrow analysis (RustHorn-style).
//!
//! Analyzes MIR for functions with `&mut` parameters and extracts how
//! those parameters are modified. This enables RustHorn-style verification
//! where mutable borrows are modeled as prophecy variables.

// Re-exported for use by tests.rs via `use super::*`.
#[cfg(test)]
pub(self) use std::collections::HashMap;

use rustc_middle::mir::BasicBlock;
#[cfg(test)]
pub(self) use trust_wp_core::formula::PureExpr;

mod call_classification;
mod data;
mod entry;
mod finality;
mod nested_transfer;
mod place_utils;
mod spec_advancement;
mod traversal;
pub(in crate::mir_analysis) mod type_analysis;

#[cfg(test)]
use call_classification::strip_generics;
use data::{BlockResult, MutBorrowAccumulators, MutBorrowBlockContext, MutBorrowTraversalState};
pub(crate) use data::{IndexedWrite, MutBorrowBody};
pub(crate) use entry::extract_mut_borrow_body;
#[cfg(test)]
use entry::make_typed_deref_expr;
use traversal::{process_statements, process_terminator};
pub(crate) use type_analysis::{
    collect_mut_ref_paths_with_tcx, type_contains_mut_ref_with_tcx,
    type_eventually_contains_mut_ref,
};

/// Extract final values for mutable borrows from a basic block.
///
/// Thin facade over `process_statements` (statement.rs) and
/// `process_terminator` (terminator.rs). Handles only loop detection
/// and dispatch; all logic lives in the traversal submodules.
fn extract_mut_borrow_from_block<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    bb: BasicBlock,
    mut state: MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) -> BlockResult {
    if state.visited.contains(&bb) {
        // Loop detected - too complex
        return None;
    }
    state.visited.insert(bb);

    let bb_data = &ctx.body.basic_blocks[bb];

    // Process statements (traversal/statement.rs)
    process_statements(ctx, &bb_data.statements, &mut state, accum);

    // Process terminator (traversal/terminator.rs)
    process_terminator(ctx, bb_data.terminator(), state, accum)
}

#[cfg(test)]
mod tests;
