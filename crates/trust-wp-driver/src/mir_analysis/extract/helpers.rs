// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Small utility functions for MIR expression extraction.

use std::{collections::HashSet, sync::Arc};

use rustc_middle::mir::{BasicBlock, Body, Local, Location, Operand, Rvalue, TerminatorKind};
use rustc_span::Span;
use trust_wp_core::formula::{BinOp, PureExpr};

mod projected_write_facts;
mod unevaluated_const;

#[allow(unused_imports)]
pub(super) use projected_write_facts::{
    expr_references_var_name, invalidate_overlapping_projected_write_facts,
    record_projected_write_fact, translate_projected_write_lhs, wrap_projected_facts,
};
pub(crate) use unevaluated_const::collect_generic_assoc_const_definitions;
pub(super) use unevaluated_const::translate_rvalue_with_enum_variants;

pub(super) fn is_fallback_arg_name(name: &str) -> bool {
    let Some(rest) = name.strip_prefix("arg") else {
        return false;
    };
    !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit())
}

pub(super) fn expr_mentions_any_fallback_arg(
    expr: &PureExpr,
    fallback_arg_names: &HashSet<String>,
) -> bool {
    expr.any_free_var(|name, _| fallback_arg_names.contains(name))
}

pub(super) fn local_has_source_binding<'tcx>(
    body: &Body<'tcx>,
    local: Local,
    arg_names: &[String],
) -> bool {
    let idx = local.as_u32() as usize;
    if idx >= 1 && idx <= arg_names.len() {
        return true;
    }

    body.var_debug_info.iter().any(|info| {
        matches!(
            &info.value,
            rustc_middle::mir::VarDebugInfoContents::Place(place)
                if place.local == local && place.projection.is_empty()
        )
    })
}

/// Find the source-level name for a MIR local, if one exists.
///
/// Checks function arguments first, then var_debug_info. Returns the
/// highest-index binding (latest in source order) to handle shadowing.
pub(in crate::mir_analysis) fn source_name_for_local<'tcx>(
    body: &Body<'tcx>,
    local: Local,
    arg_names: &[String],
) -> Option<String> {
    let idx = local.as_u32() as usize;
    if idx >= 1 && idx <= arg_names.len() {
        return Some(arg_names[idx - 1].clone());
    }
    // Use the first debug binding for this local (MIR debug info is ordered
    // by source position, so the first match is the binding site).
    for info in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &info.value {
            if place.local == local && place.projection.is_empty() {
                return Some(info.name.to_string());
            }
        }
    }
    None
}

/// Check whether a `PureExpr` contains any `Final(...)` nodes.
///
/// `Final` nodes indicate that a variable's state has been advanced by a
/// mutating closure call (e.g., `FnMut::call_mut`). When present in a
/// local's expression, the reference identity should preserve the advanced
/// state rather than reverting to a bare `Var(name)`.
pub(super) fn expr_contains_final(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Final(_)))
}

pub(super) fn span_contains_cutoff(span: Span, cutoff: Span) -> bool {
    let lhs = span.source_callsite();
    let rhs = cutoff.source_callsite();
    if lhs.is_dummy() || rhs.is_dummy() {
        return false;
    }
    lhs.lo() <= rhs.lo() && lhs.hi() >= rhs.hi()
}

pub(super) fn join_with_or(exprs: Vec<PureExpr>) -> Option<PureExpr> {
    exprs
        .into_iter()
        .reduce(|a, b| PureExpr::BinOp(Arc::new(a), BinOp::Or, Arc::new(b)))
}

pub(super) fn join_with_and(exprs: Vec<PureExpr>) -> Option<PureExpr> {
    exprs
        .into_iter()
        .reduce(|a, b| PureExpr::BinOp(Arc::new(a), BinOp::And, Arc::new(b)))
}

/// Return true when a basic block can reach the proof_assert cutoff span.
///
/// This is used to distinguish "branch does not contain this assertion point"
/// from "branch extraction failed". If a branch cannot syntactically reach the
/// cutoff span, it is safe to ignore when extracting scoped state for that
/// assertion.
pub(super) fn block_can_reach_cutoff<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    cutoff_span: Span,
    visited: &mut HashSet<BasicBlock>,
) -> bool {
    if !visited.insert(bb) {
        return false;
    }

    let bb_data = &body.basic_blocks[bb];
    if bb_data
        .statements
        .iter()
        .any(|stmt| span_contains_cutoff(stmt.source_info.span, cutoff_span))
    {
        return true;
    }
    if span_contains_cutoff(bb_data.terminator().source_info.span, cutoff_span) {
        return true;
    }

    let successors = match &bb_data.terminator().kind {
        TerminatorKind::Goto { target }
        | TerminatorKind::Drop { target, .. }
        | TerminatorKind::Assert { target, .. } => vec![*target],
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => vec![*real_target],
        TerminatorKind::SwitchInt { targets, .. } => targets.all_targets().to_vec(),
        TerminatorKind::Call {
            target: Some(next), ..
        } => vec![*next],
        TerminatorKind::Return
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::Unreachable
        | TerminatorKind::CoroutineDrop
        | TerminatorKind::Call { target: None, .. }
        | TerminatorKind::TailCall { .. }
        | TerminatorKind::InlineAsm { .. }
        | TerminatorKind::Yield { .. } => return false,
    };

    successors
        .into_iter()
        .any(|target| block_can_reach_cutoff(body, target, cutoff_span, visited))
}

/// Return true when a basic block can reach the proof_assert cutoff location.
///
/// This is the location-precise counterpart to `block_can_reach_cutoff`.
pub(super) fn block_can_reach_location<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    cutoff_location: Location,
    visited: &mut HashSet<BasicBlock>,
) -> bool {
    if !visited.insert(bb) {
        return false;
    }

    if bb == cutoff_location.block {
        return true;
    }

    let bb_data = &body.basic_blocks[bb];
    let successors = match &bb_data.terminator().kind {
        TerminatorKind::Goto { target }
        | TerminatorKind::Drop { target, .. }
        | TerminatorKind::Assert { target, .. } => vec![*target],
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => vec![*real_target],
        TerminatorKind::SwitchInt { targets, .. } => targets.all_targets().to_vec(),
        TerminatorKind::Call {
            target: Some(next), ..
        } => vec![*next],
        TerminatorKind::Return
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::Unreachable
        | TerminatorKind::CoroutineDrop
        | TerminatorKind::Call { target: None, .. }
        | TerminatorKind::TailCall { .. }
        | TerminatorKind::InlineAsm { .. }
        | TerminatorKind::Yield { .. } => return false,
    };

    successors
        .into_iter()
        .any(|target| block_can_reach_location(body, target, cutoff_location, visited))
}

/// Return true when every path from `bb` diverges before returning.
///
/// This is used by scoped proof_assert extraction to drop panic-only branches.
/// If a branch provably diverges, it cannot reach the assertion point.
pub(super) fn block_must_diverge<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    visited: &mut HashSet<BasicBlock>,
) -> bool {
    if !visited.insert(bb) {
        // A cycle back to an already-visited block means this path loops
        // without reaching `Return`. Since `SwitchInt` uses `all()` (every
        // branch must diverge), any branch that can reach `Return` will have
        // already returned `false` before the cycle is encountered. Therefore
        // a cycle on the remaining path is genuinely divergent (infinite loop).
        // This handles `loop {}` and abort-based unreachable match arms.
        return true;
    }

    let term = body.basic_blocks[bb].terminator();
    match &term.kind {
        TerminatorKind::Call { target: None, .. } => true,
        TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::Unreachable
        | TerminatorKind::CoroutineDrop => true,
        TerminatorKind::Return => false,
        TerminatorKind::Goto { target }
        | TerminatorKind::Drop { target, .. }
        | TerminatorKind::Assert { target, .. } => block_must_diverge(body, *target, visited),
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => {
            block_must_diverge(body, *real_target, visited)
        }
        TerminatorKind::SwitchInt { targets, .. } => targets
            .all_targets()
            .iter()
            .copied()
            .all(|target| block_must_diverge(body, target, visited)),
        TerminatorKind::Call {
            target: Some(next), ..
        } => block_must_diverge(body, *next, visited),
        TerminatorKind::TailCall { .. }
        | TerminatorKind::InlineAsm { .. }
        | TerminatorKind::Yield { .. } => false,
    }
}

/// Return true when every path from `bb` eventually reaches a `Return`
/// terminator (without diverging).
///
/// This detects early-return branches in try-operator (`?`) desugaring.
/// When MIR desugars `x?`, one branch of the `SwitchInt` on the
/// `ControlFlow` discriminant leads to `FromResidual::from_residual()`
/// followed by `Return`. Body extraction fails on that branch because
/// the early return doesn't contribute to the function's final return
/// expression. This helper identifies such branches so the non-boolean
/// `SwitchInt` handler can skip them and keep the surviving branch.
pub(super) fn block_must_early_return<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    visited: &mut HashSet<BasicBlock>,
) -> bool {
    if !visited.insert(bb) {
        return false;
    }

    let term = body.basic_blocks[bb].terminator();
    match &term.kind {
        TerminatorKind::Return => true,
        // Divergent terminators are NOT early returns.
        TerminatorKind::Call { target: None, .. }
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::Unreachable
        | TerminatorKind::CoroutineDrop => false,
        TerminatorKind::Goto { target }
        | TerminatorKind::Drop { target, .. }
        | TerminatorKind::Assert { target, .. } => block_must_early_return(body, *target, visited),
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => {
            block_must_early_return(body, *real_target, visited)
        }
        TerminatorKind::SwitchInt { targets, .. } => targets
            .all_targets()
            .iter()
            .copied()
            .all(|target| block_must_early_return(body, target, visited)),
        TerminatorKind::Call {
            target: Some(next), ..
        } => block_must_early_return(body, *next, visited),
        TerminatorKind::TailCall { .. }
        | TerminatorKind::InlineAsm { .. }
        | TerminatorKind::Yield { .. } => false,
    }
}

/// Check whether an rvalue reads from a specific local (possibly through projection).
pub(super) fn rvalue_reads_from_local(rvalue: &Rvalue<'_>, local: Local) -> bool {
    match rvalue {
        // WithRetag does not change which local the operand reads.
        Rvalue::Use(operand, _) | Rvalue::Cast(_, operand, _) => operand_uses_local(operand, local),
        Rvalue::Ref(_, _, place) | Rvalue::Reborrow(_, _, place) | Rvalue::Discriminant(place) => {
            place.local == local
        }
        Rvalue::Aggregate(_, operands) => operands.iter().any(|op| operand_uses_local(op, local)),
        _ => false,
    }
}

/// Check whether an operand references a specific local.
pub(super) fn operand_uses_local(operand: &Operand<'_>, local: Local) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.local == local,
        Operand::Constant(_) | Operand::RuntimeChecks(_) => false,
    }
}
