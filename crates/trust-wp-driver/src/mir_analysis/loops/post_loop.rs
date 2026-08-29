// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-loop analysis: exit block finding, return extraction, and
//! mutable-borrow dereference write tracking.

use std::{
    collections::{HashMap, HashSet},
    ops::ControlFlow,
};

use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind,
};
use tracing::debug;
use trust_wp_core::formula::PureExpr;

use super::{
    super::translate::{translate_operand, translate_rvalue},
    detection::LoopInfo,
};

/// Extract the return expression from post-loop MIR blocks.
///
/// After a loop exits, MIR typically has a short chain of blocks that copy the
/// computed value into `_0` (the return place) and then execute `Return`.
/// For `count_to_n`, the MIR looks like:
/// ```text
///   bb_exit: _0 = copy _2;  // _2 is local `i`
///            return;
/// ```
///
/// This function walks forward from the loop exit block (the SwitchInt target
/// that is NOT in the loop body), resolving temporaries, until it finds an
/// assignment to `Local::from_u32(0)` (the return place `_0`).
pub(super) fn extract_post_loop_return(
    body: &Body<'_>,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
    local_exprs: &HashMap<Local, PureExpr>,
    returns_ghost: bool,
) -> Option<PureExpr> {
    let exit_block = match find_post_loop_exit_block(body, cond_block, loop_info) {
        Some(exit_block) => {
            debug!(
                "extract_post_loop_return: exit block found: bb{}",
                exit_block.as_usize()
            );
            exit_block
        }
        None => {
            debug!("extract_post_loop_return: exit block not found");
            return None;
        }
    };

    // Walk post-loop blocks from exit_block, resolving assignments until we
    // find an assignment to _0 or hit Return.
    let return_local = Local::from_u32(0);
    let mut post_exprs = local_exprs.clone();
    let mut visited = HashSet::new();
    let mut worklist = vec![exit_block];

    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        if bb == cond_block || bb == loop_info.header {
            continue;
        }

        debug!("extract_post_loop_return: processing bb{}", bb.as_usize());

        let bb_data = &body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                if place.projection.is_empty() {
                    if let Some(expr) = translate_rvalue(rvalue, &post_exprs, Some(body)) {
                        post_exprs.insert(place.local, expr);
                    }
                }
            }
        }

        // Ghost blocks lower to a call assigning from `Ghost::new(<inner>)`.
        // In loop postcondition checks we need `result` bound to `<inner>`;
        // otherwise postconditions over `result` become unconstrained. (#873)
        //
        // trust-wp's ghost blocks use the `__trust_wp_ghost_value` debug name.
        // Creusot's `ghost!` macro uses `Ghost::new(inner)` directly with
        // compiler-generated temporaries that have no debug name. Handle
        // both: the named trust-wp pattern and unnamed single-arg constructor
        // calls (typical for Ghost wrapping in post-loop MIR). (#2116)
        //
        // When `returns_ghost` is true, also unwrap single-arg calls to _0
        // (the return place) even when _0 has a debug name. Ghost::new(inner)
        // may assign directly to _0, which can have a debug name like the
        // function's return variable. Without this, postconditions referencing
        // `*result` remain unconstrained for Ghost-returning functions whose
        // return place has a debug name. (#2671)
        if let TerminatorKind::Call {
            args, destination, ..
        } = &bb_data.terminator().kind
        {
            let dest_name = local_debug_name(body, destination.local);
            let is_trust_wp_ghost = dest_name
                .as_deref()
                .map_or(false, |name| name == "__trust_wp_ghost_value");
            let is_unnamed_single_arg_call = dest_name.is_none() && args.len() == 1;
            let is_ghost_return_to_result =
                returns_ghost && destination.local == return_local && args.len() == 1;
            let is_returns_ghost_single_arg_call = returns_ghost && args.len() == 1;
            if is_trust_wp_ghost
                || is_unnamed_single_arg_call
                || is_ghost_return_to_result
                || is_returns_ghost_single_arg_call
            {
                let mut matched_conditions = Vec::new();
                if is_trust_wp_ghost {
                    matched_conditions.push("is_trust_wp_ghost");
                }
                if is_unnamed_single_arg_call {
                    matched_conditions.push("is_unnamed_single_arg_call");
                }
                if is_ghost_return_to_result {
                    matched_conditions.push("is_ghost_return_to_result");
                }
                if is_returns_ghost_single_arg_call {
                    matched_conditions.push("is_returns_ghost_single_arg_call");
                }
                debug!(
                    "extract_post_loop_return: ghost unwrap in bb{} via {}",
                    bb.as_usize(),
                    matched_conditions.join(", ")
                );
                if let Some(arg0) = args.first() {
                    if let Some(expr) = translate_operand(&arg0.node, &post_exprs) {
                        post_exprs.insert(destination.local, expr);
                    }
                }
            }
        }

        // Check for Return terminator — if found, look up _0
        if matches!(bb_data.terminator().kind, TerminatorKind::Return) {
            let return_value = post_exprs.get(&return_local).cloned();
            debug!(
                "extract_post_loop_return: Return in bb{} value={return_value:?}",
                bb.as_usize()
            );
            return return_value;
        }

        match &bb_data.terminator().kind {
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                worklist.push(*real_target);
            }
            _ => {
                for succ in bb_data.terminator().successors() {
                    worklist.push(succ);
                }
            }
        }
    }

    // Fallback: check if _0 was assigned somewhere in the walk
    let fallback = post_exprs.get(&return_local).cloned();
    debug!(
        "extract_post_loop_return: fallback _0 found={}",
        fallback.is_some()
    );
    fallback
}

/// Find the block reached when the loop condition evaluates to exit.
pub(super) fn find_post_loop_exit_block(
    body: &Body<'_>,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
) -> Option<BasicBlock> {
    let cond_data = &body.basic_blocks[cond_block];
    match &cond_data.terminator().kind {
        TerminatorKind::SwitchInt { targets, .. } => {
            recover_post_loop_exit_block(body, cond_block, loop_info, targets).or_else(|| {
                targets
                    .all_targets()
                    .iter()
                    .copied()
                    .find(|target| {
                        !loop_info.body_blocks.contains(target)
                            && !matches!(
                                body.basic_blocks[*target].terminator().kind,
                                TerminatorKind::Unreachable
                            )
                    })
                    .or_else(|| {
                        targets
                            .all_targets()
                            .iter()
                            .copied()
                            .find(|target| !loop_info.body_blocks.contains(target))
                    })
            })
        }
        _ => None,
    }
}

fn recover_post_loop_exit_block(
    body: &Body<'_>,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
    targets: &rustc_middle::mir::SwitchTargets,
) -> Option<BasicBlock> {
    // Some desugarings route the loop-exit arm through a block that loop
    // detection conservatively keeps inside `body_blocks`. Recover the real
    // exit arm by looking for the unique switch target that can reach `Return`
    // without ever flowing back to the loop header/condition. (#2171)
    let mut exit_candidates = Vec::new();
    for target in targets.all_targets().iter().copied() {
        let reaches_return =
            reaches_return_without_loop_reentry(body, target, cond_block, loop_info);
        let reaches_reentry = reaches_loop_reentry(body, target, cond_block, loop_info);
        if reaches_return && !reaches_reentry {
            exit_candidates.push(target);
        }
    }

    let mut exit_targets = exit_candidates.into_iter();
    let exit = exit_targets.next()?;
    if exit_targets.next().is_none() {
        Some(exit)
    } else {
        None
    }
}

fn reaches_return_without_loop_reentry(
    body: &Body<'_>,
    start: BasicBlock,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
) -> bool {
    let mut visited = HashSet::new();
    let mut worklist = vec![start];

    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        if bb == cond_block || bb == loop_info.header {
            continue;
        }
        let bb_data = &body.basic_blocks[bb];
        if matches!(bb_data.terminator().kind, TerminatorKind::Return) {
            return true;
        }
        match &bb_data.terminator().kind {
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                worklist.push(*real_target);
            }
            _ => {
                for succ in bb_data.terminator().successors() {
                    worklist.push(succ);
                }
            }
        }
    }

    false
}

fn reaches_loop_reentry(
    body: &Body<'_>,
    start: BasicBlock,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
) -> bool {
    let mut visited = HashSet::new();
    let mut worklist = vec![start];

    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        if bb == cond_block || bb == loop_info.header {
            return true;
        }
        match &body.basic_blocks[bb].terminator().kind {
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                worklist.push(*real_target);
            }
            _ => {
                for succ in body.basic_blocks[bb].terminator().successors() {
                    worklist.push(succ);
                }
            }
        }
    }

    false
}

/// Walk post-loop blocks from the exit block, calling `visitor` on each block.
/// Handles visited tracking, loop-header guards, and FalseEdge/FalseUnwind
/// successor patterns.
fn walk_post_loop_blocks<'tcx, F>(
    body: &Body<'tcx>,
    exit_block: BasicBlock,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
    mut visitor: F,
) -> ControlFlow<()>
where
    F: FnMut(&BasicBlock, &BasicBlockData<'tcx>) -> ControlFlow<()>,
{
    let mut visited = HashSet::new();
    let mut worklist = vec![exit_block];
    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        if bb == cond_block || bb == loop_info.header {
            continue;
        }
        let bb_data = &body.basic_blocks[bb];
        if visitor(&bb, bb_data).is_break() {
            return ControlFlow::Break(());
        }
        match &bb_data.terminator().kind {
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                worklist.push(*real_target);
            }
            _ => {
                for succ in bb_data.terminator().successors() {
                    worklist.push(succ);
                }
            }
        }
    }
    ControlFlow::Continue(())
}

/// Extract mutable-borrow dereference writes that occur after loop exit.
///
/// Tracks direct writes (`*v = expr`) and temporary-mediated writes
/// (`_tmp = *v; *_tmp = expr`) along paths from loop exit to function return.
pub(super) fn extract_post_loop_deref_writes<'tcx>(
    body: &Body<'tcx>,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
) -> HashSet<String> {
    let Some(exit_block) = find_post_loop_exit_block(body, cond_block, loop_info) else {
        return HashSet::new();
    };

    let mut writes = HashSet::new();
    let mut deref_aliases: HashMap<Local, String> = HashMap::new();
    let _ = walk_post_loop_blocks(body, exit_block, cond_block, loop_info, |_bb, bb_data| {
        for stmt in &bb_data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                update_post_loop_deref_alias(place, rvalue, local_to_name, &mut deref_aliases);
                if let Some(root) = post_loop_deref_write_root(place, local_to_name, &deref_aliases)
                {
                    writes.insert(root);
                }
            }
        }
        ControlFlow::Continue(())
    });
    writes
}

/// Extract post-loop deref-write final values: maps `&mut` parameter names to
/// their final symbolic expressions assigned after the loop exits.
///
/// For `set_after_loop(x: &mut i32, n: i32) { while ... { *x = 0; } *x = n; }`,
/// returns `{"x" -> Var("n")}`. This provides the `final_values` needed by
/// `verify_mut_borrow_function_with_modes` when `extract_mut_borrow_body` returns
/// `None` due to loop cycle detection.
///
/// Walks the same post-loop blocks as `extract_post_loop_deref_writes` but also
/// tracks symbolic values via `translate_rvalue` to resolve the written expression.
pub(super) fn extract_post_loop_deref_final_values<'tcx>(
    body: &Body<'tcx>,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
    local_exprs: &HashMap<Local, PureExpr>,
) -> HashMap<String, PureExpr> {
    let Some(exit_block) = find_post_loop_exit_block(body, cond_block, loop_info) else {
        return HashMap::new();
    };

    let mut final_values = HashMap::new();
    let mut deref_aliases: HashMap<Local, String> = HashMap::new();
    // Track symbolic expressions for locals in post-loop blocks, starting from
    // the expressions established before the loop (pre-loop assignments + args).
    let mut post_exprs = local_exprs.clone();
    let bail = walk_post_loop_blocks(body, exit_block, cond_block, loop_info, |_bb, bb_data| {
        for stmt in &bb_data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                // Update deref alias tracking (reborrows like `_tmp = &mut *x`).
                update_post_loop_deref_alias(place, rvalue, local_to_name, &mut deref_aliases);

                if place.projection.is_empty() {
                    // Plain local assignment: update symbolic state.
                    if let Some(expr) = translate_rvalue(rvalue, &post_exprs, Some(body)) {
                        post_exprs.insert(place.local, expr);
                    }
                } else if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
                    // Deref write: `*local = rvalue`. Resolve the root param name
                    // and the rvalue to a symbolic expression.
                    if let Some(root) =
                        post_loop_deref_root_for_local(place.local, local_to_name, &deref_aliases)
                    {
                        if let Some(expr) = translate_rvalue(rvalue, &post_exprs, Some(body)) {
                            final_values.insert(root, expr);
                        }
                    }
                }
            }
        }

        // Soundness guard (#2085): if a post-loop block branches (SwitchInt),
        // we cannot determine which path will be taken, so deref final values
        // extracted from different branches would be unsound (last-write-wins
        // is path-insensitive). Bail conservatively with an empty map.
        if matches!(bb_data.terminator().kind, TerminatorKind::SwitchInt { .. }) {
            return ControlFlow::Break(());
        }

        ControlFlow::Continue(())
    });

    if bail.is_break() {
        return HashMap::new();
    }

    final_values
}

fn update_post_loop_deref_alias(
    place: &Place<'_>,
    rvalue: &Rvalue<'_>,
    local_to_name: &HashMap<Local, String>,
    deref_aliases: &mut HashMap<Local, String>,
) {
    if !place.projection.is_empty() {
        return;
    }
    if let Some(root) = rvalue_post_loop_deref_root(rvalue, local_to_name, deref_aliases) {
        deref_aliases.insert(place.local, root);
    } else {
        deref_aliases.remove(&place.local);
    }
}

fn rvalue_post_loop_deref_root(
    rvalue: &Rvalue<'_>,
    local_to_name: &HashMap<Local, String>,
    deref_aliases: &HashMap<Local, String>,
) -> Option<String> {
    let source_place = match rvalue {
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _)
        | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) => Some(src),
        Rvalue::Ref(_, _, src) => Some(src),
        _ => None,
    }?;
    if matches!(source_place.projection.first(), Some(ProjectionElem::Deref)) {
        post_loop_deref_root_for_local(source_place.local, local_to_name, deref_aliases)
    } else if source_place.projection.is_empty() {
        deref_aliases.get(&source_place.local).cloned()
    } else {
        None
    }
}

fn post_loop_deref_write_root(
    place: &Place<'_>,
    local_to_name: &HashMap<Local, String>,
    deref_aliases: &HashMap<Local, String>,
) -> Option<String> {
    if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
        return None;
    }
    post_loop_deref_root_for_local(place.local, local_to_name, deref_aliases)
}

fn post_loop_deref_root_for_local(
    local: Local,
    local_to_name: &HashMap<Local, String>,
    deref_aliases: &HashMap<Local, String>,
) -> Option<String> {
    deref_aliases
        .get(&local)
        .cloned()
        .or_else(|| local_to_name.get(&local).cloned())
}

pub(super) fn local_debug_name(body: &Body<'_>, local: Local) -> Option<String> {
    body.var_debug_info.iter().find_map(|dbg| match &dbg.value {
        rustc_middle::mir::VarDebugInfoContents::Place(place)
            if place.local == local && place.projection.is_empty() =>
        {
            Some(dbg.name.to_string())
        }
        _ => None,
    })
}
