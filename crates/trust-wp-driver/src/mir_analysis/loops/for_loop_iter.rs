// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Iterator-based for-loop analysis (#2309).
//!
//! Handles Creusot-style iterator `produced` progression, iterable extraction,
//! ghost-state synthesis, and discriminant condition classification for
//! `for x in iter` loops.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_middle::mir::{
    BasicBlock, Body, Local, Operand, ProjectionElem, Rvalue, StatementKind, SwitchTargets,
    TerminatorKind,
};
use rustc_span::Spanned;
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_logic_fn_arity, resolve_sort_name, BinOp, ExprSort, PureExpr,
};

use super::{
    super::{
        call_resolve::{extract_call_def_id, resolve_trait_method_def_id},
        translate::{operand_int_ty, translate_operand, ty_to_expr_sort, ty_to_expr_sort_enriched},
    },
    condition::switch_target_value_to_i64,
    detection::{predecessor_map, LoopInfo},
    CallSpecContext,
};

fn sort_is_range(sort: &ExprSort) -> bool {
    match sort {
        ExprSort::Datatype(id) => matches!(
            resolve_sort_name(*id).as_str(),
            "core::ops::range::Range" | "std::ops::Range" | "core::ops::Range"
        ),
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => sort_is_range(inner),
        _ => false,
    }
}

fn iterator_state_sort(sort: Option<ExprSort>) -> Option<ExprSort> {
    match sort {
        Some(ExprSort::Ref(inner) | ExprSort::MutRef(inner)) => Some((*inner).clone()),
        other => other,
    }
}

fn range_loop_elem_fallback(loop_info: &LoopInfo, iter_sort: Option<ExprSort>) -> Option<PureExpr> {
    let iter_sort = iter_sort?;
    if !sort_is_range(&iter_sort) {
        return None;
    }

    Some(PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var(
            format!("__trust_wp_for_iter_state_{}", loop_info.header.as_u32()),
            Some(iter_sort),
        )),
        method: "start_log".to_string(),
        args: vec![],
    })
}

/// Synthesize one-iteration `produced` body effect for for-loops.
///
/// For loops lowered from `for x in iter`, Creusot exposes a logical ghost
/// variable `produced` that tracks yielded values. We model one step as:
/// `produced' = produced.push_back(x)`.
///
/// Returns `None` when the loop does not match for-loop lowering shape or
/// when the loop variable cannot be recovered from the iterator step.
pub(super) fn synthesize_for_loop_produced_effect<'tcx>(
    body: &Body<'tcx>,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
    call_spec_ctx: Option<CallSpecContext<'_, 'tcx>>,
) -> Option<(String, PureExpr)> {
    let produced_name = local_to_name
        .values()
        .find(|name| name.as_str() == "produced")
        .cloned()
        .or_else(|| {
            if loop_contains_seq_ghost_mutation(body, loop_info, call_spec_ctx) {
                Some("produced".to_string())
            } else {
                // Ordinary for-loops still expose the logical ghost sequence
                // `produced` in user-written invariants even when MIR debug
                // names do not materialize a local for it.
                Some("produced".to_string())
            }
        })?;

    let (call_block, switch_bb) = resolve_for_loop_next_call(body, loop_info)?;
    if !call_block_invokes_iterator_next(body, call_block, call_spec_ctx) {
        return None;
    }
    let header_data = &body.basic_blocks[call_block];
    let TerminatorKind::Call {
        args, destination, ..
    } = &header_data.terminator().kind
    else {
        return None;
    };
    let iterator_local =
        resolve_iterator_local_from_next_arg(args.first()?, &header_data.statements)?;
    let iter_sort = iterator_state_sort(match call_spec_ctx {
        Some(ctx) => ty_to_expr_sort_enriched(ctx.tcx, body.local_decls[iterator_local].ty),
        None => ty_to_expr_sort(body.local_decls[iterator_local].ty),
    });

    let switch_data = &body.basic_blocks[switch_bb];
    let TerminatorKind::SwitchInt { targets, .. } = &switch_data.terminator().kind else {
        return None;
    };

    let loop_var = find_for_loop_var_expr(
        body,
        loop_info,
        destination.local,
        targets,
        local_to_name,
        call_spec_ctx.map(|ctx| ctx.tcx),
    )
    .unwrap_or_else(|| {
        range_loop_elem_fallback(loop_info, iter_sort.clone()).unwrap_or_else(|| {
            PureExpr::Var(
                format!("__trust_wp_for_iter_elem_{}", loop_info.header.as_u32()),
                None,
            )
        })
    });
    // `produced` is always a Seq (Creusot-style ghost sequence of yielded elements).
    let produced_var = PureExpr::Var(produced_name.clone(), Some(ExprSort::Seq));
    let produced_next = PureExpr::MethodCall {
        receiver: Arc::new(produced_var),
        method: "push_back".to_string(),
        args: vec![loop_var],
    };

    Some((produced_name, produced_next))
}

/// Extract the iterable expression from a Creusot-style for-loop.
///
/// For `for x in iter_expr`, the MIR pre-header calls
/// `IntoIterator::into_iter(iter_expr)`. This function traces through
/// the pre-header to recover `iter_expr` as a `PureExpr`.
///
/// When the loop exhausts, `produced == iter_expr` (the iterator has
/// yielded all elements of the iterable in order). This is used to
/// build postcondition completion facts. (#1581)
pub(super) fn extract_for_loop_iterable(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    _local_to_name: &HashMap<Local, String>,
    local_exprs: &HashMap<Local, PureExpr>,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
) -> Option<PureExpr> {
    let (call_block, _) = resolve_for_loop_next_call(body, loop_info)?;
    let header_data = &body.basic_blocks[call_block];
    let TerminatorKind::Call {
        args,
        target: Some(_),
        ..
    } = &header_data.terminator().kind
    else {
        return None;
    };

    // Resolve the iterator local from Iterator::next(&mut iter) call
    let iterator_local =
        resolve_iterator_local_from_next_arg(args.first()?, &header_data.statements)?;

    // Primary path: trace back through the call-block's own external preheader.
    if let Some(iterable_expr) = extract_iterable_via_call_block_preheader(
        body,
        loop_info,
        iterator_local,
        call_block,
        local_exprs,
        preds,
    ) {
        return finalize_iterable(iterable_expr);
    }

    // Fallback (ghost-block for-loops): the `Iterator::next` call-block's only
    // predecessor is the loop HEADER, which is itself a body block (e.g. a
    // `falseUnwind` header), so the call-block has no external predecessor and
    // the primary trace fails. Here the `into_iter` call feeds the loop through
    // the header: `bb_a: _it = into_iter(iterable) -> bb_b; bb_b: goto -> header`.
    // Walk back from the header's external preheader through the goto/assign
    // chain to that `into_iter` call and recover its argument. (cc/fmap)
    let iterable_expr =
        recover_iterable_before_header(body, loop_info, local_exprs, preds, call_spec_ctx)?;
    finalize_iterable(iterable_expr)
}

/// Filter range-style tuple iterables (they have no sequence-valued `produced`),
/// otherwise pass the recovered iterable through.
fn finalize_iterable(iterable_expr: PureExpr) -> Option<PureExpr> {
    match &iterable_expr {
        PureExpr::LogicFnCall { name, .. } if tuple_logic_fn_arity(name).is_some() => None,
        _ => Some(iterable_expr),
    }
}

/// Original iterable trace: find the external preheader of the `Iterator::next`
/// call-block, then the `into_iter` call in its pre-preheader.
fn extract_iterable_via_call_block_preheader(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    iterator_local: Local,
    call_block: BasicBlock,
    local_exprs: &HashMap<Local, PureExpr>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
) -> Option<PureExpr> {
    // Trace back through preheader to find IntoIterator::into_iter call
    let preheader = preds
        .get(&call_block)?
        .iter()
        .copied()
        .find(|bb| !loop_info.body_blocks.contains(bb))?;
    let preheader_data = &body.basic_blocks[preheader];

    // Find: iter = move iter_tmp (assignment in preheader)
    let iter_source_local = preheader_data
        .statements
        .iter()
        .find_map(|stmt| match &stmt.kind {
            StatementKind::Assign(box (place, Rvalue::Use(operand, _)))
                if place.projection.is_empty() && place.local == iterator_local =>
            {
                match operand {
                    Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => {
                        Some(src.local)
                    }
                    _ => None,
                }
            }
            _ => None,
        })?;

    if let Some(expr) = local_exprs.get(&iter_source_local).cloned() {
        return Some(expr);
    }

    // Find: iter_tmp = IntoIterator::into_iter(iterable) in pre-preheader
    let pre_preheader = preds
        .get(&preheader)?
        .iter()
        .copied()
        .find(|bb| !loop_info.body_blocks.contains(bb))?;
    let pre_preheader_data = &body.basic_blocks[pre_preheader];

    match &pre_preheader_data.terminator().kind {
        TerminatorKind::Call {
            args, destination, ..
        } if destination.projection.is_empty() && destination.local == iter_source_local => args
            .first()
            .and_then(|arg| translate_operand(&arg.node, local_exprs)),
        _ => None,
    }
}

/// Determine whether a call terminator invokes `IntoIterator::into_iter`.
///
/// Requires a `CallSpecContext` to resolve the callee's def path; without it we
/// cannot soundly identify the call, so return `false` (no recovery).
fn call_is_into_iter(func: &Operand<'_>, call_spec_ctx: Option<CallSpecContext<'_, '_>>) -> bool {
    let Some(ctx) = call_spec_ctx else {
        return false;
    };
    let Some(def_id) = extract_call_def_id(func) else {
        return false;
    };
    let trait_def_id = resolve_trait_method_def_id(ctx.tcx, def_id).unwrap_or(def_id);
    ctx.tcx
        .def_path_str(trait_def_id)
        .ends_with("IntoIterator::into_iter")
}

/// Recover the iterable by walking back from the loop header's external
/// preheader through the goto/assign chain to the `IntoIterator::into_iter`
/// call that produced the iterator, then translating its argument. Used for
/// ghost-block for-loops whose `into_iter` feeds the loop through the header.
///
/// The walk is bounded and only follows external (non-body) predecessors, so it
/// cannot cross a back-edge into the loop body or diverge. Recovery is gated on
/// `call_is_into_iter` (via `CallSpecContext`), so an unrelated pre-loop call is
/// never mistaken for the iterator source. (cc/fmap)
fn recover_iterable_before_header(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    local_exprs: &HashMap<Local, PureExpr>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
) -> Option<PureExpr> {
    let mut current = preds
        .get(&loop_info.header)?
        .iter()
        .copied()
        .find(|bb| !loop_info.body_blocks.contains(bb))?;

    let mut visited = HashSet::new();
    for _ in 0..8 {
        if !visited.insert(current) {
            return None;
        }
        let data = &body.basic_blocks[current];
        if let TerminatorKind::Call { func, args, .. } = &data.terminator().kind {
            if call_is_into_iter(func, call_spec_ctx) {
                return args
                    .first()
                    .and_then(|arg| translate_operand(&arg.node, local_exprs));
            }
        }
        current = preds
            .get(&current)?
            .iter()
            .copied()
            .find(|bb| !loop_info.body_blocks.contains(bb))?;
    }
    None
}

fn recover_iterator_binding_from_preheader(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    iterator_local: Local,
    local_exprs: &HashMap<Local, PureExpr>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
) -> Option<PureExpr> {
    let (call_block, _) = resolve_for_loop_next_call(body, loop_info)?;
    let preheader = preds
        .get(&call_block)?
        .iter()
        .copied()
        .find(|bb| !loop_info.body_blocks.contains(bb))?;
    let preheader_data = &body.basic_blocks[preheader];

    let iter_source_local = preheader_data
        .statements
        .iter()
        .find_map(|stmt| match &stmt.kind {
            StatementKind::Assign(box (place, Rvalue::Use(operand, _)))
                if place.projection.is_empty() && place.local == iterator_local =>
            {
                match operand {
                    Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => {
                        Some(src.local)
                    }
                    _ => None,
                }
            }
            _ => None,
        })?;

    if let Some(expr) = local_exprs.get(&iter_source_local).cloned() {
        return Some(expr);
    }

    let pre_preheader = preds
        .get(&preheader)?
        .iter()
        .copied()
        .find(|bb| !loop_info.body_blocks.contains(bb))?;
    let pre_preheader_data = &body.basic_blocks[pre_preheader];

    let iterable_expr = match &pre_preheader_data.terminator().kind {
        TerminatorKind::Call {
            args, destination, ..
        } if destination.projection.is_empty() && destination.local == iter_source_local => args
            .first()
            .and_then(|arg| translate_operand(&arg.node, local_exprs)),
        _ => None,
    }?;

    Some(PureExpr::MethodCall {
        receiver: Arc::new(iterable_expr),
        method: "into_iter".to_string(),
        args: vec![],
    })
}

fn extract_operand_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}

/// Recover the MIR local passed to `IntoIterator::into_iter` for this for-loop.
///
/// This is the collection value consumed by the iterator preheader. For
/// `for m in moves()`, it is the unnamed local receiving `moves()`, which lets
/// loop extraction attach that trusted call's postconditions to the synthesized
/// iterable expression without making all pre-loop call facts unconditional.
pub(super) fn recover_for_loop_iterable_source_local(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
) -> Option<Local> {
    let (call_block, _) = resolve_for_loop_next_call(body, loop_info)?;
    let header_data = &body.basic_blocks[call_block];
    let TerminatorKind::Call { args, .. } = &header_data.terminator().kind else {
        return None;
    };
    let iterator_local =
        resolve_iterator_local_from_next_arg(args.first()?, &header_data.statements)?;
    let preheader = preds
        .get(&call_block)?
        .iter()
        .copied()
        .find(|bb| !loop_info.body_blocks.contains(bb))?;
    let preheader_data = &body.basic_blocks[preheader];

    let iter_source_local = preheader_data
        .statements
        .iter()
        .find_map(|stmt| match &stmt.kind {
            StatementKind::Assign(box (place, Rvalue::Use(operand, _)))
                if place.projection.is_empty() && place.local == iterator_local =>
            {
                match operand {
                    Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => {
                        Some(src.local)
                    }
                    _ => None,
                }
            }
            _ => None,
        })?;

    let pre_preheader = preds
        .get(&preheader)?
        .iter()
        .copied()
        .find(|bb| !loop_info.body_blocks.contains(bb))?;
    let pre_preheader_data = &body.basic_blocks[pre_preheader];

    match &pre_preheader_data.terminator().kind {
        TerminatorKind::Call {
            args, destination, ..
        } if destination.projection.is_empty() && destination.local == iter_source_local => args
            .first()
            .and_then(|arg| extract_operand_local(&arg.node)),
        _ => None,
    }
}

/// Build grouped for-loop ghost state from MIR for structural invariant synthesis (#2171).
///
/// Combines the existing `produced` detection, iterator local resolution, and
/// iterable extraction into a single `ForLoopGhostState` payload. Returns `None`
/// when the loop is not a Creusot-style for-loop or when the iterator local
/// cannot be represented as a stable symbolic expression.
pub(super) fn extract_for_loop_ghost_state<'tcx>(
    body: &Body<'tcx>,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
    local_exprs: &HashMap<Local, PureExpr>,
    call_spec_ctx: Option<CallSpecContext<'_, 'tcx>>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
) -> Option<super::changed_places::ForLoopGhostState> {
    // 1. Detect `produced` name (same logic as synthesize_for_loop_produced_effect)
    let produced_name = local_to_name
        .values()
        .find(|name| name.as_str() == "produced")
        .cloned()
        .or_else(|| Some("produced".to_string()))?;

    // 2. Verify for-loop header shape: Call(Iterator::next) -> SwitchInt
    let (call_block, switch_bb) = resolve_for_loop_next_call(body, loop_info)?;
    if !call_block_invokes_iterator_next(body, call_block, call_spec_ctx) {
        return None;
    }
    let header_data = &body.basic_blocks[call_block];
    let TerminatorKind::Call {
        args,
        destination,
        target: Some(_),
        ..
    } = &header_data.terminator().kind
    else {
        return None;
    };

    // 3. Resolve the live iterator local from Iterator::next(&mut iter)
    let iterator_local =
        resolve_iterator_local_from_next_arg(args.first()?, &header_data.statements)?;
    let switch_data = &body.basic_blocks[switch_bb];
    let TerminatorKind::SwitchInt { targets, .. } = &switch_data.terminator().kind else {
        return None;
    };

    // 4. Build the synthetic iterator-state variables and bind them back to the
    //    MIR-recovered iterator expression. The synthetic state variable is what
    //    the loop verifier primes; the binding preserves the actual MIR meaning.
    //    If no stable expression exists, bail rather than inventing a disconnected variable.
    let iter_state_binding = recover_iterator_binding_from_preheader(
        body,
        loop_info,
        iterator_local,
        local_exprs,
        preds,
    )
    .or_else(|| local_exprs.get(&iterator_local).cloned())?;

    // 5. Synthesize iter_old as a fresh stable variable with the iterator
    //    local's MIR sort. The binding itself can be a translated expression
    //    (for example `seq.into_inner()`), not just a bare named variable.
    let iter_sort = iterator_state_sort(match call_spec_ctx {
        Some(ctx) => ty_to_expr_sort_enriched(ctx.tcx, body.local_decls[iterator_local].ty),
        None => ty_to_expr_sort(body.local_decls[iterator_local].ty),
    });
    let iter_state = PureExpr::Var(
        format!("__trust_wp_for_iter_state_{}", loop_info.header.as_u32()),
        iter_sort.clone(),
    );
    let iter_state_next = PureExpr::Var(
        format!(
            "__trust_wp_for_iter_state_next_{}",
            loop_info.header.as_u32()
        ),
        iter_sort.clone(),
    );
    let iter_old = PureExpr::Var(
        format!("__trust_wp_for_iter_old_{}", loop_info.header.as_u32()),
        iter_sort.clone(),
    );
    let loop_elem = find_for_loop_var_expr(
        body,
        loop_info,
        destination.local,
        targets,
        local_to_name,
        call_spec_ctx.map(|ctx| ctx.tcx),
    )
    .unwrap_or_else(|| {
        range_loop_elem_fallback(loop_info, iter_sort.clone()).unwrap_or_else(|| {
            PureExpr::Var(
                format!("__trust_wp_for_iter_elem_{}", loop_info.header.as_u32()),
                None,
            )
        })
    });

    // 6. Recover the iterable expression when available. Range-style iterables
    //    still need the structural invariant even though they do not have a
    //    sequence-valued completion payload.
    let iterable = extract_for_loop_iterable(
        body,
        loop_info,
        local_to_name,
        local_exprs,
        call_spec_ctx,
        preds,
    );

    // 7. Recover range bounds for `for elem in start..end` loops (#1709).
    //    When the iterator is a range type, these hold the (start, end) expressions
    //    recovered from the MIR pre-header. Used to synthesize element bounds like
    //    `elem >= start` as loop invariants for nested loop inheritance.
    let range_bounds = super::for_range::recover_range_bounds_with_spec_ctx(
        body,
        loop_info,
        call_block,
        iterator_local,
        local_exprs,
        preds,
        call_spec_ctx,
    );

    Some(super::changed_places::ForLoopGhostState {
        produced_name,
        iter_old,
        iter_state,
        iter_state_binding,
        iter_state_next,
        loop_elem,
        iterable,
        range_bounds,
    })
}

fn call_block_invokes_iterator_next<'tcx>(
    body: &Body<'tcx>,
    call_block: BasicBlock,
    call_spec_ctx: Option<CallSpecContext<'_, 'tcx>>,
) -> bool {
    let Some(ctx) = call_spec_ctx else {
        return true;
    };
    let TerminatorKind::Call { func, .. } = &body.basic_blocks[call_block].terminator().kind else {
        return false;
    };
    let Some(def_id) = extract_call_def_id(func) else {
        return false;
    };
    let trait_def_id = resolve_trait_method_def_id(ctx.tcx, def_id).unwrap_or(def_id);
    ctx.tcx
        .def_path_str(trait_def_id)
        .ends_with("Iterator::next")
}

fn loop_contains_seq_ghost_mutation(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
) -> bool {
    let Some(spec_ctx) = call_spec_ctx else {
        return false;
    };

    for bb in &loop_info.body_blocks {
        let bb_data = &body.basic_blocks[*bb];
        if let TerminatorKind::Call { func, .. } = &bb_data.terminator().kind {
            let Some(def_id) = extract_call_def_id(func) else {
                continue;
            };
            let path = spec_ctx.tcx.def_path_str(def_id);
            if path.ends_with("::push_front_ghost") || path.ends_with("::push_back_ghost") {
                return true;
            }
        }
    }

    false
}

pub(super) fn resolve_for_loop_next_call(
    body: &Body<'_>,
    loop_info: &LoopInfo,
) -> Option<(BasicBlock, BasicBlock)> {
    let preds = predecessor_map(body);
    let mut current = loop_info.header;
    let mut visited = HashSet::new();

    loop {
        if !visited.insert(current) {
            return None;
        }

        match &body.basic_blocks[current].terminator().kind {
            TerminatorKind::Call {
                target: Some(switch_bb),
                ..
            } => return Some((current, *switch_bb)),
            TerminatorKind::SwitchInt { .. } => {
                let mut back_visited = HashSet::new();
                let mut worklist = vec![current];
                while let Some(target) = worklist.pop() {
                    let Some(target_preds) = preds.get(&target) else {
                        continue;
                    };
                    for pred in target_preds {
                        if !back_visited.insert(*pred) {
                            continue;
                        }
                        match &body.basic_blocks[*pred].terminator().kind {
                            TerminatorKind::Call {
                                target: Some(call_target),
                                ..
                            } if *call_target == target => return Some((*pred, current)),
                            TerminatorKind::FalseUnwind { real_target, .. }
                                if *real_target == target =>
                            {
                                worklist.push(*pred);
                            }
                            TerminatorKind::Goto {
                                target: goto_target,
                            } if *goto_target == target => {
                                worklist.push(*pred);
                            }
                            _ => {}
                        }
                    }
                }
                return None;
            }
            TerminatorKind::FalseUnwind { real_target, .. } => current = *real_target,
            TerminatorKind::Goto { target } => current = *target,
            _ => return None,
        }
    }
}

fn find_for_loop_var_expr<'tcx>(
    body: &Body<'tcx>,
    loop_info: &LoopInfo,
    option_local: Local,
    targets: &SwitchTargets,
    local_to_name: &HashMap<Local, String>,
    tcx: Option<rustc_middle::ty::TyCtxt<'tcx>>,
) -> Option<PureExpr> {
    targets
        .all_targets()
        .iter()
        .filter(|&&bb| loop_info.body_blocks.contains(&bb))
        .find_map(|&bb| {
            switch_target_assigns_for_loop_var(body, bb, option_local, local_to_name, tcx)
        })
}

fn check_block_for_loop_var_assign<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    option_local: Local,
    local_to_name: &HashMap<Local, String>,
    tcx: Option<rustc_middle::ty::TyCtxt<'tcx>>,
) -> Option<PureExpr> {
    body.basic_blocks[bb]
        .statements
        .iter()
        .find_map(|stmt| match &stmt.kind {
            StatementKind::Assign(box (place, Rvalue::Use(operand, _)))
                if place.projection.is_empty() =>
            {
                let (Operand::Copy(source) | Operand::Move(source)) = operand else {
                    return None;
                };
                if source.local == option_local
                    && source.projection.len() == 2
                    && matches!(source.projection[0], ProjectionElem::Downcast(_, _))
                    && matches!(
                        source.projection[1],
                        ProjectionElem::Field(field, _) if field.as_u32() == 0
                    )
                {
                    let name = local_to_name.get(&place.local).cloned().unwrap_or_else(|| {
                        format!("__trust_wp_for_iter_elem_{}", place.local.as_u32())
                    });
                    let sort = match tcx {
                        Some(tcx) => {
                            ty_to_expr_sort_enriched(tcx, body.local_decls[place.local].ty)
                        }
                        None => ty_to_expr_sort(body.local_decls[place.local].ty),
                    };
                    Some(PureExpr::Var(name, sort))
                } else {
                    None
                }
            }
            _ => None,
        })
}

/// Check whether a switch target block extracts the for-loop variable from the
/// Option local. Follows one level of `Goto` forwarding to handle post-borrowck
/// MIR match arm desugaring where a forwarding block precedes the extraction.
pub(super) fn switch_target_assigns_for_loop_var<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    option_local: Local,
    local_to_name: &HashMap<Local, String>,
    tcx: Option<rustc_middle::ty::TyCtxt<'tcx>>,
) -> Option<PureExpr> {
    if let Some(expr) = check_block_for_loop_var_assign(body, bb, option_local, local_to_name, tcx)
    {
        return Some(expr);
    }
    // Follow one Goto forwarding block (match desugaring artifact in post-borrowck MIR).
    if let TerminatorKind::Goto { target } = &body.basic_blocks[bb].terminator().kind {
        return check_block_for_loop_var_assign(body, *target, option_local, local_to_name, tcx);
    }
    None
}

/// Derive the continuation condition for iterator-driven `for` loops.
///
/// For lowered `Iterator::next` + `SwitchInt(discriminant(option_tmp))`, classify
/// switch branches by whether they extract the loop variable from `option_tmp`
/// (`Some(field0)` path), not by CFG body-membership. This avoids tautological
/// conditions when loop-body detection over-approximates targets. (#1581)
pub(super) fn for_loop_discriminant_condition(
    discr: &Operand<'_>,
    targets: &SwitchTargets,
    body: &Body<'_>,
    local_exprs: &HashMap<Local, PureExpr>,
    option_local: Local,
    local_to_name: &HashMap<Local, String>,
) -> Option<PureExpr> {
    let discr_expr = translate_operand(discr, local_exprs)?;
    let discr_int_ty = operand_int_ty(discr, body);
    let mut body_values: Vec<i64> = Vec::new();
    let mut exit_values: Vec<i64> = Vec::new();

    for (value, target) in targets.iter() {
        let val = switch_target_value_to_i64(value, discr_int_ty)?;
        if switch_target_assigns_for_loop_var(body, target, option_local, local_to_name, None)
            .is_some()
        {
            body_values.push(val);
        } else {
            exit_values.push(val);
        }
    }

    let otherwise_is_body = switch_target_assigns_for_loop_var(
        body,
        targets.otherwise(),
        option_local,
        local_to_name,
        None,
    )
    .is_some();

    if body_values.is_empty() && !otherwise_is_body {
        return None;
    }

    body_values.sort_unstable();
    body_values.dedup();
    if !body_values.is_empty() {
        let mut cond = PureExpr::BinOp(
            Arc::new(discr_expr.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::Int(body_values[0])),
        );
        for &val in &body_values[1..] {
            cond = PureExpr::BinOp(
                Arc::new(cond),
                BinOp::Or,
                Arc::new(PureExpr::BinOp(
                    Arc::new(discr_expr.clone()),
                    BinOp::Eq,
                    Arc::new(PureExpr::Int(val)),
                )),
            );
        }
        return Some(cond);
    }

    if otherwise_is_body && !exit_values.is_empty() {
        exit_values.sort_unstable();
        exit_values.dedup();
        let mut cond = PureExpr::BinOp(
            Arc::new(discr_expr.clone()),
            BinOp::Ne,
            Arc::new(PureExpr::Int(exit_values[0])),
        );
        for &val in &exit_values[1..] {
            cond = PureExpr::BinOp(
                Arc::new(cond),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(discr_expr.clone()),
                    BinOp::Ne,
                    Arc::new(PureExpr::Int(val)),
                )),
            );
        }
        return Some(cond);
    }

    None
}

pub(super) fn resolve_iterator_local_from_next_arg(
    next_arg: &Spanned<Operand<'_>>,
    header_statements: &[rustc_middle::mir::Statement<'_>],
) -> Option<Local> {
    let arg_place = match &next_arg.node {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p,
        _ => return None,
    };

    // Typical MIR: `_tmp_ref = &mut iter; next(copy _tmp_ref)`.
    for stmt in header_statements {
        if let StatementKind::Assign(box (place, Rvalue::Ref(_, _, iter_place))) = &stmt.kind {
            if place.projection.is_empty()
                && place.local == arg_place.local
                && iter_place.projection.is_empty()
            {
                return Some(iter_place.local);
            }
        }
    }

    Some(arg_place.local)
}
