// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Terminator-level processing for mutable borrow extraction.
//!
//! Handles MIR terminators within `extract_mut_borrow_from_block`:
//! Return, Goto, Assert, SwitchInt (boolean if/else), Drop,
//! Call (spec advancement, IndexMut, mutation continuation, snapshot capture),
//! and diverging terminators.

use std::{collections::HashMap, sync::Arc};

use rustc_middle::{
    mir::{BasicBlock, Local, Operand, Place, Terminator, TerminatorKind},
    ty::TyKind,
};
use trust_wp_core::formula::PureExpr;

use super::super::{
    call_classification::{
        call_may_mutate_params, is_box_new_call, is_fn_trait_call, is_index_mut_call,
        is_snapshot_capture_call,
    },
    data::{
        BlockResult, DerefLookup, MutBorrowAccumulators, MutBorrowBlockContext,
        MutBorrowTraversalState, PendingIndexMut, SliceReborrow,
    },
    entry::make_typed_deref_expr,
    field_writes,
    nested_transfer::{args_touch_nested_slots, try_nested_transfer_advancement},
    place_utils::resolve_reborrow_param_local,
    spec_advancement::{find_mutation_receiver, try_spec_advancement, try_spec_result_binding},
};
use crate::mir_analysis::translate::{
    operand_is_bool, translate_operand, ty_to_expr_sort_enriched,
};

/// Process the terminator of a basic block, recursing into successor blocks.
///
/// This is the terminator-processing half of `extract_mut_borrow_from_block`.
/// It dispatches on `TerminatorKind` and either returns a final result
/// (Return, diverging) or recurses into successor blocks via the parent
/// `extract_mut_borrow_from_block`.
pub(in super::super) fn process_terminator<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    bb: BasicBlock,
    terminator: &Terminator<'tcx>,
    state: MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) -> BlockResult {
    let mut state = state;
    havoc_params_written_by_handoff(ctx, bb, terminator, &mut state, accum);
    match &terminator.kind {
        TerminatorKind::Return => {
            // Return - capture final deref values and nested-slot contents.
            // A param whose borrow is returned on THIS path gets its tracked
            // pointee value wrapped in the lent marker: that value is not the
            // prophecy of a borrow the caller keeps writing through.
            if let Some(returned) = state
                .borrow_taint
                .get(&rustc_middle::mir::RETURN_PLACE)
                .cloned()
            {
                for param in returned {
                    if let Some(value) = state.deref_exprs.get(&param).cloned() {
                        state.deref_exprs.insert(
                            param,
                            PureExpr::LogicFnCall {
                                name: super::super::lent::LENT_ON_PATH_MARKER.to_string(),
                                args: vec![value],
                            },
                        );
                    }
                }
            }
            Some((state.deref_exprs, state.field_deref_exprs, state.slot_exprs))
        }
        TerminatorKind::Goto { target, .. } => {
            super::super::extract_mut_borrow_from_block(ctx, *target, state, accum)
        }
        TerminatorKind::Assert { target, .. } => {
            super::super::extract_mut_borrow_from_block(ctx, *target, state, accum)
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            process_switch_int(ctx, discr, targets, state, accum)
        }
        // A drop whose glue may write was re-read above; any other drop
        // changes no borrow's value.
        TerminatorKind::Drop { target, .. } => {
            super::super::extract_mut_borrow_from_block(ctx, *target, state, accum)
        }
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => process_call(ctx, func, args, destination, target, state, accum),
        TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::Unreachable => None,
        _ => None,
    }
}

/// D-140 in this lane: drop glue that may write stores through what the
/// dropped or handed value holds AFTER every store the body made, so the
/// final value of each parameter whose borrow that value may hold is not the
/// body's last store (`fn f(g: G<'_>) { *g.0 = 0 }` ends with `G::drop`
/// storing 5 through `g.0`). Each tracked parameter the hand-off reaches
/// (`drop_glue_writes::locals_reached_by_handoff`, the reach every other lane
/// re-binds, with the dropped value and the call's arguments kept) is
/// havocked. A parameter a call is handed as a `&mut` keeps what the call
/// lane gives it: its final value is the callee's `^`, which covers whatever
/// the callee's glue writes.
fn havoc_params_written_by_handoff<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    bb: BasicBlock,
    terminator: &Terminator<'tcx>,
    state: &mut MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) {
    let Some(reached) = crate::mir_analysis::extract::drop_glue_writes::locals_reached_by_handoff(
        ctx.tcx, ctx.body, bb, terminator,
    ) else {
        return;
    };
    let bound_by_callee: std::collections::HashSet<Local> = match &terminator.kind {
        TerminatorKind::Call { args, .. } => args
            .iter()
            .filter_map(|arg| match &arg.node {
                Operand::Copy(place) | Operand::Move(place)
                    if matches!(
                        place.ty(ctx.body, ctx.tcx).ty.kind(),
                        TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                    ) =>
                {
                    field_writes::tracked_root(ctx, state, accum, place.local)
                }
                _ => None,
            })
            .collect(),
        _ => std::collections::HashSet::new(),
    };
    let mut roots: Vec<Local> = reached
        .into_iter()
        .filter_map(|local| field_writes::tracked_root(ctx, state, accum, local))
        .filter(|root| !bound_by_callee.contains(root))
        .collect();
    roots.sort();
    roots.dedup();
    for root in roots {
        field_writes::havoc_param(ctx, state, accum, root);
    }
}

/// Handle `SwitchInt` terminators (boolean if/else branching).
fn process_switch_int<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    discr: &Operand<'tcx>,
    targets: &rustc_middle::mir::SwitchTargets,
    state: MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) -> BlockResult {
    // Conditional branching - handle if/else for mutable borrows
    if targets.all_targets().len() < 2 {
        return None;
    }

    let lookup = DerefLookup {
        locals: &state.local_exprs,
        deref_exprs: &state.deref_exprs,
        field_deref_exprs: &state.field_deref_exprs,
        carrier_read_locals: Some(&state.carrier_read_locals),
    };
    let condition = translate_operand(discr, &lookup)?;

    // Get condition for determining targets
    let is_bool = operand_is_bool(discr, ctx.body);
    if !is_bool {
        // Non-boolean switch - more complex, skip for now
        return None;
    }

    // Determine true/false branches for boolean
    let mut false_bb = None;
    let mut true_bb = None;
    for (value, target) in targets.iter() {
        if value == 0 {
            false_bb = Some(target);
        } else if value == 1 {
            true_bb = Some(target);
        }
    }
    let otherwise_bb = targets.otherwise();
    let else_bb = false_bb.unwrap_or(otherwise_bb);
    let then_bb = true_bb.unwrap_or(otherwise_bb);

    if then_bb == else_bb {
        return None;
    }

    // Extract both branches.
    // Note: cloning state for the then-branch is O(n) per branch point
    // where n = total entries in local_exprs + deref_exprs + field_deref_exprs +
    // reborrow_map + visited. For k nested conditionals, total cloning is
    // O(2^k * n).
    // This is bounded in practice because the analysis bails on loops,
    // TerminatorKind::Call, and non-boolean switches. Typical straight-line
    // Rust functions have k < 5. If this becomes a bottleneck, convert to
    // an iterative approach with an explicit state stack (#506 F3).
    let then_state = state.clone();
    let then_result = super::super::extract_mut_borrow_from_block(ctx, then_bb, then_state, accum);
    let else_result = super::super::extract_mut_borrow_from_block(ctx, else_bb, state, accum);

    // Phase 7 (#2124): When one branch diverges (e.g., panic! from
    // assert!()), its extraction returns None. Since a diverging branch
    // never returns, the function's final mutable borrow state is
    // determined entirely by the non-diverging branch. This is sound:
    // if the panic branch is taken, postconditions are vacuously true.
    // Without this, `assert!(a[i] == x)` in a &mut function body
    // causes the entire mut_borrow extraction to bail, falling through
    // to the pure function path which lacks state advancement.
    //
    // A `None` is also what the walk returns for an arm it cannot follow
    // (a non-boolean switch, a loop, a call it does not model), and such an
    // arm may return: taking the other arm's state as the final value there
    // states the other arm's writes on executions that never made them
    // (mut_borrow_arm_walk_refused_is_not_divergence.rs). Only an arm every
    // path of which diverges may be dropped; otherwise the walk refuses.
    let arm_unfollowed = |result: &BlockResult, arm: BasicBlock| {
        result.is_none()
            && !crate::mir_analysis::extract::block_must_diverge(
                ctx.body,
                arm,
                &mut std::collections::HashSet::new(),
            )
    };
    if arm_unfollowed(&then_result, then_bb) || arm_unfollowed(&else_result, else_bb) {
        return None;
    }
    merge_branch_results(ctx, &condition, then_result, else_result)
}

/// Merge results from then/else branches using `Ite` expressions.
fn merge_branch_results(
    ctx: &MutBorrowBlockContext<'_, '_>,
    condition: &PureExpr,
    then_result: BlockResult,
    else_result: BlockResult,
) -> BlockResult {
    match (then_result, else_result) {
        (
            Some((then_deref, then_field_deref, then_slots)),
            Some((else_deref, else_field_deref, else_slots)),
        ) => {
            // Both branches succeed — merge with Ite
            let mut result = HashMap::new();
            for &param_local in ctx.mut_borrow_params {
                if let (Some(then_val), Some(else_val)) =
                    (then_deref.get(&param_local), else_deref.get(&param_local))
                {
                    let ite_val = PureExpr::Ite(
                        Arc::new(condition.clone()),
                        Arc::new(then_val.clone()),
                        Arc::new(else_val.clone()),
                    );
                    result.insert(param_local, ite_val);
                }
            }

            let mut field_result = HashMap::new();
            let all_keys: std::collections::HashSet<_> = then_field_deref
                .keys()
                .chain(else_field_deref.keys())
                .collect();
            for &key in &all_keys {
                if let (Some(then_val), Some(else_val)) =
                    (then_field_deref.get(key), else_field_deref.get(key))
                {
                    let ite_val = PureExpr::Ite(
                        Arc::new(condition.clone()),
                        Arc::new(then_val.clone()),
                        Arc::new(else_val.clone()),
                    );
                    field_result.insert(*key, ite_val);
                }
            }

            // Merge nested-slot contents. An absent entry means the identity
            // (the slot still holds its entry borrow), so default the missing
            // side to the slot's entry-borrow expression before Ite-merging.
            let mut slot_result = HashMap::new();
            let slot_keys: std::collections::HashSet<_> = then_slots
                .keys()
                .chain(else_slots.keys())
                .copied()
                .collect();
            for slot in slot_keys {
                let default = || default_slot_content(ctx, slot);
                let then_val = then_slots.get(&slot).cloned().unwrap_or_else(default);
                let else_val = else_slots.get(&slot).cloned().unwrap_or_else(default);
                let merged = if then_val == else_val {
                    then_val
                } else {
                    PureExpr::Ite(
                        Arc::new(condition.clone()),
                        Arc::new(then_val),
                        Arc::new(else_val),
                    )
                };
                slot_result.insert(slot, merged);
            }

            Some((result, field_result, slot_result))
        }
        // One branch diverges — use the surviving branch directly.
        (Some(surviving), None) | (None, Some(surviving)) => Some(surviving),
        // Both branches diverge — the function never returns.
        (None, None) => None,
    }
}

/// The entry-borrow expression for a nested mut-ref parameter slot: the slot's
/// content before any transfer call rebinds it.
pub(in super::super) fn default_slot_content(
    ctx: &MutBorrowBlockContext<'_, '_>,
    slot: Local,
) -> PureExpr {
    let param_idx = slot.as_usize().saturating_sub(1);
    let name = ctx
        .arg_names
        .get(param_idx)
        .cloned()
        .unwrap_or_else(|| format!("$param_{}", slot.as_u32()));
    let sort = ty_to_expr_sort_enriched(ctx.tcx, ctx.body.local_decls[slot].ty);
    PureExpr::Var(name, sort)
}

/// Handle `Call` terminators.
///
/// Dispatches between mutating calls (spec advancement, IndexMut continuation,
/// Fn-trait calls, mutation continuation) and non-mutating calls (snapshot
/// capture, spec result binding, opaque variable fallback).
#[allow(clippy::trivially_copy_pass_by_ref)]
fn process_call<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
    target: &Option<BasicBlock>,
    mut state: MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) -> BlockResult {
    // Ghost calls (Snapshot::capture, proof_assert closures, etc.)
    // don't modify mutable borrow parameters. Skip them and continue
    // to the target block if the call is "mut-safe" — i.e., none of
    // its arguments pass a &mut reference to a tracked param. (#533)
    let target_bb = match target {
        Some(bb) => *bb,
        None => return None, // Diverging call — cannot continue
    };

    // A tracked borrow passed inside a composite argument (not itself a
    // `&mut`, e.g. a struct or tuple holding the borrow) reaches the callee
    // without any lane below modelling it: havoc its parameter (s34).
    let mut escaped_roots = Vec::new();
    for arg in args {
        let (Operand::Copy(place) | Operand::Move(place)) = &arg.node else {
            continue;
        };
        let ty = place.ty(ctx.body, ctx.tcx).ty;
        if matches!(
            ty.kind(),
            TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
        ) || !super::super::type_analysis::type_eventually_contains_mut_ref(ctx.tcx, ty)
        {
            continue;
        }
        if let Some(root) = field_writes::tracked_root(ctx, &state, accum, place.local) {
            escaped_roots.push(root);
        }
    }
    for root in escaped_roots {
        field_writes::havoc_param(ctx, &mut state, accum, root);
    }

    if call_may_mutate_params(ctx.tcx, args, ctx.body, func) {
        return process_mutating_call(ctx, func, args, destination, target_bb, state, accum);
    }

    // Non-mutating call path
    let dest_local = destination.local;
    let dest_sort = ty_to_expr_sort_enriched(ctx.tcx, ctx.body.local_decls[dest_local].ty);

    // Box::new(arg) is a transparent wrapper: the Box wraps its argument
    // without breaking reborrow chains. When the argument is a local that
    // reborrows a `&mut` param (has a tracked deref_exprs entry), propagate
    // the reborrow relationship to the Box destination so that writes through
    // the Box still alias the original `&mut` param. (#2318)
    //
    // Example MIR for `let bx = Box::new(&mut x)`:
    //   _tmp = &mut x           // _tmp reborrows x (tracked in deref_exprs)
    //   _bx = call Box::new(move _tmp)  // without this handler, _bx gets
    //                                    // an opaque binding, disconnecting
    //                                    // **bx from *x
    //
    // With this handler, _bx inherits _tmp's reborrow chain, so writes
    // through **_bx correctly update x's tracked final value.
    if is_box_new_call(ctx.tcx, func) && args.len() == 1 {
        if let Some(arg_local) = extract_simple_local(&args[0].node) {
            // Propagate local expression binding
            if let Some(arg_expr) = state.local_exprs.get(&arg_local).cloned() {
                state.local_exprs.insert(dest_local, arg_expr);
            }
            // Propagate deref tracking: if the argument has a tracked deref
            // expression (e.g., Deref(Var("x"))), the Box destination should
            // inherit it. This ensures that writes through *(*_bx) still
            // update x's final value.
            if let Some(deref_expr) = state.deref_exprs.get(&arg_local).cloned() {
                state.deref_exprs.insert(dest_local, deref_expr);
            }
            // Propagate reborrow chain so resolve_reborrow_param_local
            // can trace _bx back to the original &mut param.
            if let Some(&origin) = state.reborrow_map.get(&arg_local) {
                state.reborrow_map.insert(dest_local, origin);
            } else if ctx.mut_borrow_params.contains(&arg_local) {
                state.reborrow_map.insert(dest_local, arg_local);
            }

            return super::super::extract_mut_borrow_from_block(ctx, target_bb, state, accum);
        }
    }

    // Snapshot::capture(&value) semantically yields the captured value.
    // Bind the destination to the argument expression instead of an
    // opaque variable so that later `*snapshot` references resolve to
    // the value at the capture site. (#547)
    //
    // Exception: when the captured argument is `&mut T` (or `&&mut T`),
    // preserve the reference identity instead of resolving through
    // deref_exprs to the pointee state. This ensures `snapshot!(&mut **x)`
    // captures the borrow identity, not the current pointee value. (#2590)
    let dest_expr = if is_snapshot_capture_call(ctx.tcx, func) && !args.is_empty() {
        // The captured reference is the last argument. Both a direct
        // `Snapshot::capture(&expr)` and the type-directed
        // `snapshot_capture_select(&(expr))` dispatch carry the sole inline
        // reborrow `&expr` as their (single) argument. (bug/869)
        let ref_arg = &args[args.len() - 1].node;
        let arg_ty = ref_arg.ty(ctx.body, ctx.tcx);
        let is_mut_ref_capture = arg_ty.is_mutable_ptr()
            || matches!(arg_ty.kind(), TyKind::Ref(_, inner, _) if inner.is_mutable_ptr());
        if is_mut_ref_capture {
            // For &mut captures, use locals-only lookup to preserve reference
            // identity. The default ExprLookup for HashMap<Local, PureExpr>
            // returns None for get_deref_expr, preventing pointee collapse.
            translate_operand(ref_arg, &state.local_exprs).unwrap_or_else(|| {
                PureExpr::Var(format!("$_call_{}", dest_local.as_u32()), dest_sort.clone())
            })
        } else {
            let lookup = DerefLookup {
                locals: &state.local_exprs,
                deref_exprs: &state.deref_exprs,
                field_deref_exprs: &state.field_deref_exprs,
                carrier_read_locals: Some(&state.carrier_read_locals),
            };
            translate_operand(ref_arg, &lookup).unwrap_or_else(|| {
                PureExpr::Var(format!("$_call_{}", dest_local.as_u32()), dest_sort.clone())
            })
        }
    } else {
        // Try spec-driven result binding (#2124 Phase 3): if the
        // called function has a known spec with `result == <expr>`
        // or `result@ == <expr>`, bind the destination to the
        // substituted expression instead of an opaque variable.
        let lookup = DerefLookup {
            locals: &state.local_exprs,
            deref_exprs: &state.deref_exprs,
            field_deref_exprs: &state.field_deref_exprs,
            carrier_read_locals: Some(&state.carrier_read_locals),
        };
        try_spec_result_binding(ctx, func, args, &lookup).unwrap_or_else(|| {
            // Fallback: opaque variable. The opaque var ensures
            // the local is defined if referenced later.
            PureExpr::Var(format!("$_call_{}", dest_local.as_u32()), dest_sort)
        })
    };
    state.local_exprs.insert(dest_local, dest_expr);

    super::super::extract_mut_borrow_from_block(ctx, target_bb, state, accum)
}

/// Handle a call that may mutate `&mut` parameters.
///
/// Tries (in order): spec advancement, IndexMut continuation, Fn-trait bail,
/// mutation continuation fallback.
fn process_mutating_call<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
    target_bb: BasicBlock,
    mut state: MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) -> BlockResult {
    // Nested-reborrow transfer call (rusthorn inc_max_3 class): a call like
    // `swap(&mut ma, &mut mb)` whose spec is a pure whole-borrow permutation
    // of `&mut T`-typed parameter slots. Forward-simulate the permutation on
    // slot contents and pointee values; the exact per-path expiry resolutions
    // are emitted at function exit from the merged slot contents (entry.rs).
    if let Some(transfers) = try_nested_transfer_advancement(ctx, func, args, &state) {
        let moved: Vec<(Local, PureExpr, PureExpr)> = transfers
            .iter()
            .map(|&(dst, src)| {
                let content = state
                    .slot_exprs
                    .get(&src)
                    .cloned()
                    .unwrap_or_else(|| default_slot_content(ctx, src));
                let deref = state.deref_exprs.get(&src).cloned().unwrap_or_else(|| {
                    let param_idx = src.as_usize().saturating_sub(1);
                    let name = ctx
                        .arg_names
                        .get(param_idx)
                        .cloned()
                        .unwrap_or_else(|| format!("$param_{}", src.as_u32()));
                    make_typed_deref_expr(ctx.tcx, ctx.body, src, &name)
                });
                (dst, content, deref)
            })
            .collect();
        for (dst, content, deref) in moved {
            state.slot_exprs.insert(dst, content);
            if accum.havoc_params.is_empty() {
                state.deref_exprs.insert(dst, deref);
            } else {
                // Some pointee is havocked; never re-seed a stale referent.
                state.deref_exprs.remove(&dst);
            }
            accum.nested_transfer_slots.insert(dst);
        }

        // Bind the call destination to an opaque variable (transfer callees
        // return `()` or an unrelated value).
        let dest_local = destination.local;
        let dest_sort = ty_to_expr_sort_enriched(ctx.tcx, ctx.body.local_decls[dest_local].ty);
        state.local_exprs.insert(
            dest_local,
            PureExpr::Var(format!("$_call_{}", dest_local.as_u32()), dest_sort),
        );

        return super::super::extract_mut_borrow_from_block(ctx, target_bb, state, accum);
    }

    // Any other call that receives a nested slot borrow may rebind the slot
    // in ways this analysis does not model — poison nested-slot content
    // tracking (fail-closed: no expiry resolutions will be emitted).
    if args_touch_nested_slots(args, &state) {
        accum.nested_transfer_poisoned = true;
    }

    // Try spec-driven state advancement (#2124): if the called
    // function has a known spec with ensures clauses relating
    // `^self` to `self`, use the spec to advance the receiver's
    // symbolic state instead of bailing.
    let advancement = try_spec_advancement(
        ctx,
        func,
        args,
        &state.local_exprs,
        &state.deref_exprs,
        &state.field_deref_exprs,
        &state.reborrow_map,
        &state.carrier_read_locals,
    );
    if let Some(adv) = advancement {
        // The `^self` equation advances the receiver only. Every other `&mut`
        // argument reaches the callee too, and nothing the advancement read
        // says what it is left with: `keep(v, &mut *p)` under `^v == *v`
        // leaves `^p` the callee's to decide, and `v.push(p)` moves `p` into
        // the vector, whose holder decides it. Those parameters are havocked
        // like the arguments of a call no spec advances.
        let mut other_roots = Vec::new();
        for arg in args.iter().skip(1) {
            let (Operand::Copy(place) | Operand::Move(place)) = &arg.node else {
                continue;
            };
            if !matches!(
                ctx.body.local_decls[place.local].ty.kind(),
                TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
            ) {
                continue;
            }
            if let Some(root) = field_writes::tracked_root(ctx, &state, accum, place.local) {
                if root != adv.receiver_local {
                    other_roots.push(root);
                }
            }
        }
        for root in other_roots {
            field_writes::havoc_param(ctx, &mut state, accum, root);
        }
        // Apply state advancement: update deref_exprs for the
        // mutated receiver.
        state.deref_exprs.insert(adv.receiver_local, adv.new_state);
        field_writes::refresh_carrier_aliases(&mut state, adv.receiver_local);

        // Bind the call destination to an opaque variable (the
        // return value of the mutation call, e.g., () for push).
        let dest_local = destination.local;
        let dest_sort = ty_to_expr_sort_enriched(ctx.tcx, ctx.body.local_decls[dest_local].ty);
        state.local_exprs.insert(
            dest_local,
            PureExpr::Var(format!("$_call_{}", dest_local.as_u32()), dest_sort),
        );

        return super::super::extract_mut_borrow_from_block(ctx, target_bb, state, accum);
    }

    // Closed-form advancement failed. Try IndexMut continuation:
    // record the call as a pending write so that when `*dest = val`
    // occurs, it becomes an IndexedWrite. (#2124 Phase 4)
    if try_index_mut_continuation(ctx, func, args, destination, &state, accum) {
        register_range_index_mut_reborrow(ctx, args, destination, &mut state);
        // Don't bind the destination to an opaque variable — the
        // destination holds `&mut T` from index_mut, and the actual
        // value will be determined by the subsequent write.
        return super::super::extract_mut_borrow_from_block(ctx, target_bb, state, accum);
    }

    // Fn-trait calls (Fn::call, FnMut::call_mut, FnOnce::call_once)
    // must bail so that identity-final-value synthesis triggers (#537).
    if is_fn_trait_call(ctx.tcx, func) {
        return None;
    }

    // Mutation call continuation (#2124 Phase 5): when spec
    // advancement and IndexMut continuation both fail, continue
    // extraction and record the parameter as mutation-continued.
    // The identity `Deref(Var(name))` is preserved in deref_exprs
    // so that the ay layer creates `v_current`/`v_final` SMT
    // variables. The SMT encoder skips the identity `v_final ==
    // v_current` assertion for these params, letting
    // `call_assumptions` + `resolve_assertions` be the sole
    // constraints on the final value.
    let mut continued_roots = Vec::new();
    for arg in args {
        let local = match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => place.local,
            Operand::Constant(_) | Operand::RuntimeChecks(_) => continue,
        };
        let ty = ctx.body.local_decls[local].ty;
        if matches!(
            ty.kind(),
            TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
        ) {
            // Trace through EVERY tracking lane (whole, field and carrier
            // reborrows, slices, pending IndexMut) to the original param. A
            // field reborrow used to be missed here, leaving the identity
            // final-value premise for a mutated param (s34).
            if let Some(pl) = field_writes::tracked_root(ctx, &state, accum, local) {
                continued_roots.push(pl);
            }
        }
    }
    for pl in continued_roots {
        // Record the param as mutation-continued (#2124 Phase 5) and drop
        // every tracked referent a later read could observe stale (s34).
        field_writes::havoc_param(ctx, &mut state, accum, pl);
    }

    // Bind the call destination to an opaque variable.
    let dest_local = destination.local;
    let dest_sort = ty_to_expr_sort_enriched(ctx.tcx, ctx.body.local_decls[dest_local].ty);
    state.local_exprs.insert(
        dest_local,
        PureExpr::Var(format!("$_call_{}", dest_local.as_u32()), dest_sort),
    );

    super::super::extract_mut_borrow_from_block(ctx, target_bb, state, accum)
}

fn register_range_index_mut_reborrow<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
    state: &mut MutBorrowTraversalState,
) {
    if args.len() < 2 {
        return;
    }
    let Some(index_local) = extract_simple_local(&args[1].node) else {
        return;
    };
    if !is_range_inclusive_local(ctx, index_local) {
        return;
    }
    let Some(receiver_local) = extract_simple_local(&args[0].node) else {
        return;
    };
    let Some(parent_local) =
        resolve_reborrow_param_local(receiver_local, ctx.mut_borrow_params, &state.reborrow_map)
    else {
        return;
    };

    let range_expr = {
        let sort = ty_to_expr_sort_enriched(ctx.tcx, ctx.body.local_decls[index_local].ty);
        PureExpr::Var(format!("$call_{}", index_local.as_u32()), sort)
    };
    let start_expr = PureExpr::MethodCall {
        receiver: Arc::new(range_expr),
        method: "start_log".to_string(),
        args: vec![],
    };

    state.slice_reborrow_map.insert(
        destination.local,
        SliceReborrow {
            parent_local,
            start_expr,
        },
    );
}

fn is_range_inclusive_local(
    ctx: &MutBorrowBlockContext<'_, '_>,
    local: rustc_middle::mir::Local,
) -> bool {
    let ty = ctx.body.local_decls[local].ty;
    let ty_name = format!("{}", ty);
    ty_name.contains("RangeInclusive")
}

/// Check whether a Call is to `IndexMut::index_mut` and, if so, record
/// the pending metadata so that the subsequent `*dest = val` statement
/// synthesizes an `IndexedWrite`. (#2124 Phase 4)
///
/// Co-located with the Call terminator handler because it is only called
/// from `process_mutating_call`.
fn try_index_mut_continuation<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
    state: &MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) -> bool {
    if !is_index_mut_call(ctx.tcx, func) {
        return false;
    }

    // Need at least self + index arguments.
    if args.len() < 2 {
        return false;
    }

    // Find the receiver — must be a tracked &mut param.
    let Some((receiver_local, _expr)) =
        find_mutation_receiver(ctx, args, &state.deref_exprs, &state.reborrow_map)
    else {
        return false;
    };

    // Resolve the index expression from the second argument.
    let lookup = DerefLookup {
        locals: &state.local_exprs,
        deref_exprs: &state.deref_exprs,
        field_deref_exprs: &state.field_deref_exprs,
        carrier_read_locals: Some(&state.carrier_read_locals),
    };
    let Some(index_expr) = translate_operand(&args[1].node, &lookup) else {
        return false;
    };

    // Determine param name.
    let param_idx = receiver_local.as_usize().saturating_sub(1);
    let param_name = if param_idx < ctx.arg_names.len() {
        ctx.arg_names[param_idx].clone()
    } else {
        format!("$param_{}", receiver_local.as_u32())
    };

    // Record pending IndexMut metadata on the destination local.
    let dest_local = destination.local;
    accum.pending_index_mut.insert(
        dest_local,
        PendingIndexMut {
            param_name,
            index_expr,
            receiver_local,
        },
    );

    true
}

/// Extract a simple local from an operand (no projections).
///
/// Returns `Some(local)` for `Copy(local)` or `Move(local)` when the place
/// has no projections. Returns `None` for constants or places with projections.
fn extract_simple_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}
