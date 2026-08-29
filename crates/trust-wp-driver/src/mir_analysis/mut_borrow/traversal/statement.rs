// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Statement-level processing for mutable borrow extraction.
//!
//! Handles MIR `Assign` statements within `extract_mut_borrow_from_block`:
//! field reborrows, whole-value reborrows, indexed writes, deref writes,
//! and regular local assignments.

use std::sync::Arc;

use rustc_middle::mir::{Local, Operand, ProjectionElem, Rvalue, Statement, StatementKind};
use trust_wp_core::formula::{BinOp, PureExpr};

use super::super::{
    data::{
        DerefLookup, DerefTarget, IndexedWrite, MutBorrowAccumulators, MutBorrowBlockContext,
        MutBorrowTraversalState,
    },
    entry::make_typed_deref_expr,
    place_utils::{get_deref_target, resolve_reborrow_param_local},
    type_analysis::{self, is_newtype_wrapping_mut},
};
use crate::mir_analysis::translate::{translate_rvalue, ty_to_expr_sort_enriched};

/// Process all statements in a basic block, updating mutable borrow tracking state.
///
/// This is the statement-processing half of the `extract_mut_borrow_from_block`
/// traversal. It handles:
/// - Field reborrows: `_N = &mut (*_1).field`
/// - Whole-value reborrows: `_N = &mut (*_M)` (#1682)
/// - Field copy reborrows: `_N = Copy(_M.field)` where field is `&mut T` (#2124)
/// - Indexed writes: `(*_N)[_M] = val` (#1317)
/// - Pending IndexMut resolution: `*_dest = val` after `index_mut` call (#2124 Phase 4)
/// - Deref writes: `*v = expr` (whole) and `(*v).N = expr` (field)
/// - Regular local assignments
pub(in super::super) fn process_statements<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    statements: &[Statement<'tcx>],
    state: &mut MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) {
    for stmt in statements {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                process_assign(ctx, place, rvalue, state, accum);
            }
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {}
            StatementKind::FakeRead(_)
            | StatementKind::PlaceMention(_)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(_)
            | StatementKind::ConstEvalCounter
            | StatementKind::BackwardIncompatibleDropHint { .. }
            | StatementKind::Intrinsic(box rustc_middle::mir::NonDivergingIntrinsic::Assume(_)) => {
            }
            StatementKind::SetDiscriminant { .. }
            | StatementKind::Intrinsic(
                box rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(_),
            ) => {
                // These statements can mutate memory outside the assignment
                // tracker. A later nested transfer must not mint expiry facts
                // from a state that may already be stale.
                accum.nested_transfer_poisoned = true;
            }
        }
    }
}

/// Process a single `Assign` statement.
#[allow(clippy::too_many_lines)]
fn process_assign<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    place: &rustc_middle::mir::Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
    state: &mut MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) {
    // Detect field reborrows: _N = &mut (*_1).field
    // Track that _N reborrows a specific capture field, and
    // also register the field's current expression in deref_exprs
    // for _N so reads through *_N resolve to the field value.
    //
    // Also detect whole-value reborrows: _N = &mut (*_M) (#1682)
    // Track that _N reborrows _M (or transitively, whichever
    // &mut param _M itself reborrows).
    if place.projection.is_empty() {
        state.field_reborrow_map.remove(&place.local);
        state.reborrow_map.remove(&place.local);
        state.slice_reborrow_map.remove(&place.local);
        state.slot_borrow_map.remove(&place.local);
        if let Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Mut { .. }, ref_place) = rvalue {
            let ref_projs: Vec<_> = ref_place.projection.iter().collect();
            // Nested slot borrow: `_tmp = &mut ma` where `ma` is itself a
            // `&mut T`-typed parameter slot (projection-less borrow OF the
            // local, not of its pointee). Track tmp → slot so a following
            // transfer call (`swap(&mut ma, &mut mb)`) can be recognized.
            if ref_projs.is_empty()
                && ctx.mut_borrow_params.contains(&ref_place.local)
                && matches!(
                    ctx.body.local_decls[ref_place.local].ty.kind(),
                    rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                )
            {
                state.slot_borrow_map.insert(place.local, ref_place.local);
            }
            // Reborrow of a nested slot borrow: `_arg = &mut (*_tmp)` where
            // `_tmp` is a tracked slot borrow — `_arg` borrows the SAME slot.
            // (rustc emits this shape for two-phase call arguments.)
            if let [ProjectionElem::Deref] = ref_projs.as_slice() {
                if let Some(&slot) = state.slot_borrow_map.get(&ref_place.local) {
                    state.slot_borrow_map.insert(place.local, slot);
                }
            }
            if ref_projs.len() == 2 {
                if let (ProjectionElem::Deref, ProjectionElem::Field(field, _)) =
                    (ref_projs[0], ref_projs[1])
                {
                    let base = ref_place.local;
                    if ctx.mut_borrow_params.contains(&base) {
                        let field_idx = field.as_u32();
                        state
                            .field_reborrow_map
                            .insert(place.local, (base, field_idx));
                        // Register the field's tracked value for reads
                        // through *_N (the reborrow local).
                        if let Some(field_expr) =
                            state.field_deref_exprs.get(&(base, field_idx)).cloned()
                        {
                            state.deref_exprs.insert(place.local, field_expr);
                        }
                    }
                }
            }
            // Detect whole-value reborrows: _N = &mut (*_M)
            // where ref_place has projection [Deref] only. (#1682)
            if ref_projs.len() == 1 {
                if let ProjectionElem::Deref = ref_projs[0] {
                    if let Some(slice_reborrow) =
                        state.slice_reborrow_map.get(&ref_place.local).cloned()
                    {
                        state.slice_reborrow_map.insert(place.local, slice_reborrow);
                    } else if let Some(origin) = resolve_reborrow_param_local(
                        ref_place.local,
                        ctx.mut_borrow_params,
                        &state.reborrow_map,
                    ) {
                        state.reborrow_map.insert(place.local, origin);
                        let param_name = param_name_for_local(ctx, origin);
                        let current =
                            state.deref_exprs.get(&origin).cloned().unwrap_or_else(|| {
                                make_typed_deref_expr(ctx.tcx, ctx.body, origin, &param_name)
                            });
                        state.deref_exprs.insert(place.local, current);
                    }
                }
            }
        }

        // Detect field copy reborrows: _N = Copy/Move(_M.field)
        // where _M is a mut_borrow param and the field type is `&mut T`.
        // This occurs when a newtype wrapping `&mut T` (e.g., `HasMutRef`)
        // is accessed via field projection rather than `&mut` reborrow.
        // MIR: `_2 = copy (_1.0: &mut u32)` for `*x.0 = 5`. (#2124)
        //
        // Also detect closure capture field moves through a deref:
        // _N = Move((*_1).field) where field type eventually contains `&mut T`.
        // This covers Box-wrapped captures like `Box<&mut T>` (#2318).
        // MIR: `_4 = move ((*_1).1: Box<&mut i32>)` when `let bx2 = bx;`
        // inside a closure that captured `bx: Box<&mut i32>` as self.1.
        // A Use retag transfers runtime provenance but does not create a new
        // logical borrow/writeback edge; the source place is identical in both
        // modes.
        if let Rvalue::Use(Operand::Copy(src_place) | Operand::Move(src_place), _) = rvalue {
            let src_projs: Vec<_> = src_place.projection.iter().collect();
            // Move/copy of a nested slot borrow: `_arg = move _tmp` where
            // `_tmp` is a tracked slot borrow — `_arg` is the same borrow.
            if src_projs.is_empty() {
                if let Some(&slot) = state.slot_borrow_map.get(&src_place.local) {
                    state.slot_borrow_map.insert(place.local, slot);
                }
            }
            // Pattern 1: _N = Copy/Move(_M.field) — direct field access
            if src_projs.len() == 1 {
                if let ProjectionElem::Field(field, field_ty) = src_projs[0] {
                    if type_analysis::type_eventually_contains_mut_ref(ctx.tcx, field_ty) {
                        let base = src_place.local;
                        let resolved = if ctx.mut_borrow_params.contains(&base) {
                            Some(base)
                        } else {
                            state.reborrow_map.get(&base).copied()
                        };
                        if let Some(param_local) = resolved {
                            let field_idx = field.as_u32();
                            state
                                .field_reborrow_map
                                .insert(place.local, (param_local, field_idx));
                            // Register the field's tracked value for reads
                            // through *_N.
                            if let Some(field_expr) = state
                                .field_deref_exprs
                                .get(&(param_local, field_idx))
                                .cloned()
                            {
                                state.deref_exprs.insert(place.local, field_expr);
                            }
                        }
                    }
                }
            }
            // Pattern 2: _N = Copy/Move((*_M).field) — closure capture field
            // through a deref, where the field type contains `&mut T` at any
            // depth (Box<&mut T>, Box<Box<&mut T>>, etc.). (#2318)
            if src_projs.len() == 2 {
                if let (ProjectionElem::Deref, ProjectionElem::Field(field, field_ty)) =
                    (src_projs[0], src_projs[1])
                {
                    let base = src_place.local;
                    let resolved = if ctx.mut_borrow_params.contains(&base) {
                        Some(base)
                    } else {
                        state.reborrow_map.get(&base).copied()
                    };
                    if let Some(param_local) = resolved {
                        // Accept both direct &mut T and nested wrappers (Box<&mut T>).
                        if type_analysis::type_eventually_contains_mut_ref(ctx.tcx, field_ty) {
                            let field_idx = field.as_u32();
                            state
                                .field_reborrow_map
                                .insert(place.local, (param_local, field_idx));
                            if let Some(field_expr) = state
                                .field_deref_exprs
                                .get(&(param_local, field_idx))
                                .cloned()
                            {
                                state.deref_exprs.insert(place.local, field_expr);
                            }
                        }
                    }
                }
            }
        }
    }

    // Check for writes through field reborrows FIRST: *_N where _N
    // was previously recorded as a reborrow of a capture field.
    // This must happen before get_deref_target because that function's
    // generic reborrow heuristic would match *_N as Whole(param),
    // preventing field-level tracking.
    //
    // Generalized for Box wrappers (#2318): accept one or more trailing
    // Deref projections. For Box<&mut T>, the write is **_N = expr
    // which has projections [Deref, Deref]. For Box<Box<&mut T>>,
    // it's [Deref, Deref, Deref].
    let field_reborrow_target = {
        let projs: Vec<_> = place.projection.iter().collect();
        if !projs.is_empty() && projs.iter().all(|p| matches!(p, ProjectionElem::Deref)) {
            state.field_reborrow_map.get(&place.local).copied()
        } else {
            None
        }
    };

    if let Some((param_local, field_idx)) = field_reborrow_target {
        // Write through field reborrow: *_N = expr where _N reborrows (*_1).field
        let lookup = DerefLookup {
            locals: &state.local_exprs,
            deref_exprs: &state.deref_exprs,
            field_deref_exprs: &state.field_deref_exprs,
        };
        if let Some(expr) = translate_rvalue(rvalue, &lookup, Some(ctx.body)) {
            state
                .field_deref_exprs
                .insert((param_local, field_idx), expr);
        } else {
            accum.nested_transfer_poisoned = true;
        }
    } else {
        process_non_field_reborrow_write(ctx, place, rvalue, state, accum);
    }
}

/// Process a write that is NOT through a field reborrow.
///
/// Handles indexed writes, pending IndexMut resolution, deref writes,
/// and regular local assignments.
fn process_non_field_reborrow_write<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    place: &rustc_middle::mir::Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
    state: &mut MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) {
    // Check for indexed writes: (*_N)[_M] = val (#1317).
    // MIR for `a[2] = 3` on `&mut [u32]` generates a place
    // with projections [Deref, Index(idx_local)] on a reborrow
    // of the `&mut` param. Record these as IndexedWrite entries
    // so the verification code can synthesize IndexMut postconditions.
    let indexed_write_detected = try_indexed_write(ctx, place, rvalue, state, accum);

    if !indexed_write_detected {
        // Check for writes through pending IndexMut results:
        // *_dest = val where _dest was returned by index_mut. (#2124 Phase 4)
        let pending_resolved = {
            let projs: Vec<_> = place.projection.iter().collect();
            if projs.len() == 1 {
                if let ProjectionElem::Deref = projs[0] {
                    accum.pending_index_mut.get(&place.local).cloned()
                } else {
                    None
                }
            } else {
                None
            }
        };
        if let Some(pending) = pending_resolved {
            process_pending_index_mut_write(ctx, place, rvalue, state, &pending, accum);
        } else {
            // Not a field reborrow — check for other deref writes.
            process_deref_or_local_write(ctx, place, rvalue, state, accum);
        }
    }
}

/// Try to detect and record an indexed write: `(*_N)[_M] = val`.
fn try_indexed_write<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    place: &rustc_middle::mir::Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
    state: &mut MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) -> bool {
    let projs: Vec<_> = place.projection.iter().collect();
    if projs.len() != 2 {
        return false;
    }
    let (ProjectionElem::Deref, ProjectionElem::Index(idx_local)) = (projs[0], projs[1]) else {
        return false;
    };

    let lookup = DerefLookup {
        locals: &state.local_exprs,
        deref_exprs: &state.deref_exprs,
        field_deref_exprs: &state.field_deref_exprs,
    };
    let idx_expr = state
        .local_exprs
        .get(&idx_local)
        .cloned()
        .unwrap_or_else(|| {
            let sort = ty_to_expr_sort_enriched(ctx.tcx, ctx.body.local_decls[idx_local].ty);
            PureExpr::Var(format!("_{}", idx_local.as_u32()), sort)
        });
    let Some(val_expr) = translate_rvalue(rvalue, &lookup, Some(ctx.body)) else {
        accum.nested_transfer_poisoned = true;
        return false;
    };

    if let Some(slice_reborrow) = state.slice_reborrow_map.get(&place.local).cloned() {
        let parent_idx_expr = PureExpr::BinOp(
            Arc::new(slice_reborrow.start_expr),
            BinOp::Add,
            Arc::new(idx_expr),
        );
        record_indexed_write_and_advance(
            ctx,
            state,
            accum,
            slice_reborrow.parent_local,
            parent_idx_expr,
            val_expr,
        );
        return true;
    }

    // Find which &mut param this reborrow refers to.
    let Some(param_local) =
        resolve_reborrow_param_local(place.local, ctx.mut_borrow_params, &state.reborrow_map)
    else {
        return false;
    };

    record_indexed_write_and_advance(ctx, state, accum, param_local, idx_expr, val_expr);
    true
}

fn record_indexed_write_and_advance<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    state: &mut MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
    param_local: Local,
    idx_expr: PureExpr,
    val_expr: PureExpr,
) {
    let param_idx = param_local.as_usize().saturating_sub(1);
    let param_name = if param_idx < ctx.arg_names.len() {
        ctx.arg_names[param_idx].clone()
    } else {
        format!("_param_{}", param_local.as_u32())
    };
    accum.indexed_writes.push(IndexedWrite {
        param_name: param_name.clone(),
        index: idx_expr.clone(),
        value: val_expr.clone(),
    });

    let current_state = state
        .deref_exprs
        .get(&param_local)
        .cloned()
        .unwrap_or_else(|| make_typed_deref_expr(ctx.tcx, ctx.body, param_local, &param_name));
    let new_state = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(current_state))),
        method: "set".to_string(),
        args: vec![idx_expr, val_expr],
    };
    state.deref_exprs.insert(param_local, new_state);
}

/// Process a write through a pending IndexMut result: `*_dest = val`.
fn process_pending_index_mut_write<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    place: &rustc_middle::mir::Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
    state: &mut MutBorrowTraversalState,
    pending: &super::super::data::PendingIndexMut,
    accum: &mut MutBorrowAccumulators,
) {
    let lookup = DerefLookup {
        locals: &state.local_exprs,
        deref_exprs: &state.deref_exprs,
        field_deref_exprs: &state.field_deref_exprs,
    };
    if let Some(val_expr) = translate_rvalue(rvalue, &lookup, Some(ctx.body)) {
        accum.indexed_writes.push(IndexedWrite {
            param_name: pending.param_name.clone(),
            index: pending.index_expr.clone(),
            value: val_expr.clone(),
        });

        // Phase 5 (#2124): Advance the receiver's
        // intermediate symbolic state so subsequent
        // in-body reads see the written value. The new
        // state is `View(old_state).set(idx, val)` —
        // a Seq-model pointwise update analogous to
        // how spec advancement produces
        // `View(old_state).push_back(val)` for push.
        let current_state = state
            .deref_exprs
            .get(&pending.receiver_local)
            .cloned()
            .unwrap_or_else(|| {
                make_typed_deref_expr(
                    ctx.tcx,
                    ctx.body,
                    pending.receiver_local,
                    &pending.param_name,
                )
            });
        let new_state = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(current_state))),
            method: "set".to_string(),
            args: vec![pending.index_expr.clone(), val_expr],
        };
        state.deref_exprs.insert(pending.receiver_local, new_state);
    } else {
        accum.nested_transfer_poisoned = true;
    }
    // Remove the pending entry now that it's resolved.
    accum.pending_index_mut.remove(&place.local);
}

/// Process a deref write or regular local assignment.
fn process_deref_or_local_write<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    place: &rustc_middle::mir::Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
    state: &mut MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
) {
    let target = get_deref_target(place, ctx.body, ctx.mut_borrow_params, &state.reborrow_map);
    match target {
        Some(DerefTarget::Whole(deref_local)) => {
            // *v = expr, update whole deref_exprs
            let lookup = DerefLookup {
                locals: &state.local_exprs,
                deref_exprs: &state.deref_exprs,
                field_deref_exprs: &state.field_deref_exprs,
            };
            if let Some(expr) = translate_rvalue(rvalue, &lookup, Some(ctx.body)) {
                // Keep whole and field-0 tracking in sync for
                // newtype wrappers around `&mut T` (`x.0`).
                if is_newtype_wrapping_mut(ctx.tcx, ctx.body.local_decls[deref_local].ty) {
                    state
                        .field_deref_exprs
                        .insert((deref_local, 0), expr.clone());
                }
                set_whole_deref_expr(state, deref_local, expr);
            } else {
                // The write's value could not be translated: the tracked
                // pointee value for this slot is now stale. Nested-slot expiry
                // resolutions would pair a correct content with a wrong value,
                // so poison them (fail-closed; identity `final_values` behave
                // exactly as before this feature).
                accum.nested_transfer_poisoned = true;
            }
        }
        Some(DerefTarget::Field(deref_local, field_idx)) => {
            // (*v).N = expr, update field deref_exprs
            let lookup = DerefLookup {
                locals: &state.local_exprs,
                deref_exprs: &state.deref_exprs,
                field_deref_exprs: &state.field_deref_exprs,
            };
            if let Some(expr) = translate_rvalue(rvalue, &lookup, Some(ctx.body)) {
                state
                    .field_deref_exprs
                    .insert((deref_local, field_idx), expr);
            } else {
                accum.nested_transfer_poisoned = true;
            }
        }
        None => {
            // Regular local assignment
            let local = place.local;
            if place.projection.is_empty() && ctx.mut_borrow_params.contains(&local) {
                // A direct assignment to an `&mut` parameter rebinds the slot
                // without going through the recognized transfer semantics.
                // Even when it occurs before the first transfer, poison the
                // whole function so a later transfer cannot emit expiry facts
                // from stale slot-content tracking.
                accum.nested_transfer_poisoned = true;
            }
            let lookup = DerefLookup {
                locals: &state.local_exprs,
                deref_exprs: &state.deref_exprs,
                field_deref_exprs: &state.field_deref_exprs,
            };
            if let Some(expr) = translate_rvalue(rvalue, &lookup, Some(ctx.body)) {
                state.local_exprs.insert(local, expr);
            }
        }
    }
}

fn param_name_for_local(ctx: &MutBorrowBlockContext<'_, '_>, local: Local) -> String {
    local
        .as_usize()
        .checked_sub(1)
        .and_then(|idx| ctx.arg_names.get(idx))
        .cloned()
        .unwrap_or_else(|| format!("_param_{}", local.as_u32()))
}

fn set_whole_deref_expr(state: &mut MutBorrowTraversalState, deref_local: Local, expr: PureExpr) {
    state.deref_exprs.insert(deref_local, expr.clone());
    let aliases: Vec<Local> = state
        .reborrow_map
        .iter()
        .filter_map(|(local, origin)| (*origin == deref_local).then_some(*local))
        .collect();
    for alias in aliases {
        state.deref_exprs.insert(alias, expr.clone());
    }
}
