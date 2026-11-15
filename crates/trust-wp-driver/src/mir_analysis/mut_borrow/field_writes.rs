// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Field writes through `&mut` parameters, and the fail-closed havoc lane.
//!
//! # Value carriers
//!
//! A *value carrier* is a `&mut T` parameter whose referent `T` is a struct or
//! tuple that contains no `&mut` anywhere. For such a parameter every write to
//! a field path `(*p).f1.f2...fk = e` is a FUNCTIONAL UPDATE of the tracked
//! whole referent value:
//!
//! ```text
//! upd(cur, [i, rest..], e) = tupleN(get_0(cur), .., upd(get_i(cur), rest, e), .., get_{N-1}(cur))
//! ```
//!
//! and every read `(*p).f1...fk` is the projection of the tracked whole value.
//! This is literally Rust's semantics of a place write; the final value of the
//! borrow is the whole referent at exit, so it reflects every field write in
//! program order (whole writes and field writes interleave correctly because
//! both act on the single whole value), and branch merges merge whole values.
//!
//! # Havoc (fail-closed)
//!
//! Any write that reaches a tracked parameter's referent but cannot be
//! represented EXACTLY — an untranslatable right-hand side, an unsupported
//! projection (downcast, index inside a carrier, ...), an untracked `&mut` into
//! the referent, a tracked borrow escaping into an aggregate — *havocs* the
//! parameter: its final-value premise is removed (the parameter joins
//! `mutation_continued_params`, so the ay layer asserts neither the final value
//! nor the identity resolve), its per-field final entries and indexed writes are
//! dropped, and its tracked referent is removed from the traversal state so no
//! later read can observe a stale value. Havoc only ever REMOVES premises.

use std::collections::HashMap;

use rustc_middle::{
    mir::{Local, Place, ProjectionElem},
    ty::{Ty, TyCtxt, TyKind},
};
use trust_wp_core::formula::{
    internal::tuple_lowering::{
        tuple_field_logic_fn_name, tuple_logic_fn_arity, tuple_logic_fn_name,
    },
    PureExpr,
};

use super::{
    data::{MutBorrowAccumulators, MutBorrowBlockContext, MutBorrowTraversalState},
    type_analysis::type_eventually_contains_mut_ref,
};

/// The referent type of a value-carrier parameter, or `None` when `local` is
/// not a value carrier.
pub(super) fn value_carrier_referent<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Mut) = ty.kind() else {
        return None;
    };
    let inner = *inner;
    let is_record = match inner.kind() {
        TyKind::Adt(adt_def, _) => adt_def.is_struct() && !adt_def.is_box(),
        TyKind::Tuple(fields) => !fields.is_empty(),
        _ => false,
    };
    if !is_record || type_eventually_contains_mut_ref(tcx, inner) {
        return None;
    }
    Some(inner)
}

/// Whether the tracked parameter `local` is a value carrier.
pub(super) fn is_value_carrier_param(ctx: &MutBorrowBlockContext<'_, '_>, local: Local) -> bool {
    ctx.mut_borrow_params.contains(&local)
        && value_carrier_referent(ctx.tcx, ctx.body.local_decls[local].ty).is_some()
}

/// Arity of a record type and the type of its field `idx`.
fn record_field<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, idx: u32) -> Option<(usize, Ty<'tcx>)> {
    match ty.kind() {
        TyKind::Tuple(fields) => Some((fields.len(), *fields.get(idx as usize)?)),
        TyKind::Adt(adt_def, substs) if adt_def.is_struct() && !adt_def.is_box() => {
            let variant = adt_def.non_enum_variant();
            let field = variant.fields.iter().nth(idx as usize)?;
            Some((variant.fields.len(), field.ty(tcx, *substs).skip_norm_wip()))
        }
        _ => None,
    }
}

/// `get_idx(base)`, simplified when `base` is a tuple constructor.
pub(super) fn project_field(base: &PureExpr, idx: u32) -> PureExpr {
    if let PureExpr::LogicFnCall { name, args } = base {
        if tuple_logic_fn_arity(name).is_some_and(|arity| arity == args.len()) {
            if let Some(arg) = args.get(idx as usize) {
                return arg.clone();
            }
        }
    }
    PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(idx as usize),
        args: vec![base.clone()],
    }
}

/// Project a field path.
pub(super) fn project_path(base: &PureExpr, path: &[u32]) -> PureExpr {
    path.iter()
        .fold(base.clone(), |acc, idx| project_field(&acc, *idx))
}

/// Functional update of `cur` (of record type `ty`) at `path` with `value`.
///
/// Returns `None` when a step's type is not a record with a known arity; the
/// caller must then havoc (the write cannot be represented exactly).
pub(super) fn functional_update<'tcx>(
    tcx: TyCtxt<'tcx>,
    cur: &PureExpr,
    ty: Ty<'tcx>,
    path: &[u32],
    value: PureExpr,
) -> Option<PureExpr> {
    let Some((&idx, rest)) = path.split_first() else {
        return Some(value);
    };
    let (arity, field_ty) = record_field(tcx, ty, idx)?;
    let child = project_field(cur, idx);
    let new_child = functional_update(tcx, &child, field_ty, rest, value)?;
    let args = (0..arity)
        .map(|j| {
            if j == idx as usize {
                new_child.clone()
            } else {
                project_field(cur, j as u32)
            }
        })
        .collect();
    Some(PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(arity),
        args,
    })
}

/// Classification of a place that may address a value carrier's referent.
#[derive(Debug, PartialEq, Eq)]
pub(super) enum CarrierPlace {
    /// A field path (non-empty) inside the referent of carrier param `.0`.
    Path(Local, Vec<u32>),
    /// Addresses the carrier's referent through a projection that cannot be
    /// represented exactly.
    Unsupported(Local),
    /// Not a (strict) field place of a value carrier.
    NotCarrier,
}

/// Classify `place` against the value carriers.
///
/// The base local may be the carrier parameter itself, a whole reborrow of it
/// (`reborrow_map`), or a tracked carrier field reborrow.
pub(super) fn classify_carrier_place(
    ctx: &MutBorrowBlockContext<'_, '_>,
    state: &MutBorrowTraversalState,
    place: &Place<'_>,
) -> CarrierPlace {
    let local = place.local;
    let (param, base_path) = if let Some((param, path)) = state.carrier_field_reborrows.get(&local)
    {
        (*param, path.clone())
    } else if is_value_carrier_param(ctx, local) {
        (local, Vec::new())
    } else if let Some(&origin) = state.reborrow_map.get(&local) {
        if !is_value_carrier_param(ctx, origin) {
            return CarrierPlace::NotCarrier;
        }
        (origin, Vec::new())
    } else {
        return CarrierPlace::NotCarrier;
    };

    let projections: Vec<_> = place.projection.iter().collect();
    let Some((first, rest)) = projections.split_first() else {
        return CarrierPlace::NotCarrier;
    };
    if !matches!(first, ProjectionElem::Deref) {
        return CarrierPlace::Unsupported(param);
    }
    let mut path = base_path;
    for proj in rest {
        match proj {
            ProjectionElem::Field(field, _) => path.push(field.as_u32()),
            _ => return CarrierPlace::Unsupported(param),
        }
    }
    if path.is_empty() {
        // `*p` / `*reborrow`: the whole referent, handled by the Whole lane.
        return CarrierPlace::NotCarrier;
    }
    CarrierPlace::Path(param, path)
}

/// Refresh the tracked referent of every carrier field reborrow of `param`
/// after `param`'s whole value changed.
pub(super) fn refresh_carrier_aliases(state: &mut MutBorrowTraversalState, param: Local) {
    let Some(whole) = state.deref_exprs.get(&param).cloned() else {
        return;
    };
    let aliases: Vec<(Local, Vec<u32>)> = state
        .carrier_field_reborrows
        .iter()
        .filter(|(_, (p, _))| *p == param)
        .map(|(alias, (_, path))| (*alias, path.clone()))
        .collect();
    for (alias, path) in aliases {
        state.deref_exprs.insert(alias, project_path(&whole, &path));
    }
}

/// Resolve a local to the tracked parameter whose referent it can reach.
pub(super) fn tracked_root(
    ctx: &MutBorrowBlockContext<'_, '_>,
    state: &MutBorrowTraversalState,
    accum: &MutBorrowAccumulators,
    local: Local,
) -> Option<Local> {
    if ctx.mut_borrow_params.contains(&local) {
        return Some(local);
    }
    if let Some(&origin) = state.reborrow_map.get(&local) {
        return Some(origin);
    }
    if let Some(&(param, _)) = state.field_reborrow_map.get(&local) {
        return Some(param);
    }
    if let Some((param, _)) = state.carrier_field_reborrows.get(&local) {
        return Some(*param);
    }
    if let Some(slice) = state.slice_reborrow_map.get(&local) {
        return Some(slice.parent_local);
    }
    if let Some(&slot) = state.slot_borrow_map.get(&local) {
        return Some(slot);
    }
    if let Some(pending) = accum.pending_index_mut.get(&local) {
        return Some(pending.receiver_local);
    }
    // Last, because it is the least precise lane: a pointer into the SLOT of
    // a tracked borrow names the root param, not the borrow it happens to
    // hold right now. Every caller of this function havocs what it returns,
    // so a root reached this way can only delete a premise.
    state.slot_alias_roots.get(&local).copied()
}

/// Havoc tracked parameter `param`: remove its final-value premise and every
/// traversal fact through which a later read could observe its (now unknown)
/// referent.
pub(super) fn havoc_param(
    ctx: &MutBorrowBlockContext<'_, '_>,
    state: &mut MutBorrowTraversalState,
    accum: &mut MutBorrowAccumulators,
    param: Local,
) {
    accum.havoc_params.insert(param);
    if let Some(name) = param
        .as_usize()
        .checked_sub(1)
        .and_then(|idx| ctx.arg_names.get(idx))
    {
        accum.mutation_continued_params.insert(name.clone());
    }
    // A havocked pointee makes any nested-slot expiry value stale.
    accum.nested_transfer_poisoned = true;

    let mut aliases: Vec<Local> = vec![param];
    aliases.extend(
        state
            .reborrow_map
            .iter()
            .filter(|(_, origin)| **origin == param)
            .map(|(local, _)| *local),
    );
    aliases.extend(
        state
            .field_reborrow_map
            .iter()
            .filter(|(_, (origin, _))| *origin == param)
            .map(|(local, _)| *local),
    );
    aliases.extend(
        state
            .carrier_field_reborrows
            .iter()
            .filter(|(_, (origin, _))| *origin == param)
            .map(|(local, _)| *local),
    );
    for alias in aliases {
        state.deref_exprs.remove(&alias);
        state.local_exprs.remove(&alias);
    }
    state
        .field_deref_exprs
        .retain(|(local, _), _| *local != param);
}

/// Whether `param` has been havocked.
pub(super) fn is_havocked(accum: &MutBorrowAccumulators, param: Local) -> bool {
    accum.havoc_params.contains(&param)
}

/// Build the per-field final entries (`"p.i"`) for a carrier's written
/// top-level fields from its final whole value.
pub(super) fn carrier_field_final_entries(
    name: &str,
    whole_final: &PureExpr,
    fields: impl IntoIterator<Item = u32>,
) -> HashMap<String, PureExpr> {
    fields
        .into_iter()
        .map(|idx| (format!("{name}.{idx}"), project_field(whole_final, idx)))
        .collect()
}

/// `true` when `expr` is exactly the typed identity `Deref(Var(name))`.
pub(super) fn is_identity_deref(name: &str, expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == name))
}

/// For a NON-carrier parameter written through a per-field entry
/// (`field_deref_exprs`): whether the write keeps the per-field
/// reconstruction exact. Per-field entries of a non-closure `&mut` record
/// parameter are reconstructed over the ENTRY value (Phase 3), so they are only
/// exact for fields that hold a `&mut` (pointee writes) and when no whole write
/// happened. Closure environments and by-value carriers keep their semantics.
pub(super) fn per_field_write_is_exact(
    ctx: &MutBorrowBlockContext<'_, '_>,
    accum: &MutBorrowAccumulators,
    param: Local,
    field_idx: u32,
) -> bool {
    let TyKind::Ref(_, pointee, _) = ctx.body.local_decls[param].ty.kind() else {
        return true;
    };
    if matches!(
        pointee.kind(),
        TyKind::Closure(..) | TyKind::Coroutine(..) | TyKind::CoroutineClosure(..)
    ) {
        return true;
    }
    if accum.whole_written_params.contains(&param) {
        return false;
    }
    match record_field(ctx.tcx, *pointee, field_idx) {
        Some((_, field_ty)) => type_eventually_contains_mut_ref(ctx.tcx, field_ty),
        None => false,
    }
}

/// Whether `place` writes through a borrow held in a field of a `&mut`
/// parameter's referent: a dereference AFTER its first field projection
/// (`(*x).0.*`, `(*x).0.*.*` through a `Box`), not a store into the field
/// itself (`(*x).0 = e`). (D-184)
pub(super) fn writes_through_a_held_borrow(place: &Place<'_>) -> bool {
    place
        .projection
        .iter()
        .skip_while(|p| !matches!(p, ProjectionElem::Field(..)))
        .any(|p| matches!(p, ProjectionElem::Deref))
}

/// Whether `param`'s referent is a closure environment.
pub(super) fn is_closure_env_param(ctx: &MutBorrowBlockContext<'_, '_>, param: Local) -> bool {
    matches!(
        ctx.body.local_decls[param].ty.kind(),
        TyKind::Ref(_, pointee, _) if matches!(
            pointee.kind(),
            TyKind::Closure(..) | TyKind::Coroutine(..) | TyKind::CoroutineClosure(..)
        )
    )
}
