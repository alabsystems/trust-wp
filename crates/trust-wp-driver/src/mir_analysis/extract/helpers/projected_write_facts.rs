// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Helpers for recording and injecting projected-write facts.

use std::{collections::HashMap, sync::Arc};

use rustc_middle::mir::{Body, Local, Place, ProjectionElem};
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::{
    super::super::translate::{translate_place, ty_to_expr_sort_enriched},
    source_name_for_local,
};

/// Wrap an expression with projected write facts as `LetAssume` nodes.
///
/// Applies facts in reverse order (latest first) so the innermost assumption
/// is the most recent write - matching the injection order at cutoff. Returns
/// `None` unchanged, and passes through empty fact vectors without wrapping.
pub(in super::super) fn wrap_projected_facts(
    facts: Vec<(PureExpr, PureExpr)>,
    expr: Option<PureExpr>,
) -> Option<PureExpr> {
    let mut inner = expr?;
    for (lhs, rhs) in facts.into_iter().rev() {
        let fact = PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs));
        inner = PureExpr::LetAssume {
            assumption: Arc::new(fact),
            body: Arc::new(inner),
        };
    }
    Some(inner)
}

/// Record a projected write fact with last-write-wins semantics.
///
/// If the same projected LHS is written more than once before a proof_assert
/// cutoff point, keep only the most recent equality. Retaining stale equalities
/// can create contradictory assumptions and vacuous verification. (#1424)
pub(in super::super) fn record_projected_write_fact(
    projected_write_facts: &mut Vec<(PureExpr, PureExpr)>,
    lhs: PureExpr,
    rhs: PureExpr,
) {
    if let Some(existing_pos) = projected_write_facts
        .iter()
        .position(|(existing_lhs, _)| existing_lhs == &lhs)
    {
        projected_write_facts.remove(existing_pos);
    }
    projected_write_facts.push((lhs, rhs));
}

/// Check whether a `PureExpr` contains a `Var` node with the given name.
///
/// Used to invalidate stale projected-write facts when a whole-local
/// reassignment occurs: any fact whose LHS references the reassigned local's
/// source name must be removed. (#1450)
pub(in super::super) fn expr_references_var_name(expr: &PureExpr, name: &str) -> bool {
    expr.any_free_var(|var, _| var == name)
}

/// Check whether `expr` contains `target` as a (possibly equal) sub-expression.
pub(super) fn expr_contains_subexpr(expr: &PureExpr, target: &PureExpr) -> bool {
    expr.any_recursive(|node| node == target)
}

/// Remove projected-write facts whose paths overlap the newly written path.
///
/// Writing a projected path invalidates both:
/// - descendant facts (`x.a = ...` invalidates prior `x.a.b == ...`)
/// - ancestor facts (`x.a.b = ...` invalidates prior `x.a == ...`)
///
/// Sibling paths remain valid (`x.a` and `x.c` are disjoint). (#1500)
pub(in super::super) fn invalidate_overlapping_projected_write_facts(
    projected_write_facts: &mut Vec<(PureExpr, PureExpr)>,
    written_lhs: &PureExpr,
) {
    projected_write_facts.retain(|(existing_lhs, _)| {
        !expr_contains_subexpr(existing_lhs, written_lhs)
            && !expr_contains_subexpr(written_lhs, existing_lhs)
    });
}

/// Translate projected-write LHS using source-local identity when available.
///
/// For source-named locals (including function args), projected writes should
/// produce symbolic paths like `tuple_get_0(pair)` rather than simplifying via
/// the local's current value (e.g., `tuple_get_0(tuple_1(0)) -> 0`). The latter
/// can turn write facts into constant equalities and create vacuous proofs.
/// Uses enriched ADT sort resolution via the provided `TyCtxt`.
pub(in super::super) fn translate_projected_write_lhs<'tcx>(
    body: &Body<'tcx>,
    place: &Place<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
    arg_names: &[String],
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
) -> Option<PureExpr> {
    let mut symbolic_locals = local_exprs.clone();
    let source_name = source_name_for_local(body, place.local, arg_names);
    if let Some(name) = source_name.clone() {
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[place.local].ty);
        symbolic_locals.insert(place.local, PureExpr::Var(name, sort));
    } else if let Some(existing) = local_exprs.get(&place.local) {
        // Fallback for anonymous intermediates (e.g., deref_mut borrow
        // carriers in ghost blocks): if the local currently holds a
        // compound expression (not a Var), replace it with a fresh
        // symbolic identity so the projected-write LHS stays in
        // symbolic form instead of collapsing through the concrete
        // value (e.g., `tuple_get_0(tuple2(2,3))` → `2`). (#2533)
        if !matches!(existing, PureExpr::Var(..)) {
            let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[place.local].ty);
            let synthetic_name = format!("_local_{}", place.local.as_u32());
            symbolic_locals.insert(place.local, PureExpr::Var(synthetic_name, sort));
        }
    }

    // Projected-write facts for anonymous `&mut` call results must preserve the
    // top-level dereference. General place translation intentionally collapses
    // `*_tmp` to the carrier local, but for writes that turns `*_tmp = 2` into
    // `_tmp == 2` instead of `Deref(_tmp) == 2`, which loses the pointee
    // update. Keep the existing aliasing behaviour for source-named locals
    // (`*x = v`) and only preserve the deref for anonymous mut-ref carriers.
    if source_name.is_none()
        && matches!(place.projection.as_ref(), [ProjectionElem::Deref])
        && matches!(
            ty_to_expr_sort_enriched(tcx, body.local_decls[place.local].ty),
            Some(ExprSort::MutRef(_))
        )
    {
        let base = symbolic_locals.get(&place.local)?.clone();
        return Some(PureExpr::Deref(Arc::new(base)));
    }

    // Box-wrapped `&mut T` writes: `(**bx) = v` where `bx: Box<&mut T>`.
    // Box deref is transparent in the expression model (both Deref projections
    // become no-ops), so translate_place would produce `Var("bx")` when the
    // correct LHS is `Deref(Var("bx"))` (the pointee of the &mut inside the
    // Box). Count transparent Box deref layers and preserve remaining real
    // deref projections as `Deref(...)` wrappers. (#2318)
    {
        let deref_count = place
            .projection
            .iter()
            .filter(|p| matches!(p, ProjectionElem::Deref))
            .count();
        if deref_count >= 2 {
            let local_ty = body.local_decls[place.local].ty;
            let box_depth = box_nesting_depth(tcx, local_ty);
            // For Box<&mut T>, box_depth=1, deref_count=2: 1 real deref
            // For Box<Box<&mut T>>, box_depth=2, deref_count=3: 1 real deref
            let real_derefs = deref_count.saturating_sub(box_depth);
            if box_depth > 0 && real_derefs > 0 {
                let base = symbolic_locals.get(&place.local)?.clone();
                let mut result = base;
                for _ in 0..real_derefs {
                    result = PureExpr::Deref(Arc::new(result));
                }
                return Some(result);
            }
        }
    }

    translate_place(place, &symbolic_locals)
}

/// Count the nesting depth of Box wrappers in a type.
///
/// `Box<T>` → 1, `Box<Box<T>>` → 2, `&mut T` → 0, `Box<&mut T>` → 1.
fn box_nesting_depth<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> usize {
    use rustc_middle::ty::TyKind;
    match ty.kind() {
        TyKind::Adt(adt_def, substs) if adt_def.is_box() => {
            if let Some(inner_ty) = substs.types().next() {
                1 + box_nesting_depth(tcx, inner_ty)
            } else {
                1
            }
        }
        _ => 0,
    }
}
