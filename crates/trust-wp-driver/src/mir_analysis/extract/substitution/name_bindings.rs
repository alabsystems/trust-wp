// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use rustc_middle::{
    mir::{Body, Local},
    ty::TyCtxt,
};
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::super::super::translate::ty_to_expr_sort_enriched;

pub(super) fn build_name_substitutions<'tcx>(
    body: &Body<'tcx>,
    arg_names: &[String],
    closure_capture_names: Option<&[String]>,
    local_exprs: &HashMap<Local, PureExpr>,
    deref_exprs: &HashMap<Local, PureExpr>,
    borrow_of: &HashMap<Local, Local>,
    name_updates: &HashMap<String, PureExpr>,
) -> HashMap<String, PureExpr> {
    let best_for_name = current_name_bindings(body, arg_names, local_exprs);
    let best_for_name_exprs: HashMap<String, PureExpr> = best_for_name
        .iter()
        .map(|(name, (_, expr))| (name.clone(), expr.clone()))
        .collect();

    // Resolve pre-state self-references embedded in a deref-write value.
    //
    // A deref-write value like `BinOp(Var("x"), Add, Int(1))` (from
    // `*b += 1` where `b = &mut x`) references the PRE-write value of the
    // borrow target symbolically. Substituting the entry-time bindings
    // (`x -> Int(12)`) makes it concrete (`12 + 1`), exactly as the
    // name_updates resolution below does for its self-references. (#1277)
    // Borrow targets never receive direct `local_exprs` updates while
    // borrowed, so their `best_for_name` binding IS the pre-write value.
    let resolve_deref_val =
        |deref_val: &PureExpr| -> PureExpr { deref_val.substitute(&best_for_name_exprs) };

    let mut substitutions = HashMap::new();
    for (name, (local, expr)) in &best_for_name {
        // Emit deref substitution for locals with deref writes (#746 AC1).
        // This must happen BEFORE the identity skip: argument `a` maps to
        // `Var("a")` (identity), but `*a = 1` still needs `"*a" → Int(1)`.
        let mut deref_written = false;
        if let Some(deref_val) = deref_exprs.get(local) {
            substitutions.insert(format!("*{name}"), resolve_deref_val(deref_val));
            deref_written = true;
        }

        if matches!(expr, PureExpr::Var(var, _) if var == name) {
            continue;
        }
        // A deref write reached this local (directly, or through a borrow
        // chain via the `borrow_of` propagation in
        // `handle_single_deref_write`). Its entry-time whole-VALUE binding
        // in `local_exprs` is now stale: emitting `name -> <entry value>`
        // would pin the pre-write value alongside the post-write facts
        // (`*name -> <new value>`, mut-borrow writebacks) and manufacture
        // an UNSAT premise set — a vacuous "proof" the vacuity guard then
        // rejects (resolve_drop: `x == 12` vs writeback `x == 13`).
        // The substitution map means "value at the cutoff", so rebind the
        // name to the POST-write value instead. (resolve_drop)
        if deref_written {
            if let Some(deref_val) = deref_exprs.get(local) {
                substitutions.insert(name.clone(), resolve_deref_val(deref_val));
            }
            continue;
        }
        substitutions.insert(name.clone(), expr.clone());
    }

    // Also check for deref writes through borrow chains: if local _N borrows
    // parameter _P (named "a"), and _N has a deref value, emit "*a".
    for (borrower, &origin) in borrow_of {
        if let Some(deref_val) = deref_exprs.get(borrower) {
            for (name, (local, _)) in &best_for_name {
                if *local == origin {
                    substitutions.insert(format!("*{name}"), resolve_deref_val(deref_val));
                }
            }
        }
    }

    // Apply direct source-name updates gathered from projected deref writes,
    // e.g., `*p.0 = 10` updates `b` in swap-borrow patterns.
    //
    // Name updates may contain self-references: `**b += 1` through a Box
    // alias (`local_exprs[b] = Var("x")`) produces `name_updates["x"] =
    // BinOp(Var("x"), Add, Int(1))`. The inner `Var("x")` is the pre-write
    // value, not a circular reference. Resolve it using `best_for_name` so
    // the substitution becomes concrete (e.g., `BinOp(Int(12), Add, Int(1))`)
    // instead of self-referential. (#1277)
    for (name, expr) in name_updates {
        let is_closure_capture_name = closure_capture_names
            .is_some_and(|capture_names| capture_names.iter().any(|capture| capture == name));
        // Deref-prefixed capture names (#2691): `*g2` should be included
        // when `g2` is a closure capture name. This handles ghost block
        // double-deref writes like `**g2 = 1` where the substitution
        // extraction produces `name_updates["*g2"] = Int(1)`.
        let is_deref_capture_name = name.starts_with('*')
            && closure_capture_names.is_some_and(|capture_names| {
                capture_names.iter().any(|capture| capture == &name[1..])
            });
        // Deref of a closure env field key (`*self.N`) flows through
        // synthesized capture mutation updates for `Box<&mut T>` ByValue
        // captures inside `move ||` closures: writes like `**bx2 = expr`
        // produce `name_updates["*self.N"] = expr`, and proof_assert
        // assumptions about `*self.N` need that substitution to fire. The
        // bare `self.N` form is intentionally excluded because its
        // `name_updates` value would be self-referential
        // (`self.N == self.N + 1`) without a pre-state binding to resolve
        // against. (#5 closures/09)
        let is_self_field_key = closure_capture_names.is_some()
            && name
                .strip_prefix("*self.")
                .is_some_and(|tail| !tail.is_empty() && tail.chars().all(|c| c.is_ascii_digit()));
        if best_for_name_exprs.contains_key(name)
            || is_closure_capture_name
            || is_deref_capture_name
            || is_self_field_key
        {
            let resolved = if let Some(pre_value) = best_for_name_exprs.get(name) {
                let mut self_ref_sub = HashMap::new();
                self_ref_sub.insert(name.clone(), pre_value.clone());
                expr.substitute(&self_ref_sub)
            } else {
                expr.clone()
            };
            substitutions.insert(name.clone(), resolved);
        }
    }

    substitutions
}

pub(super) fn build_name_substitution_sorts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    local_exprs: &HashMap<Local, PureExpr>,
) -> HashMap<String, Option<ExprSort>> {
    current_name_bindings(body, arg_names, local_exprs)
        .into_iter()
        .map(|(name, (local, _))| {
            (
                name,
                ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty),
            )
        })
        .collect()
}

/// Return the current source-name bindings at the cutoff point, including
/// identity mappings like `x -> Var("x", sort)`.
///
/// `build_name_substitutions()` intentionally omits those identity bindings
/// because they are redundant in the final assumption set. Branch-merge logic
/// still needs them so missing arms can fall back to the pre-branch symbolic
/// value instead of rebuilding an untyped `Var(name, None)`. (#994, #1965)
pub(super) fn current_name_exprs<'tcx>(
    body: &Body<'tcx>,
    arg_names: &[String],
    local_exprs: &HashMap<Local, PureExpr>,
) -> HashMap<String, PureExpr> {
    current_name_bindings(body, arg_names, local_exprs)
        .into_iter()
        .map(|(name, (_, expr))| (name, expr))
        .collect()
}

/// The current value of every non-reference source name whose binding is a
/// value of its own rather than the name itself: what a `snapshot!` taken
/// now freezes. A by-name read (`Var(name)`) in a capture result means the
/// name's CURRENT binding to every later reader (the internal-reference
/// resolution, the substitution facts), so a snapshot left holding it
/// follows every later write of the name (D-241,
/// snapshot_follows_later_write_unseen.rs). A reference keeps its identity:
/// a snapshot of one freezes the reference, which
/// `recover_snapshot_capture_current_pointee` handles.
pub(super) fn snapshot_frozen_name_values<'tcx>(
    body: &Body<'tcx>,
    arg_names: &[String],
    local_exprs: &HashMap<Local, PureExpr>,
) -> HashMap<String, PureExpr> {
    current_name_bindings(body, arg_names, local_exprs)
        .into_iter()
        .filter(|(name, (local, expr))| {
            !body.local_decls[*local].ty.is_any_ptr()
                && !matches!(expr, PureExpr::Var(var, _) if var == name)
        })
        .map(|(name, (_, expr))| (name, expr))
        .collect()
}

fn current_name_bindings<'tcx>(
    body: &Body<'tcx>,
    arg_names: &[String],
    local_exprs: &HashMap<Local, PureExpr>,
) -> HashMap<String, (Local, PureExpr)> {
    let mut best_for_name: HashMap<String, (Local, PureExpr)> = HashMap::new();
    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        if let Some(expr) = local_exprs.get(&local) {
            best_for_name.insert(name.clone(), (local, expr.clone()));
        }
    }
    for debug in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &debug.value {
            if place.projection.is_empty() {
                let Some(expr) = local_exprs.get(&place.local) else {
                    continue;
                };
                let name = debug.name.to_string();
                let dominated = best_for_name
                    .get(&name)
                    .is_none_or(|(prev, _)| place.local.as_u32() > prev.as_u32());
                if dominated {
                    best_for_name.insert(name, (place.local, expr.clone()));
                }
            }
        }
    }
    best_for_name
}
