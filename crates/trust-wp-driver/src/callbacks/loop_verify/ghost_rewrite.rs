// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost return type detection and ensures-clause rewriting.
//!
//! When a function returns `Ghost<T>`, postcondition clauses that reference
//! `*result` need rewriting to use the actual return expression extracted
//! from the loop body. This module handles detection and rewriting.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{TyCtxt, TyKind};
use trust_wp_core::{formula::PureExpr, logic::is_invariant_method_name};

pub(in crate::callbacks) fn function_returns_ghost(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    // Closures don't support fn_sig(); use args.as_closure().sig() instead.
    // Closure return types are determined from the closure substs, not fn_sig().
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        let ty = tcx.type_of(def_id).instantiate_identity().skip_norm_wip();
        if let TyKind::Closure(_, substs) = ty.kind() {
            let closure_sig = substs.as_closure().sig();
            let output = closure_sig.skip_binder().output();
            if let TyKind::Adt(adt, _) = output.kind() {
                let adt_def_id = adt.did();
                let crate_name = tcx.crate_name(adt_def_id.krate).to_string();
                let path = tcx.def_path_str(adt_def_id);
                return is_trust_wp_ghost_def_path(&crate_name, &path);
            }
        }
        return false;
    }

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let output = sig.skip_binder().output();
    if let TyKind::Adt(adt, _) = output.kind() {
        let adt_def_id = adt.did();
        let crate_name = tcx.crate_name(adt_def_id.krate).to_string();
        let path = tcx.def_path_str(adt_def_id);
        return is_trust_wp_ghost_def_path(&crate_name, &path);
    }
    false
}

pub(in crate::callbacks) fn is_trust_wp_ghost_def_path(crate_name: &str, def_path: &str) -> bool {
    // Aligned with ghost.rs::is_trust_wp_ghost_like_path.
    // The crate_name comes from tcx.crate_name() (the defining crate), while
    // def_path comes from tcx.def_path_str() (which may use re-export paths).
    // For example, trust_wp_std re-exports creusot_std::Ghost, so at runtime
    // crate="trust_wp_std" path="creusot_std::Ghost".
    matches!(
        (crate_name, def_path),
        (
            "trust_wp_std",
            "trust_wp_std::ghost::Ghost"
                | "trust_wp_std::Ghost"
                | "creusot_std::Ghost"
                | "ghost::Ghost"
        ) | ("trust-wp", "trust_wp::Ghost" | "Ghost")
            | (
                "creusot_std",
                "creusot_std::ghost::Ghost" | "creusot_std::Ghost" | "ghost::Ghost"
            )
            | (
                "creusot_contracts",
                "creusot_contracts::ghost::Ghost"
                    | "creusot_contracts::Ghost"
                    | "ghost::Ghost"
                    | "Ghost"
            )
    )
}

pub(in crate::callbacks) fn rewrite_loop_ensures_for_ghost_return(
    ensures: &[PureExpr],
    returns_ghost: bool,
    return_expr: Option<&PureExpr>,
) -> Vec<PureExpr> {
    if !returns_ghost {
        return ensures.to_vec();
    }
    let Some(return_expr) = return_expr else {
        return ensures.to_vec();
    };
    ensures
        .iter()
        .map(|ens| rewrite_ghost_result_deref(ens, return_expr))
        .collect()
}

pub(in crate::callbacks) fn filter_post_loop_borrow_resolution_vars(
    deref_body_effect: std::collections::HashMap<String, PureExpr>,
    post_loop_deref_writes: &std::collections::HashSet<String>,
) -> std::collections::HashMap<String, PureExpr> {
    if post_loop_deref_writes.is_empty() {
        return deref_body_effect;
    }
    deref_body_effect
        .into_iter()
        .filter(|(name, _)| !post_loop_deref_writes.contains(name))
        .collect()
}

pub(in crate::callbacks) fn filter_post_loop_stale_deref_assumptions(
    assumptions: Vec<PureExpr>,
    post_loop_deref_writes: &std::collections::HashSet<String>,
) -> Vec<PureExpr> {
    if post_loop_deref_writes.is_empty() {
        return assumptions;
    }

    assumptions
        .into_iter()
        .filter(|assumption| !mentions_post_loop_written_deref(assumption, post_loop_deref_writes))
        .collect()
}

pub(in crate::callbacks) fn filter_post_loop_current_invariant_clauses(
    clauses: &mut Vec<PureExpr>,
    post_loop_final_values: &std::collections::HashMap<String, PureExpr>,
) {
    if post_loop_final_values.is_empty() {
        return;
    }

    clauses.retain(|clause| {
        !matches!(
            clause,
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if args.is_empty()
                && is_invariant_method_name(method)
                && invariant_receiver_mentions_post_loop_current(
                    receiver,
                    post_loop_final_values,
                )
        )
    });
}

fn invariant_receiver_mentions_post_loop_current(
    expr: &PureExpr,
    post_loop_final_values: &std::collections::HashMap<String, PureExpr>,
) -> bool {
    match expr {
        PureExpr::Var(name, _) => name
            .strip_suffix("_current")
            .is_some_and(|base| post_loop_final_values.contains_key(base)),
        PureExpr::Deref(inner) => {
            matches!(
                inner.as_ref(),
                PureExpr::Var(name, _) if post_loop_final_values.contains_key(name)
            ) || invariant_receiver_mentions_post_loop_current(inner, post_loop_final_values)
        }
        PureExpr::View(inner) | PureExpr::Old(inner) => {
            invariant_receiver_mentions_post_loop_current(inner, post_loop_final_values)
        }
        _ => false,
    }
}

fn mentions_post_loop_written_deref(
    expr: &PureExpr,
    post_loop_deref_writes: &std::collections::HashSet<String>,
) -> bool {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
        PureExpr::Deref(inner) => {
            matches!(
                inner.as_ref(),
                PureExpr::Var(name, _) if post_loop_deref_writes.contains(name)
            ) || mentions_post_loop_written_deref(inner, post_loop_deref_writes)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => mentions_post_loop_written_deref(inner, post_loop_deref_writes),
        PureExpr::BinOp(lhs, _, rhs) => {
            mentions_post_loop_written_deref(lhs, post_loop_deref_writes)
                || mentions_post_loop_written_deref(rhs, post_loop_deref_writes)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            mentions_post_loop_written_deref(cond, post_loop_deref_writes)
                || mentions_post_loop_written_deref(then_expr, post_loop_deref_writes)
                || mentions_post_loop_written_deref(else_expr, post_loop_deref_writes)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            mentions_post_loop_written_deref(receiver, post_loop_deref_writes)
                || args
                    .iter()
                    .any(|arg| mentions_post_loop_written_deref(arg, post_loop_deref_writes))
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            mentions_post_loop_written_deref(body, post_loop_deref_writes)
                || triggers.iter().flatten().any(|trigger| {
                    mentions_post_loop_written_deref(trigger, post_loop_deref_writes)
                })
        }
        PureExpr::Match { scrutinee, arms } => {
            mentions_post_loop_written_deref(scrutinee, post_loop_deref_writes)
                || arms.iter().any(|arm| {
                    pattern_mentions_post_loop_written_deref(&arm.pattern, post_loop_deref_writes)
                        || mentions_post_loop_written_deref(&arm.body, post_loop_deref_writes)
                })
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter()
            .any(|arg| mentions_post_loop_written_deref(arg, post_loop_deref_writes)),
        PureExpr::Let { value, body, .. } => {
            mentions_post_loop_written_deref(value, post_loop_deref_writes)
                || mentions_post_loop_written_deref(body, post_loop_deref_writes)
        }
        PureExpr::LetAssume { assumption, body }
        | PureExpr::LetObligation {
            obligation: assumption,
            body,
        } => {
            mentions_post_loop_written_deref(assumption, post_loop_deref_writes)
                || mentions_post_loop_written_deref(body, post_loop_deref_writes)
        }
        PureExpr::Closure { body, .. } => {
            mentions_post_loop_written_deref(body, post_loop_deref_writes)
        }
        _ => false,
    }
}

fn pattern_mentions_post_loop_written_deref(
    pattern: &trust_wp_core::formula::Pattern,
    post_loop_deref_writes: &std::collections::HashSet<String>,
) -> bool {
    match pattern {
        trust_wp_core::formula::Pattern::Wildcard
        | trust_wp_core::formula::Pattern::Binding(_)
        | trust_wp_core::formula::Pattern::Constructor { inner: None, .. } => false,
        trust_wp_core::formula::Pattern::Literal(expr) => {
            mentions_post_loop_written_deref(expr, post_loop_deref_writes)
        }
        trust_wp_core::formula::Pattern::Constructor {
            inner: Some(inner), ..
        }
        | trust_wp_core::formula::Pattern::Alias { pattern: inner, .. } => {
            pattern_mentions_post_loop_written_deref(inner, post_loop_deref_writes)
        }
        trust_wp_core::formula::Pattern::Tuple(patterns) => patterns
            .iter()
            .any(|inner| pattern_mentions_post_loop_written_deref(inner, post_loop_deref_writes)),
        _ => false,
    }
}

fn rewrite_ghost_result_deref(expr: &PureExpr, return_expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Deref(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) if name == "result" => return_expr.clone(),
            _ => PureExpr::Deref(inner),
        },
        other => other,
    })
}
