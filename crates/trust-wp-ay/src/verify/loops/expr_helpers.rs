// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression helper utilities for loop verification.
//!
//! Pure expression analysis functions with no encoder or solver dependencies:
//! variable reference checking, scalar view stripping, and chain projection detection.

use std::{collections::HashSet, sync::Arc};

#[cfg(test)]
use trust_wp_core::formula::PureExprDepthLimitedTraversalExt as _;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

/// Returns `true` if `expr` references any free variable whose name is in `var_set`.
///
/// Used to filter function-level requires in the postcondition VC: requires
/// that reference loop-modified variables would constrain the post-loop state
/// with pre-loop values, creating unsound proofs. (#1295, #904)
///
/// Delegates to `PureExpr::any_free_var` for exhaustive binder-aware traversal,
/// preventing silent gaps when new PureExpr variants are added. (#2577)
pub(in crate::verify::loops) fn expr_references_any_var(
    expr: &PureExpr,
    var_set: &HashSet<&str>,
) -> bool {
    expr.any_free_var(|name, _sort| var_set.contains(name))
}

/// Collect all free variable names referenced in an expression.
///
/// Walks the expression tree and collects every free `Var(name, _)`.
/// Bound names introduced by quantifiers, match patterns, let-bindings, and
/// closures are excluded, while trigger-only free variables are still counted.
///
/// Used to determine which init_extra_facts are relevant to a given invariant
/// slice — facts are included if they share any free variable with the slice. (#2116)
///
/// Delegates to `PureExpr::for_each_free_var` for exhaustive binder-aware
/// traversal. (#2577)
pub(in crate::verify::loops) fn collect_expr_var_names<'a>(
    expr: &'a PureExpr,
    names: &mut HashSet<&'a str>,
) {
    expr.for_each_free_var(|name, _sort| {
        names.insert(name);
    });
}

/// Strip `View(Var(name))` → `Var(name)` for scalar variables.
///
/// In Creusot syntax, `x@` produces `View(Var("x"))`. For scalar types (integers,
/// bools), the View is identity, but the encoder creates a separate `x_view`
/// SMT variable linked by equality (`x_view == x`). In QF_LIA postcondition
/// VCs, these extra variables can cause ay-dpll's bound-tightening loop to
/// diverge on trivially provable obligations. Stripping scalar Views before
/// encoding eliminates the intermediate variables entirely. (#1581)
///
/// Non-scalar Views (e.g., `View(MethodCall { ... })`) are preserved because
/// the View has a non-trivial meaning (e.g., Seq model).
pub(in crate::verify::loops) fn strip_scalar_views(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::View(inner)
            if matches!(
                inner.as_ref(),
                PureExpr::Var(_, _) | PureExpr::Deref(_) | PureExpr::Final(_)
            ) =>
        {
            inner.as_ref().clone()
        }
        other => other,
    })
}

/// Strip `Deref(receiver.ward())` to `receiver.ward()` for ghost permissions.
///
/// The driver lowers `Perm::ward` to the stable guarded target itself, not to a
/// separate reference term. Creusot specs commonly write `*perm.ward()`; keeping
/// the outer `Deref` creates a second, unlinked loop fact.
pub(in crate::verify::loops) fn strip_transparent_ghost_derefs(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Deref(inner)
            if matches!(
                inner.as_ref(),
                PureExpr::MethodCall { method, args, .. }
                    if method == "ward" && args.is_empty()
            ) =>
        {
            inner.as_ref().clone()
        }
        other => other,
    })
}

/// Collect base variable names that appear directly under `Final(Var(x))` in
/// an expression. These are mutable reference variables whose prophecy value
/// (`^x`, encoded as `x_final`) is referenced in the postcondition.
///
/// Used by Phase 4 (#759) borrow resolution: for mutable reference parameters
/// that are not modified in the loop, the postcondition check needs to assert
/// `x_final == x_current` so the prophecy resolves to the loop-exit deref value.
/// Without this, `x_final` is a free variable and the solver finds spurious
/// counterexamples.
pub(in crate::verify::loops) fn collect_final_var_names(exprs: &[PureExpr]) -> HashSet<String> {
    let mut names = HashSet::new();
    for expr in exprs {
        expr.for_each_recursive(|node| {
            if let PureExpr::Final(inner) = node {
                if let PureExpr::Var(name, _) = inner.as_ref() {
                    names.insert(name.clone());
                }
            }
        });
    }
    names
}

/// Strip `Deref(Var(name))` → `Var(name)` for snapshot-like immutable locals.
///
/// In Creusot, `snapshot!(x@)` captures a `Snapshot<T>` value, and `*snap`
/// dereferences it. For scalar types, this dereference is semantically identity:
/// the snapshot holds the captured value directly, so `*snap == snap`. However,
/// the encoder translates `Deref(Var("snap"))` to a derived variable name
/// (e.g., `snap_current`) that is not linked to `snap` by the current-chain
/// alias constraints (which only link `_current_current` to `_current`).
///
/// This causes loop invariants like `*total == x + result` to reference an
/// unlinked `total_current` variable, making initialization and preservation
/// checks time out or fail.
///
/// The fix: strip `Deref(Var(name))` to `Var(name)` when `name` is an
/// immutable snapshot local — a variable in `pre_loop_assignments` that is
/// NOT modified by the loop body. This is sound because:
/// - The variable is immutable across loop iterations (auto-frame invariant
///   already asserts `name == initial_value`)
/// - Dereference of an immutable Snapshot is identity
/// - The stripped form directly uses the variable linked by auto-frame
///
/// (#2665)
pub(in crate::verify::loops) fn strip_snapshot_derefs(
    expr: &PureExpr,
    snapshot_vars: &std::collections::HashSet<&str>,
) -> PureExpr {
    if snapshot_vars.is_empty() {
        return expr.clone();
    }
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Deref(inner)
            if matches!(
                inner.as_ref(),
                PureExpr::Var(name, _) if snapshot_vars.contains(name.as_str())
            ) =>
        {
            inner.as_ref().clone()
        }
        other => other,
    })
}

/// Canonicalize loop-emitted `fmap_new()` facts to the encoder's axiom-backed
/// FMap empty constructor.
pub(in crate::verify::loops) fn canonicalize_fmap_new(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::LogicFnCall { ref name, ref args } if name == "fmap_new" && args.is_empty() => {
            PureExpr::LogicFnCall {
                name: "fmap_empty".to_string(),
                args: vec![],
            }
        }
        other => other,
    })
}

/// Derive ground FMap length facts from loop-carried FMap equalities.
///
/// Loop iterator facts use `fmap_new()` for exhausted FMap-backed iterators.
/// In mixed loop VCs, FMap lengths may be encoded as arithmetic proxies, so the
/// solver cannot rely on UF congruence to derive `len(a) == len(b)` from
/// `a == b`. Assert those ground consequences directly in the loop VC.
pub(in crate::verify::loops) fn derive_fmap_len_facts(facts: &[PureExpr]) -> Vec<PureExpr> {
    let mut derived = Vec::new();
    for fact in facts {
        let Some((lhs, rhs)) = equality_to_exprs(fact) else {
            continue;
        };

        if is_fmap_empty_expr(lhs) && is_fmap_expr(rhs) {
            for receiver in fmap_len_receivers(rhs) {
                push_unique(
                    &mut derived,
                    fmap_len_equality(receiver, PureExpr::Int(0)),
                    facts,
                );
            }
        } else if is_fmap_empty_expr(rhs) && is_fmap_expr(lhs) {
            for receiver in fmap_len_receivers(lhs) {
                push_unique(
                    &mut derived,
                    fmap_len_equality(receiver, PureExpr::Int(0)),
                    facts,
                );
            }
        } else if is_fmap_expr(lhs) && is_fmap_expr(rhs) {
            for left_receiver in fmap_len_receivers(lhs) {
                for right_receiver in fmap_len_receivers(rhs) {
                    push_unique(
                        &mut derived,
                        fmap_len_equality(left_receiver.clone(), fmap_len(right_receiver)),
                        facts,
                    );
                }
            }
        }
    }
    derived
}

fn push_unique(out: &mut Vec<PureExpr>, fact: PureExpr, existing: &[PureExpr]) {
    if !existing.contains(&fact) && !out.contains(&fact) {
        out.push(fact);
    }
}

fn equality_to_exprs(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    Some((lhs.as_ref(), rhs.as_ref()))
}

fn fmap_len(receiver: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "len".to_string(),
        args: vec![],
    }
}

fn fmap_len_equality(receiver: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(fmap_len(receiver)), BinOp::Eq, Arc::new(rhs))
}

fn fmap_len_receivers(expr: &PureExpr) -> Vec<PureExpr> {
    let mut receivers = vec![expr.clone()];
    if matches!(expr, PureExpr::Var(_, Some(ExprSort::FMap))) {
        let viewed = PureExpr::View(Arc::new(expr.clone()));
        if !receivers.contains(&viewed) {
            receivers.push(viewed);
        }
    }
    receivers
}

fn is_fmap_empty_expr(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, args } if args.is_empty() => {
            matches!(name.as_str(), "fmap_new" | "fmap_empty" | "FMap::empty")
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "empty" && args.is_empty() => {
            matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "FMap")
        }
        PureExpr::View(inner) => is_fmap_empty_expr(inner),
        _ => false,
    }
}

fn is_fmap_expr(expr: &PureExpr) -> bool {
    if is_fmap_empty_expr(expr) {
        return true;
    }

    match expr {
        PureExpr::Var(_, Some(ExprSort::FMap)) => true,
        PureExpr::View(inner) | PureExpr::Final(inner) | PureExpr::Old(inner) => {
            is_fmap_expr(inner)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            matches!(method.as_str(), "insert" | "insert_ghost" | "merge")
                || (method == "empty"
                    && args.is_empty()
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "FMap"))
        }
        PureExpr::LogicFnCall { name, .. } => {
            matches!(name.as_str(), "fmap_insert" | "fmap_merge")
        }
        _ => false,
    }
}

#[cfg(test)]
mod strip_snapshot_derefs_tests {
    use std::{collections::HashSet, sync::Arc};

    use trust_wp_core::formula::BinOp;

    use super::*;

    #[test]
    fn test_strip_snapshot_deref_simple() {
        // `*total` → `total` when total is a snapshot var
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var("total".to_string(), None)));
        let snap_vars: HashSet<&str> = ["total"].into_iter().collect();
        let result = strip_snapshot_derefs(&expr, &snap_vars);
        assert_eq!(result, PureExpr::Var("total".to_string(), None));
    }

    #[test]
    fn test_strip_snapshot_deref_non_snapshot_preserved() {
        // `*x` stays as `*x` when x is NOT a snapshot var
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None)));
        let snap_vars: HashSet<&str> = ["total"].into_iter().collect();
        let result = strip_snapshot_derefs(&expr, &snap_vars);
        assert_eq!(
            result,
            PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None)))
        );
    }

    #[test]
    fn test_strip_snapshot_deref_in_binop() {
        // `*total == x + result` → `total == x + result`
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "total".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("result".to_string(), None)),
            )),
        );
        let snap_vars: HashSet<&str> = ["total"].into_iter().collect();
        let result = strip_snapshot_derefs(&expr, &snap_vars);
        let expected = PureExpr::BinOp(
            Arc::new(PureExpr::Var("total".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("result".to_string(), None)),
            )),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn test_strip_snapshot_deref_empty_set_noop() {
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var("total".to_string(), None)));
        let snap_vars: HashSet<&str> = HashSet::new();
        let result = strip_snapshot_derefs(&expr, &snap_vars);
        assert_eq!(
            result,
            PureExpr::Deref(Arc::new(PureExpr::Var("total".to_string(), None)))
        );
    }
}

#[cfg(test)]
mod strip_transparent_ghost_derefs_tests {
    use std::sync::Arc;

    use super::*;

    #[test]
    fn strips_deref_of_ward_call() {
        let ward = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("perm".into(), None)),
            method: "ward".to_string(),
            args: vec![],
        };
        let expr = PureExpr::Deref(Arc::new(ward.clone()));

        assert_eq!(strip_transparent_ghost_derefs(&expr), ward);
    }

    #[test]
    fn keeps_other_deref_calls() {
        let call = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("perm".into(), None)),
            method: "val".to_string(),
            args: vec![],
        };
        let expr = PureExpr::Deref(Arc::new(call.clone()));

        assert_eq!(
            strip_transparent_ghost_derefs(&expr),
            PureExpr::Deref(Arc::new(call))
        );
    }
}

/// Returns `true` if the expression contains deref/final/view/old chain nodes.
///
/// Current-chain alias constraints are only needed when loop VCs include these
/// projection forms. Arithmetic-only VCs can skip alias assertions to avoid
/// unnecessary solver overhead.
#[cfg(test)]
pub(in crate::verify::loops) fn expr_has_chain_projection(expr: &PureExpr) -> bool {
    expr.any_recursive_with_depth_limit(crate::encoder::MAX_ENCODING_DEPTH, true, |node| {
        matches!(
            node,
            PureExpr::Deref(_) | PureExpr::Final(_) | PureExpr::View(_) | PureExpr::Old(_)
        )
    })
}
