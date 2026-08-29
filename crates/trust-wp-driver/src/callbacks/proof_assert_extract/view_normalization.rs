// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! View and scalar normalization for proof_assert extraction.
//!
//! Normalizes `LogicFnCall("view", ...)` to `View(...)`, collapses nested
//! idempotent views, and materializes scalar `Deref(Var(...))` patterns into
//! named current-value variables for cleaner SMT encoding.

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::formula::{resolve_sort_name, BinOp, ExprSort, PureExpr};

use super::substitutions::{infer_substitution_expr_sort, is_scalar_view_identity_sort};

pub(crate) fn transparent_adapter_inner(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    let short_name = name.rsplit("::").next().unwrap_or(name.as_str());
    if matches!(short_name, "Copied" | "Cloned") && args.len() == 1 {
        Some(&args[0])
    } else {
        None
    }
}

/// Preserve the witness for a transparent adapter when it wraps a
/// non-identity inner expression.
///
/// Copied/cloned adapters should collapse to the inner expression only for
/// scalar identity domains. For iterator/view-like collection terms we keep a
/// `View(...)` wrapper around the inner term so downstream bridges can relate
/// the adapter result back to the collection model.
#[allow(clippy::needless_pass_by_value)]
pub(crate) fn preserve_transparent_adapter_view_witness(expr: PureExpr) -> PureExpr {
    if let Some(inner) = transparent_adapter_inner(&expr) {
        let inner = inner.clone();
        if is_provably_view_identity_domain(&inner) {
            inner
        } else {
            PureExpr::View(Arc::new(inner))
        }
    } else {
        expr
    }
}

/// Normalize `LogicFnCall("view", [expr])` → `View(expr)` and
/// `LogicFnCall("final_value", [expr])` → `Final(expr)`.
///
/// When `proof_assert!` is nested inside `ghost!`, the ghost macro's
/// `preprocess_view_syntax` transforms `expr@` to `view(expr)` at the token
/// level before the proof_assert macro captures the expression text. The
/// contract parser then produces `LogicFnCall("view", ...)` instead of
/// `View(...)`. The SMT encoder only simplifies `View(Int(n))` to `n`
/// (identity for scalar types); `LogicFnCall("view", ...)` is encoded as an
/// uninterpreted function with no axiom connecting it to the View trait. (#2209)
#[allow(clippy::needless_pass_by_value)] // PureExpr by-value is idiomatic for rewrite chains
pub(in crate::callbacks) fn normalize_view_fn_calls(expr: PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::LogicFnCall { name, args } if args.len() == 1 => {
            let inner = args
                .into_iter()
                .next()
                .expect("single-arg logic fn call guarded by len()");
            match name.as_str() {
                "view" => PureExpr::View(Arc::new(inner)),
                "final_value" => PureExpr::Final(Arc::new(inner)),
                _ => PureExpr::LogicFnCall {
                    name,
                    args: vec![inner],
                },
            }
        }
        other => other,
    })
}

/// Collapse nested logical views (`expr@@`) to a single view.
///
/// Proof-assert substitution and iterator-spec rewrites can synthesize
/// `View(View(e))` on collection model terms (for example `xs@@@`). Those
/// extra wrappers are semantically redundant and prevent the proof VC from
/// matching the call assumptions that already characterize the single-view
/// model term. (#2116)
///
/// Also collapses `View(expr)` when the inner expression is already in a
/// scalar view-identity domain, or is itself another `View(...)`. This handles
/// double-view from chained spec
/// application: `from_millis` produces `result@ == arg@ * 1_000_000` (Int),
/// then `Add` spec `result@ == self@ + rhs@` substitutes self with the
/// from_millis view expression, creating `View(Int-domain-expr)`. Since
/// View is identity on Int/Bool, the outer View is redundant and causes sort
/// mismatches when the solver sees `Duration == Int`. (#976)
#[allow(clippy::needless_pass_by_value)] // PureExpr by-value is idiomatic for rewrite chains
pub(in crate::callbacks) fn collapse_idempotent_views(expr: PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::View(inner) => {
            if let PureExpr::View(nested) = inner.as_ref() {
                // Collapse View(View(nested)) → View(nested)
                PureExpr::View(nested.clone())
            } else if is_provably_view_identity_domain(inner.as_ref()) {
                // Collapse View(identity-domain-expr) → identity-domain-expr
                // View is already a no-op here, so stripping is safe.
                inner.as_ref().clone()
            } else {
                PureExpr::View(inner)
            }
        }
        other => other,
    })
}

pub(in crate::callbacks) fn normalize_seq_final_fact_views(expr: PureExpr) -> PureExpr {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return expr;
    };

    let wrap_lhs =
        expr_is_bare_seq_final_carrier(lhs.as_ref()) && expr_is_seq_model_boundary(rhs.as_ref());
    let wrap_rhs =
        expr_is_bare_seq_final_carrier(rhs.as_ref()) && expr_is_seq_model_boundary(lhs.as_ref());

    let lhs = if wrap_lhs {
        PureExpr::View(lhs)
    } else {
        lhs.as_ref().clone()
    };
    let rhs = if wrap_rhs {
        PureExpr::View(rhs)
    } else {
        rhs.as_ref().clone()
    };

    PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
}

/// Check if applying `View` to `expr` is provably a no-op.
///
/// This covers scalar deep-model expressions (Int/Bool/Float/Unit) plus
/// nested view expressions that are already in model space. The check is
/// intentionally conservative: unknown expressions return false.
pub(crate) fn is_provably_view_identity_domain(expr: &PureExpr) -> bool {
    if transparent_adapter_inner(expr).is_some() {
        return false;
    }

    let text = format!("{expr:?}");
    if text.contains("Intersection")
        || text.contains("Difference")
        || text.contains("intersection")
        || text.contains("difference")
    {
        return false;
    }

    match expr {
        PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => true,
        PureExpr::View(_) => true,
        PureExpr::Ite(cond, then_br, else_br) => {
            is_provably_view_identity_domain(cond)
                && is_provably_view_identity_domain(then_br)
                && is_provably_view_identity_domain(else_br)
        }
        PureExpr::Match { arms, .. } => {
            !arms.is_empty()
                && arms
                    .iter()
                    .all(|arm| is_provably_view_identity_domain(&arm.body))
        }
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. }
        | PureExpr::Closure { body, .. } => is_provably_view_identity_domain(body),
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            is_provably_view_identity_domain(inner)
        }
        _ => infer_substitution_expr_sort(expr)
            .is_some_and(|sort| is_scalar_view_identity_sort(&sort)),
    }
}

fn scalar_current_base_name(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::Deref(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => Some(name.clone()),
            _ => None,
        },
        PureExpr::View(inner) | PureExpr::Final(inner) => scalar_current_base_name(inner),
        _ => None,
    }
}

fn expr_is_bare_seq_final_carrier(expr: &PureExpr) -> bool {
    let PureExpr::Final(inner) = expr else {
        return false;
    };
    infer_substitution_expr_sort(inner)
        .as_ref()
        .is_some_and(is_seq_collection_sort)
}

fn is_seq_collection_sort(sort: &ExprSort) -> bool {
    match sort {
        ExprSort::Seq => true,
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => is_seq_collection_sort(inner),
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            matches!(name.rsplit("::").next().unwrap_or(&name), "Seq" | "Vec")
        }
        _ => false,
    }
}

fn expr_is_seq_model_boundary(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::View(_))
        || infer_substitution_expr_sort(expr)
            .as_ref()
            .is_some_and(|sort| matches!(sort, ExprSort::Seq))
}

fn collect_scalar_current_sorts(expr: &PureExpr, current_sorts: &mut HashMap<String, ExprSort>) {
    expr.for_each_recursive(|node| {
        if let PureExpr::BinOp(left, BinOp::Eq, right) = node {
            if let Some(name) = scalar_current_base_name(left) {
                if let Some(rhs_sort) = infer_substitution_expr_sort(right) {
                    if is_scalar_view_identity_sort(&rhs_sort) {
                        current_sorts.insert(name, rhs_sort);
                    }
                }
            }
            if let Some(name) = scalar_current_base_name(right) {
                if let Some(lhs_sort) = infer_substitution_expr_sort(left) {
                    if is_scalar_view_identity_sort(&lhs_sort) {
                        current_sorts.insert(name, lhs_sort);
                    }
                }
            }
        }
    });
}

fn materialize_scalar_current_name(
    expr: &PureExpr,
    current_sorts: &HashMap<String, ExprSort>,
) -> Option<(String, ExprSort)> {
    match expr {
        PureExpr::Deref(inner) => {
            let PureExpr::Var(name, _) = inner.as_ref() else {
                return None;
            };
            current_sorts
                .get(name)
                .cloned()
                .map(|sort| (format!("{name}_current"), sort))
        }
        PureExpr::View(inner) => {
            if let PureExpr::Var(name, Some(sort)) = inner.as_ref() {
                if is_scalar_view_identity_sort(sort) {
                    return Some((name.clone(), sort.clone()));
                }
            }
            materialize_scalar_current_name(inner, current_sorts)
        }
        PureExpr::Final(inner) => materialize_scalar_current_name(inner, current_sorts)
            .map(|(name, sort)| (format!("{name}_final"), sort)),
        _ => None,
    }
}

#[allow(clippy::needless_pass_by_value)] // PureExpr by-value is idiomatic for rewrite chains
fn materialize_scalar_current_vars(
    expr: PureExpr,
    current_sorts: &HashMap<String, ExprSort>,
) -> PureExpr {
    expr.rewrite_bottom_up(|node| {
        if let Some((name, sort)) = materialize_scalar_current_name(&node, current_sorts) {
            PureExpr::Var(name, Some(sort))
        } else {
            node
        }
    })
}

pub(in crate::callbacks) fn normalize_scalar_proof_assert_boundary(
    preconditions: &mut [PureExpr],
    ensures: &mut [PureExpr],
    return_expr: &mut Option<PureExpr>,
) {
    let mut current_sorts = HashMap::new();
    for expr in preconditions
        .iter()
        .chain(ensures.iter())
        .chain(return_expr.iter())
    {
        collect_scalar_current_sorts(expr, &mut current_sorts);
    }
    if current_sorts.is_empty() {
        return;
    }

    for expr in preconditions.iter_mut() {
        *expr = materialize_scalar_current_vars(expr.clone(), &current_sorts);
    }
    for expr in ensures.iter_mut() {
        *expr = materialize_scalar_current_vars(expr.clone(), &current_sorts);
    }
    if let Some(expr) = return_expr.take() {
        *return_expr = Some(materialize_scalar_current_vars(expr, &current_sorts));
    }
}
