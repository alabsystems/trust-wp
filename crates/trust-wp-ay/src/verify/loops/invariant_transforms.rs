// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared invariant transform utilities for loop verification phases.
//!
//! These transforms (trigger injection, FMap biconditional normalization) are
//! applied to loop invariants before encoding in all three loop phases:
//! initialization, preservation, and postcondition. Extracted from
//! `preservation.rs` per #2591.

use std::sync::Arc;

use tracing::debug;
use trust_wp_core::formula::{BinOp, PureExpr};

use crate::encoder::trigger::synthesize_triggers;

/// Inject synthesized triggers into triggerless `Forall` nodes. (#2116)
///
/// ay-dpll's single-round E-matching is unreliable when triggers are synthesized
/// at encoding time (inside the encoder's quantifier path). This function walks
/// a `PureExpr` tree and pre-synthesizes triggers at the AST level for any
/// `Forall { triggers: [], .. }` node, so that the encoder receives explicit
/// triggers and produces deterministic E-matching behavior.
///
/// Applied to loop invariants before encoding in all loop phases (preservation,
/// initialization, postcondition), ensuring consistent trigger patterns.
pub(super) fn inject_forall_triggers(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let new_triggers = if triggers.is_empty() {
                let synthesized = synthesize_triggers(std::slice::from_ref(&var), &body);
                if !synthesized.is_empty() {
                    debug!(
                        "[#2116] inject_forall_triggers: synthesized {} pattern(s) for ∀{var}",
                        synthesized.len(),
                    );
                }
                synthesized
            } else {
                triggers
            };
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers: new_triggers,
            }
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let new_triggers = if triggers.is_empty() {
                synthesize_triggers(std::slice::from_ref(&var), &body)
            } else {
                triggers
            };
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers: new_triggers,
            }
        }
        other => other,
    })
}

/// Retarget single-variable multi-triggers to synthesized singleton triggers.
///
/// Loop transition facts for logical FMap iterators currently use explicit
/// multi-triggers like `{contains(iter, k), lookup(iter, k)}`. In contains-only
/// preservation slices, the negated witness key observes `contains(..., k)` but
/// never materializes `lookup(..., k)`, so ay-dpll never instantiates the fact.
///
/// This rewrite is local to loop transition facts: keep the quantified body
/// unchanged, but replace explicit multi-triggers on single-variable quantifiers
/// with synthesized singleton triggers when available. Triggers affect solver
/// guidance, not semantics, so this preserves soundness while recovering the
/// missing witness instantiation path for #2116.
pub(super) fn relax_single_var_multitriggers(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } if triggers.iter().any(|pattern| pattern.len() > 1) => {
            let synthesized = synthesize_triggers(std::slice::from_ref(&var), &body);
            if synthesized.iter().all(|pattern| pattern.len() == 1) && !synthesized.is_empty() {
                debug!(
                    "[#2116] relax_single_var_multitriggers: retargeted {} pattern(s) for ∀{var}",
                    synthesized.len(),
                );

                PureExpr::Forall {
                    var,
                    var_sort,
                    body,
                    triggers: synthesized,
                }
            } else {
                PureExpr::Forall {
                    var,
                    var_sort,
                    body,
                    triggers,
                }
            }
        }
        other => other,
    })
}

// =============================================================================
// FMap get/Some biconditional normalization (#2116)
// =============================================================================

/// Normalize doubly-quantified FMap get/Some biconditionals to singly-quantified form.
///
/// Detects the pattern:
///   `∀k. ∀v. (get(A,k)==Some(v)) == (get(B,k)==Some(v) || get(C,k)==Some(v))`
///
/// Rewrites to the equivalent singly-quantified conjunction:
///   `∀k. contains(A,k) == (contains(B,k) || contains(C,k))`
///     `&& (contains(B,k) → lookup(A,k)==lookup(B,k))`
///     `&& (contains(C,k) → lookup(A,k)==lookup(C,k))`
///
/// The inner variable `v` has no trigger coverage for E-matching since it only
/// appears in equality chains (`lookup(X,k)==v`). Eliminating it produces a
/// singly-quantified formula where all variables appear in triggerable method
/// calls (`contains`, `lookup`).
///
/// Applied before [`inject_forall_triggers`] so the resulting single-variable
/// Forall node gets proper triggers synthesized.
pub(super) fn normalize_fmap_get_biconditional(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| {
        if let Some(rewritten) = try_normalize_fmap_biconditional(&node) {
            debug!("[#2116] normalize_fmap_get_biconditional: eliminated inner value quantifier");

            rewritten
        } else {
            node
        }
    })
}

/// Try to rewrite a nested `∀k.∀v. (get==Some) ↔ (get==Some || get==Some)`.
///
/// Returns `Some(rewritten)` if the node matches, `None` otherwise.
fn try_normalize_fmap_biconditional(node: &PureExpr) -> Option<PureExpr> {
    let PureExpr::Forall {
        var: k_var,
        var_sort: k_sort,
        body: inner,
        triggers: outer_triggers,
    } = node
    else {
        return None;
    };
    if !outer_triggers.is_empty() {
        return None;
    }
    let PureExpr::Forall {
        var: v_var,
        body: bicond_body,
        triggers: inner_triggers,
        ..
    } = inner.as_ref()
    else {
        return None;
    };
    if !inner_triggers.is_empty() {
        return None;
    }

    // Match: BinOp(lhs, Eq, rhs) — the biconditional.
    let PureExpr::BinOp(bicond_lhs, BinOp::Eq, bicond_rhs) = bicond_body.as_ref() else {
        return None;
    };

    // Try both orientations: single==disjunction or disjunction==single.
    try_build_normalized(k_var, k_sort.as_ref(), v_var, bicond_lhs, bicond_rhs)
        .or_else(|| try_build_normalized(k_var, k_sort.as_ref(), v_var, bicond_rhs, bicond_lhs))
}

/// Build the normalized formula given the single side and disjunction side.
///
/// `single_side` should be `get(A,k)==Some(v)`.
/// `disj_side` should be `get(B,k)==Some(v) || get(C,k)==Some(v)`.
fn try_build_normalized(
    k_var: &str,
    k_sort: Option<&trust_wp_core::formula::ExprSort>,
    v_var: &str,
    single_side: &PureExpr,
    disj_side: &PureExpr,
) -> Option<PureExpr> {
    // Single side: get(A, Var(k)) == Some(Var(v))
    let (a_recv, a_key, a_val) = extract_get_eq_some(single_side)?;
    if !is_var_named(a_key, k_var) || !is_var_named(a_val, v_var) {
        return None;
    }

    // Disjunction side: get(B,k)==Some(v) || get(C,k)==Some(v)
    let PureExpr::BinOp(disj_left, BinOp::Or, disj_right) = disj_side else {
        return None;
    };
    let (b_recv, b_key, b_val) = extract_get_eq_some(disj_left)?;
    if !is_var_named(b_key, k_var) || !is_var_named(b_val, v_var) {
        return None;
    }
    let (c_recv, c_key, c_val) = extract_get_eq_some(disj_right)?;
    if !is_var_named(c_key, k_var) || !is_var_named(c_val, v_var) {
        return None;
    }

    let k = PureExpr::Var(k_var.to_string(), None);

    // contains(A,k) == (contains(B,k) || contains(C,k))
    let contains_partition = PureExpr::BinOp(
        Arc::new(method_call_1(a_recv, "contains", &k)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(method_call_1(b_recv, "contains", &k)),
            BinOp::Or,
            Arc::new(method_call_1(c_recv, "contains", &k)),
        )),
    );

    // contains(B,k) → lookup(A,k)==lookup(B,k)
    let value_agreement_b = PureExpr::BinOp(
        Arc::new(method_call_1(b_recv, "contains", &k)),
        BinOp::Implies,
        Arc::new(PureExpr::BinOp(
            Arc::new(method_call_1(a_recv, "lookup", &k)),
            BinOp::Eq,
            Arc::new(method_call_1(b_recv, "lookup", &k)),
        )),
    );

    // contains(C,k) → lookup(A,k)==lookup(C,k)
    let value_agreement_c = PureExpr::BinOp(
        Arc::new(method_call_1(c_recv, "contains", &k)),
        BinOp::Implies,
        Arc::new(PureExpr::BinOp(
            Arc::new(method_call_1(a_recv, "lookup", &k)),
            BinOp::Eq,
            Arc::new(method_call_1(c_recv, "lookup", &k)),
        )),
    );

    let body = PureExpr::BinOp(
        Arc::new(contains_partition),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(value_agreement_b),
            BinOp::And,
            Arc::new(value_agreement_c),
        )),
    );

    Some(PureExpr::Forall {
        var: k_var.to_string(),
        var_sort: k_sort.cloned(),
        body: Arc::new(body),
        triggers: vec![],
    })
}

/// Extract `(receiver, key, value)` from `get(receiver, key) == Some(value)`.
///
/// Handles both orientations: `get(...)==Some(...)` and `Some(...)==get(...)`.
fn extract_get_eq_some(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    extract_get_some_pair(lhs, rhs).or_else(|| extract_get_some_pair(rhs, lhs))
}

/// Match `get_side` as a `get` method call and `some_side` as a `Some` constructor.
fn extract_get_some_pair<'a>(
    get_side: &'a PureExpr,
    some_side: &'a PureExpr,
) -> Option<(&'a PureExpr, &'a PureExpr, &'a PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = get_side
    else {
        return None;
    };
    if !matches!(method.as_str(), "get" | "get_ghost" | "get_mut_ghost") || args.len() != 1 {
        return None;
    }
    let PureExpr::LogicFnCall {
        name,
        args: some_args,
    } = some_side
    else {
        return None;
    };
    if !name.ends_with("Some") || some_args.len() != 1 {
        return None;
    }
    Some((receiver.as_ref(), &args[0], &some_args[0]))
}

fn is_var_named(expr: &PureExpr, name: &str) -> bool {
    matches!(expr, PureExpr::Var(n, _) if n == name)
}

fn method_call_1(receiver: &PureExpr, method: &str, arg: &PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver.clone()),
        method: method.to_string(),
        args: vec![arg.clone()],
    }
}
