// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Axiom detection, existential witness extraction, and Skolemization.
//!
//! Contains embedded existential instantiation with body-derived witnesses
//! and trust-wp-level Skolemization for negated universal postconditions.

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, PureExpr};

/// Check if an expression is a universal quantifier (possibly nested).
pub(in crate::verify) fn is_universal_quantifier(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Forall { .. })
}

/// Check if logic_fns contains any Open-mode, non-opaque logic functions.
///
/// Open-mode logic functions have defining axioms that can make quantified
/// postconditions provable. Their presence signals that Skolemization at the
/// trust-wp level (for ground pool instantiation) is beneficial.
///
/// Skolemization of universal postconditions is unconditional and no longer
/// gates on this predicate (#2696); it still selects the plain ay-level `not`
/// branch for non-universal postconditions with open logic fns in
/// `encode_negated_postcondition`.
#[cfg_attr(not(test), allow(dead_code))]
pub(in crate::verify) fn has_open_logic_fns(
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    logic_fns.is_some_and(|fns| {
        fns.iter()
            .any(|f| !f.is_opaque() && f.mode() == trust_wp_core::logic::LogicMode::Open)
    })
}

/// Check if an expression contains an existential quantifier at any depth
/// (excluding top-level existentials, which are handled by
/// `negate_existential_postcondition`).
pub(in crate::verify) fn expr_contains_embedded_existential(expr: &PureExpr) -> bool {
    if matches!(expr, PureExpr::Exists { .. }) {
        return false;
    }
    if let PureExpr::Forall { body, .. } = expr {
        // Top-level forall wrapping an inner existential: the existential is
        // embedded within the forall body. Use contains_any_existential (not
        // expr_contains_embedded_existential) because inside a forall, any
        // existential is embedded — including a direct child exists. (#2575)
        return contains_any_existential(body);
    }
    expr.any_recursive(|node| matches!(node, PureExpr::Exists { .. }))
}

/// Check if an expression contains a universal quantifier at any depth
/// below the top level.
///
/// Used to route postconditions with embedded `forall` nodes onto the slow
/// path even when the outermost postcondition constructor is a conjunction,
/// implication, `ite`, or similar wrapper.
pub(in crate::verify) fn expr_contains_embedded_universal(expr: &PureExpr) -> bool {
    if matches!(expr, PureExpr::Forall { .. }) {
        return false;
    }
    expr.any_recursive(|node| matches!(node, PureExpr::Forall { .. }))
}

/// Check if an expression contains any existential quantifier at any depth.
fn contains_any_existential(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Exists { .. }))
}

/// Instantiate embedded existentials with body-derived witnesses.
///
/// When a postcondition contains `exists y. result == Ctor(y) && P(y)` and the
/// body provides a `Ctor(arg)` constructor call, substitute `y := arg` in the
/// existential body. This converts the existential to a ground formula that
/// ay-dpll can handle.
///
/// When no witness can be found (no body, or body doesn't provide a constructor
/// that matches the existential pattern), fall back to keeping the existential
/// as-is (ay may return Unknown, but no false Verified).
pub(in crate::verify) fn instantiate_embedded_existentials_with_body_witness(
    expr: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            // Try to find a witness from the body. Look for `result == Ctor(y)`
            // in the existential body and match it against the return_expr.
            if let Some(witness) = extract_existential_witness(&var, &body, return_expr) {
                let mut subs = std::collections::HashMap::new();
                subs.insert(var.clone(), witness);
                let instantiated = body.substitute(&subs);
                // Recurse on the instantiated body in case of nested existentials.
                instantiate_embedded_existentials_with_body_witness(&instantiated, return_expr)
            } else {
                PureExpr::Exists {
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

/// Try to extract a witness for an existentially-bound variable from the body result.
///
/// Looks for patterns like `result == Ctor(y)` in the existential body and
/// matches the constructor against the return_expr expression. When the body
/// is `Ctor(arg)` and the existential has `result == Ctor(y)`, the witness is `arg`.
///
/// Also handles ITE bodies: `ite(c, Ctor(a), ...)` produces `a` as the witness
/// when the existential matches `Ctor(y)`.
fn extract_existential_witness(
    var: &str,
    exists_body: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> Option<PureExpr> {
    let body_expr = return_expr?;

    // Find `result == Ctor(y)` or `Ctor(y) == result` in the existential body
    // where `y` is the bound variable.
    let ctor_name = find_constructor_matching_var(exists_body, var)?;

    // Find matching constructor arguments in the body
    extract_ctor_arg_from_body(body_expr, &ctor_name)
}

/// Find a constructor name in `X == Ctor(y)` patterns within the exists body,
/// where X is any non-constructor expression (e.g., `result`, `*self`, `self`).
///
/// Besides `result == Ctor(y)` this matches `Deref(Var("self")) == Ctor(y)`
/// and other variable-like left sides, which occur in postconditions like
/// `exists<e: E> *self == OwnResult::Err(e)`.
fn find_constructor_matching_var(expr: &PureExpr, var: &str) -> Option<String> {
    /// Check if an expression is a "known value" side of an equality
    /// (i.e., not the constructor side). Matches:
    /// - `Var("result", _)` — the standard return-value pattern
    /// - `Deref(Var(_))` — `*self` in postconditions
    /// - `Var(_, _)` — any named variable (e.g., `self`)
    fn is_known_value_expr(expr: &PureExpr) -> bool {
        match expr {
            PureExpr::Var(_, _) => true,
            PureExpr::Deref(inner) => matches!(inner.as_ref(), PureExpr::Var(_, _)),
            _ => false,
        }
    }

    fn known_equality_constructor_name(
        known_side: &PureExpr,
        ctor_side: &PureExpr,
        var: &str,
    ) -> Option<String> {
        if !is_known_value_expr(known_side) {
            return None;
        }
        let PureExpr::LogicFnCall { name, args } = ctor_side else {
            return None;
        };
        if args.len() == 1 && matches!(&args[0], PureExpr::Var(arg_name, _) if arg_name == var) {
            Some(name.clone())
        } else {
            None
        }
    }

    let mut ctor_name = None;
    expr.any_recursive(|node| {
        let PureExpr::BinOp(left, BinOp::Eq, right) = node else {
            return false;
        };
        ctor_name = known_equality_constructor_name(left, right, var)
            .or_else(|| known_equality_constructor_name(right, left, var));
        ctor_name.is_some()
    });
    ctor_name
}

/// Extract the argument of a constructor call from the body expression.
///
/// If body is `Ctor(arg)`, return `arg`.
/// If body is `ite(c, Ctor(arg), ...)`, return `arg`.
fn extract_ctor_arg_from_body(body: &PureExpr, ctor_name: &str) -> Option<PureExpr> {
    match body {
        PureExpr::LogicFnCall { name, args } if name == ctor_name && args.len() == 1 => {
            Some(args[0].clone())
        }
        PureExpr::Ite(_, then_branch, else_branch) => {
            // Try both branches
            extract_ctor_arg_from_body(then_branch, ctor_name)
                .or_else(|| extract_ctor_arg_from_body(else_branch, ctor_name))
        }
        _ => None,
    }
}

/// Skolemize a negated universal postcondition at the PureExpr level.
///
/// When the postcondition is `forall x. forall y. P(x, y)`, the negation is
/// `exists x. exists y. NOT P(x, y)`, which Skolemizes to `NOT P(sk_x, sk_y)`
/// where `sk_x` and `sk_y` are fresh constant names.
///
/// **Guard extraction (#2696):** When the body is an implication
/// `guard ==> consequent`, the Skolemized negation is decomposed into
/// `guard[sk] AND NOT consequent[sk]` instead of `NOT(guard[sk] ==> consequent[sk])`.
/// These are logically equivalent, but the decomposed form is far better for
/// the solver because:
/// 1. The guard provides concrete ground terms (e.g., `0 <= sk_i`, `sk_i < seq_len(v)`)
///    that E-matching can use to instantiate logic function axioms.
/// 2. The negated consequent directly targets the property to disprove.
/// Without this, `NOT(guard ==> P)` is an opaque negation that ay-dpll cannot
/// decompose at the theory level, leading to quantifier-unhandled results.
///
/// This is done at the PureExpr level (rather than relying on ay's internal
/// Skolemization) so that the resulting Skolem constants are visible to the
/// encoder's ground pool. This lets logic function defining axioms be
/// instantiated on the Skolem variables, which ay-dpll's single-round
/// E-matching cannot do when the Skolem variables are internal.
///
/// Returns `None` for non-universal postconditions.
pub(crate) fn skolemize_negated_universal(expr: &PureExpr) -> Option<PureExpr> {
    use std::collections::HashMap;

    use trust_wp_core::formula::UnOp;

    // Collect bound variables from nested Forall
    let mut vars: Vec<(String, Option<trust_wp_core::formula::ExprSort>)> = Vec::new();
    let mut current = expr;
    while let PureExpr::Forall {
        var,
        var_sort,
        body,
        ..
    } = current
    {
        vars.push((var.clone(), var_sort.clone()));
        current = body;
    }

    if vars.is_empty() {
        return None;
    }

    // Create Skolem constants: fresh variable names that will be declared
    // as uninterpreted constants by the encoder.
    let mut substitutions = HashMap::new();
    for (var_name, sort) in &vars {
        let skolem_name = format!("sk${var_name}");
        substitutions.insert(var_name.clone(), PureExpr::Var(skolem_name, sort.clone()));
    }

    // Guard extraction: when the body is `guard ==> consequent`, decompose
    // into `guard[sk] AND NOT consequent[sk]`. Handles nested implications
    // by peeling through chains like `g1 ==> (g2 ==> P)` to extract all
    // guards. (#2696)
    let (guards, innermost) = extract_implication_guards(current);
    if guards.is_empty() {
        // No implication structure: simple negation.
        let skolemized_body = current.substitute(&substitutions);
        Some(PureExpr::UnOp(UnOp::Not, Arc::new(skolemized_body)))
    } else {
        // Build: guard1[sk] AND guard2[sk] AND ... AND NOT consequent[sk]
        let negated_consequent =
            PureExpr::UnOp(UnOp::Not, Arc::new(innermost.substitute(&substitutions)));
        let mut result = negated_consequent;
        for guard in guards.into_iter().rev() {
            let skolemized_guard = guard.substitute(&substitutions);
            result = PureExpr::BinOp(Arc::new(skolemized_guard), BinOp::And, Arc::new(result));
        }
        Some(result)
    }
}

/// Extract implication guards from a chain of implications.
///
/// Given `g1 ==> (g2 ==> P)`, returns `([g1, g2], P)`.
/// Given `P` (non-implication), returns `([], P)`.
///
/// Used by `skolemize_negated_universal` to decompose implication bodies
/// for guard extraction. (#2696)
fn extract_implication_guards(expr: &PureExpr) -> (Vec<&PureExpr>, &PureExpr) {
    let mut guards = Vec::new();
    let mut current = expr;
    while let PureExpr::BinOp(guard, BinOp::Implies, consequent) = current {
        guards.push(guard.as_ref());
        current = consequent.as_ref();
    }
    (guards, current)
}
