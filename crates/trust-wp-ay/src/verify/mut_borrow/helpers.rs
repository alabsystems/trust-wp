// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Canonicalization and introspection helpers for mutable-borrow verification.
//!
//! Contains `canonicalize_mut_ref_vars` (bare Var→Deref rewriting) and
//! result-use classification helpers. These are pure `PureExpr` transformations
//! with no encoder or solver dependency.
//!
//! Extracted from `mut_borrow.rs` as part of #1865 mid-tier decomposition.

use std::{borrow::Cow, collections::HashSet, sync::Arc};

use trust_wp_core::formula::{
    BinOp, ExprSort, MatchArm, Pattern, PureExpr, PureExprDepthLimitedTraversalExt as _,
};

/// Canonicalize bare `Var(name)` to `Deref(Var(name))` when `name` is a mut-ref parameter.
///
/// MIR extraction collapses `*param` (Deref projection) to bare `Var(param)` in
/// return expressions. The SMT encoder maps `Var("x")` to `x` but
/// `Deref(Var("x"))` to `x_current`. Since both represent the initial value of
/// the mutable reference and postconditions use `old(*x)` -> `x_current`, the
/// return expression must also use `x_current` for the proof obligation to be
/// satisfiable. The driver can also preserve `MutRef` annotations on bare
/// variables inside arithmetic/comparison subexpressions of a mut-borrow
/// `return_expr`; those contexts still need the dereferenced current value
/// rather than the whole-borrow carrier. (#431, #598, #2593)
pub(crate) fn canonicalize_mut_ref_vars(expr: &PureExpr, param_names: &HashSet<&str>) -> PureExpr {
    canonicalize_inner(expr, param_names, 0, false)
}

#[allow(clippy::too_many_lines)]
fn canonicalize_inner(
    expr: &PureExpr,
    param_names: &HashSet<&str>,
    depth: usize,
    force_deref_annotated_mutrefs: bool,
) -> PureExpr {
    fn reuse_arc(original: &Arc<PureExpr>, rewritten: PureExpr) -> Arc<PureExpr> {
        if rewritten.ptr_eq_shallow(original.as_ref()) || &rewritten == original.as_ref() {
            Arc::clone(original)
        } else {
            Arc::new(rewritten)
        }
    }

    fn reuse_node(original: &PureExpr, rebuilt: PureExpr) -> PureExpr {
        if rebuilt.ptr_eq_shallow(original) || &rebuilt == original {
            original.clone()
        } else {
            rebuilt
        }
    }

    if depth > crate::encoder::MAX_ENCODING_DEPTH {
        return expr.clone();
    }
    let rec_with_force =
        |e: &PureExpr, force: bool| canonicalize_inner(e, param_names, depth + 1, force);
    match expr {
        PureExpr::Var(name, sort)
            if param_names.contains(name.as_str())
                && (!matches!(sort, Some(ExprSort::MutRef(_)))
                    || force_deref_annotated_mutrefs) =>
        {
            PureExpr::Deref(Arc::new(PureExpr::Var(name.clone(), sort.clone())))
        }
        PureExpr::BinOp(l, op, r) => {
            let force_deref_children = force_deref_annotated_mutrefs
                || matches!(
                    op,
                    BinOp::Add
                        | BinOp::Sub
                        | BinOp::Mul
                        | BinOp::Div
                        | BinOp::Mod
                        | BinOp::Shl
                        | BinOp::Shr
                        | BinOp::BitAnd
                        | BinOp::BitXor
                        | BinOp::BitOr
                        | BinOp::Lt
                        | BinOp::Le
                        | BinOp::Gt
                        | BinOp::Ge
                );
            let new_l = rec_with_force(l, force_deref_children);
            let new_r = rec_with_force(r, force_deref_children);
            reuse_node(
                expr,
                PureExpr::BinOp(reuse_arc(l, new_l), *op, reuse_arc(r, new_r)),
            )
        }
        PureExpr::UnOp(op, inner) => {
            let new_inner = rec_with_force(inner, force_deref_annotated_mutrefs);
            reuse_node(expr, PureExpr::UnOp(*op, reuse_arc(inner, new_inner)))
        }
        PureExpr::Ite(c, t, e) => {
            let new_c = rec_with_force(c, force_deref_annotated_mutrefs);
            let new_t = rec_with_force(t, force_deref_annotated_mutrefs);
            let new_e = rec_with_force(e, force_deref_annotated_mutrefs);
            reuse_node(
                expr,
                PureExpr::Ite(
                    reuse_arc(c, new_c),
                    reuse_arc(t, new_t),
                    reuse_arc(e, new_e),
                ),
            )
        }
        PureExpr::Old(inner) => {
            let new_inner = rec_with_force(inner, force_deref_annotated_mutrefs);
            reuse_node(expr, PureExpr::Old(reuse_arc(inner, new_inner)))
        }
        PureExpr::View(inner) => {
            let new_inner = rec_with_force(inner, force_deref_annotated_mutrefs);
            reuse_node(expr, PureExpr::View(reuse_arc(inner, new_inner)))
        }
        // Deref/Final already encode the inner Var correctly (x_current/x_final).
        // Recursing would double-wrap: Deref(Var("x")) -> Deref(Deref(Var("x"))).
        PureExpr::Deref(_) | PureExpr::Final(_) => expr.clone(),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_receiver = rec_with_force(receiver, force_deref_annotated_mutrefs);
            let new_args: Vec<PureExpr> = args
                .iter()
                .map(|arg| rec_with_force(arg, force_deref_annotated_mutrefs))
                .collect();
            reuse_node(
                expr,
                PureExpr::MethodCall {
                    receiver: reuse_arc(receiver, new_receiver),
                    method: method.clone(),
                    args: new_args,
                },
            )
        }
        PureExpr::LogicFnCall { name, args } => {
            let new_args: Vec<PureExpr> = args
                .iter()
                .map(|arg| rec_with_force(arg, force_deref_annotated_mutrefs))
                .collect();
            reuse_node(
                expr,
                PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: new_args,
                },
            )
        }
        PureExpr::Match { scrutinee, arms } => {
            let new_scrutinee = rec_with_force(scrutinee, force_deref_annotated_mutrefs);
            let new_arms: Vec<MatchArm> = arms
                .iter()
                .map(|arm| {
                    let arm_params = params_excluding_pattern(param_names, &arm.pattern);
                    MatchArm {
                        pattern: arm.pattern.clone(),
                        body: canonicalize_inner(
                            &arm.body,
                            &arm_params,
                            depth + 1,
                            force_deref_annotated_mutrefs,
                        ),
                    }
                })
                .collect();
            reuse_node(
                expr,
                PureExpr::Match {
                    scrutinee: reuse_arc(scrutinee, new_scrutinee),
                    arms: new_arms,
                },
            )
        }
        PureExpr::Let { var, value, body } => {
            let new_value = rec_with_force(value, force_deref_annotated_mutrefs);
            let body_params = params_excluding(param_names, var);
            let new_body =
                canonicalize_inner(body, &body_params, depth + 1, force_deref_annotated_mutrefs);
            reuse_node(
                expr,
                PureExpr::Let {
                    var: var.clone(),
                    value: reuse_arc(value, new_value),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let bp = params_excluding(param_names, var);
            let new_body = canonicalize_inner(body, &bp, depth + 1, force_deref_annotated_mutrefs);
            let new_triggers =
                canonicalize_triggers(triggers, &bp, depth + 1, force_deref_annotated_mutrefs);
            reuse_node(
                expr,
                PureExpr::Forall {
                    var: var.clone(),
                    var_sort: var_sort.clone(),
                    body: reuse_arc(body, new_body),
                    triggers: new_triggers,
                },
            )
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let bp = params_excluding(param_names, var);
            let new_body = canonicalize_inner(body, &bp, depth + 1, force_deref_annotated_mutrefs);
            let new_triggers =
                canonicalize_triggers(triggers, &bp, depth + 1, force_deref_annotated_mutrefs);
            reuse_node(
                expr,
                PureExpr::Exists {
                    var: var.clone(),
                    var_sort: var_sort.clone(),
                    body: reuse_arc(body, new_body),
                    triggers: new_triggers,
                },
            )
        }
        PureExpr::LetAssume { assumption, body } => {
            let new_assumption = rec_with_force(assumption, force_deref_annotated_mutrefs);
            let new_body = rec_with_force(body, force_deref_annotated_mutrefs);
            reuse_node(
                expr,
                PureExpr::LetAssume {
                    assumption: reuse_arc(assumption, new_assumption),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::LetObligation { obligation, body } => {
            let new_obligation = rec_with_force(obligation, force_deref_annotated_mutrefs);
            let new_body = rec_with_force(body, force_deref_annotated_mutrefs);
            reuse_node(
                expr,
                PureExpr::LetObligation {
                    obligation: reuse_arc(obligation, new_obligation),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::Closure { params, body } => {
            let mut bp = param_names.clone();
            for (name, _) in params {
                bp.remove(name.as_str());
            }
            let new_body = canonicalize_inner(body, &bp, depth + 1, force_deref_annotated_mutrefs);
            reuse_node(
                expr,
                PureExpr::Closure {
                    params: params.clone(),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {
            expr.clone()
        }
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => expr.clone(),
    }
}

/// Synthesize a result expression from postconditions when the driver does not
/// provide a `return_expr`. (#2673)
///
/// Handles postconditions of the form:
///   `if cond { X && result == a } else { Y && result == b }`
///
/// Returns `Some(Ite(cond, a, b))` when the postcondition contains a conditional
/// result equality pattern. Returns `None` if no such pattern is found.
///
/// This enables verification of patterns like `pair_bor_mut` where the driver
/// fails to extract the conditional field-projection return expression from MIR,
/// but the postcondition itself contains the necessary `result == <expr>` structure.
///
/// # Soundness
///
/// The synthesized expression is a consequence of the postcondition itself — it
/// adds no new information to the proof obligation. The postcondition already
/// asserts that `result == a` in the then-branch and `result == b` in the
/// else-branch. Making the result binding explicit simply allows the solver to
/// close the proof, since otherwise `result` is an unconstrained free variable.
pub(crate) fn synthesize_result_expr_from_postconditions(ensures: &[PureExpr]) -> Option<PureExpr> {
    for ens in ensures {
        if let Some(synthesized) = extract_result_from_ite(ens) {
            return Some(synthesized);
        }
    }
    None
}

/// Extract a result expression from an ITE postcondition.
///
/// Pattern: `Ite(cond, And(Eq(result, a), ...), And(Eq(result, b), ...))`
///       -> `Ite(cond, a, b)`
///
/// Also handles:
///   `Ite(cond, Eq(result, a), Eq(result, b))` (no conjunction)
///   `Ite(cond, And(..., Eq(result, a)), And(..., Eq(result, b)))` (eq on right)
fn extract_result_from_ite(expr: &PureExpr) -> Option<PureExpr> {
    let PureExpr::Ite(cond, then_branch, else_branch) = expr else {
        return None;
    };
    let then_rhs = extract_result_equality_rhs(then_branch)?;
    let else_rhs = extract_result_equality_rhs(else_branch)?;
    Some(PureExpr::Ite(
        Arc::clone(cond),
        Arc::new(then_rhs),
        Arc::new(else_rhs),
    ))
}

/// Extract the RHS of `result == <expr>` from a conjunction or bare equality.
///
/// Handles:
///   `Eq(Var("result"), expr)` -> `Some(expr)`
///   `Eq(expr, Var("result"))` -> `Some(expr)`
///   `And(Eq(Var("result"), expr), ...)` -> `Some(expr)`
///   `And(..., Eq(Var("result"), expr))` -> `Some(expr)`
///   `And(And(...), Eq(Var("result"), expr))` -> `Some(expr)` (nested)
fn extract_result_equality_rhs(expr: &PureExpr) -> Option<PureExpr> {
    // Direct equality: result == expr or expr == result
    if let Some(rhs) = match_result_equality(expr) {
        return Some(rhs);
    }
    // Conjunction: try both sides recursively
    if let PureExpr::BinOp(lhs, BinOp::And, rhs) = expr {
        if let Some(result_rhs) = extract_result_equality_rhs(lhs) {
            return Some(result_rhs);
        }
        if let Some(result_rhs) = extract_result_equality_rhs(rhs) {
            return Some(result_rhs);
        }
    }
    None
}

/// Match `result == expr` or `expr == result`, returning the non-result side.
fn match_result_equality(expr: &PureExpr) -> Option<PureExpr> {
    if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr {
        if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "result") {
            return Some(rhs.as_ref().clone());
        }
        if matches!(rhs.as_ref(), PureExpr::Var(name, _) if name == "result") {
            return Some(lhs.as_ref().clone());
        }
    }
    None
}

/// Return true when an expression mentions `*result` or `^result` (possibly nested).
pub(crate) fn expr_has_result_projection(expr: &PureExpr) -> bool {
    expr.any_recursive_with_depth_limit(crate::encoder::MAX_ENCODING_DEPTH, true, |node| {
        matches!(
            node,
            PureExpr::Deref(inner) | PureExpr::Final(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "result")
        )
    })
}

/// Return true when `result` is used as a whole value, not only through
/// `*result`/`^result` projections.
pub(crate) fn expr_has_non_projection_result_var(expr: &PureExpr) -> bool {
    has_non_projection_result_var(expr, false, 0)
}

fn has_non_projection_result_var(expr: &PureExpr, projected: bool, depth: usize) -> bool {
    if depth > crate::encoder::MAX_ENCODING_DEPTH {
        return false;
    }

    match expr {
        PureExpr::Var(name, _) => name == "result" && !projected,
        PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            let projects_result =
                matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "result");
            has_non_projection_result_var(inner, projected || projects_result, depth + 1)
        }
        PureExpr::Old(inner) | PureExpr::View(inner) => {
            has_non_projection_result_var(inner, projected, depth + 1)
        }
        PureExpr::BinOp(lhs, _, rhs) => {
            has_non_projection_result_var(lhs, projected, depth + 1)
                || has_non_projection_result_var(rhs, projected, depth + 1)
        }
        PureExpr::UnOp(_, inner) => has_non_projection_result_var(inner, projected, depth + 1),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            has_non_projection_result_var(cond, projected, depth + 1)
                || has_non_projection_result_var(then_expr, projected, depth + 1)
                || has_non_projection_result_var(else_expr, projected, depth + 1)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            has_non_projection_result_var(receiver, projected, depth + 1)
                || args
                    .iter()
                    .any(|arg| has_non_projection_result_var(arg, projected, depth + 1))
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter()
            .any(|arg| has_non_projection_result_var(arg, projected, depth + 1)),
        PureExpr::Match { scrutinee, arms } => {
            has_non_projection_result_var(scrutinee, projected, depth + 1)
                || arms.iter().any(|arm| {
                    !arm.pattern
                        .bound_names()
                        .iter()
                        .any(|name| *name == "result")
                        && has_non_projection_result_var(&arm.body, projected, depth + 1)
                })
        }
        PureExpr::Let { var, value, body } => {
            has_non_projection_result_var(value, projected, depth + 1)
                || (var != "result" && has_non_projection_result_var(body, projected, depth + 1))
        }
        PureExpr::Forall {
            var,
            body,
            triggers,
            ..
        }
        | PureExpr::Exists {
            var,
            body,
            triggers,
            ..
        } => {
            if var == "result" {
                return triggers
                    .iter()
                    .flatten()
                    .any(|trigger| has_non_projection_result_var(trigger, projected, depth + 1));
            }
            has_non_projection_result_var(body, projected, depth + 1)
                || triggers
                    .iter()
                    .flatten()
                    .any(|trigger| has_non_projection_result_var(trigger, projected, depth + 1))
        }
        PureExpr::LetAssume { assumption, body } => {
            has_non_projection_result_var(assumption, projected, depth + 1)
                || has_non_projection_result_var(body, projected, depth + 1)
        }
        PureExpr::LetObligation { obligation, body } => {
            has_non_projection_result_var(obligation, projected, depth + 1)
                || has_non_projection_result_var(body, projected, depth + 1)
        }
        PureExpr::Closure { params, body } => {
            !params.iter().any(|(name, _)| name == "result")
                && has_non_projection_result_var(body, projected, depth + 1)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => false,
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

fn params_excluding<'a, 'b>(params: &'b HashSet<&'a str>, var: &str) -> Cow<'b, HashSet<&'a str>> {
    if params.contains(var) {
        let mut inner = params.clone();
        inner.remove(var);
        Cow::Owned(inner)
    } else {
        Cow::Borrowed(params)
    }
}

fn params_excluding_pattern<'a>(params: &HashSet<&'a str>, pattern: &Pattern) -> HashSet<&'a str> {
    let mut result = params.clone();
    for name in pattern.bound_names() {
        result.remove(name);
    }
    result
}

fn canonicalize_triggers(
    triggers: &[Vec<PureExpr>],
    params: &HashSet<&str>,
    depth: usize,
    force_deref_annotated_mutrefs: bool,
) -> Vec<Vec<PureExpr>> {
    triggers
        .iter()
        .map(|trig| {
            trig.iter()
                .map(|t| canonicalize_inner(t, params, depth, force_deref_annotated_mutrefs))
                .collect()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use ntest::timeout;
    use trust_wp_core::formula::PureExpr;

    use crate::tests::helpers::{deref, eq, final_expr, var};

    #[test]
    #[timeout(30000)]
    fn deref_result_detected() {
        assert!(super::expr_has_result_projection(&deref(var("result"))));
    }

    #[test]
    #[timeout(30000)]
    fn final_result_detected() {
        assert!(super::expr_has_result_projection(&final_expr(var(
            "result"
        ))));
    }

    #[test]
    #[timeout(30000)]
    fn deref_non_result_not_detected() {
        assert!(!super::expr_has_result_projection(&deref(var("x"))));
    }

    #[test]
    #[timeout(30000)]
    fn bare_result_var_not_detected() {
        assert!(!super::expr_has_result_projection(&var("result")));
    }

    #[test]
    #[timeout(30000)]
    fn bare_result_var_is_non_projection_use() {
        assert!(super::expr_has_non_projection_result_var(&var("result")));
    }

    #[test]
    #[timeout(30000)]
    fn deref_result_is_projection_only_use() {
        assert!(!super::expr_has_non_projection_result_var(&deref(var(
            "result"
        ))));
    }

    #[test]
    #[timeout(30000)]
    fn final_result_view_is_projection_only_use() {
        assert!(!super::expr_has_non_projection_result_var(&PureExpr::View(
            Arc::new(final_expr(var("result")))
        )));
    }

    #[test]
    #[timeout(30000)]
    fn nested_in_binop_detected() {
        assert!(super::expr_has_result_projection(&eq(
            deref(var("result")),
            PureExpr::Int(42)
        )));
    }

    #[test]
    #[timeout(30000)]
    fn nested_in_ite_then_branch() {
        let expr = PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(deref(var("result"))),
            Arc::new(PureExpr::Int(0)),
        );
        assert!(super::expr_has_result_projection(&expr));
    }

    #[test]
    #[timeout(30000)]
    fn nested_in_method_call_receiver() {
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(deref(var("result"))),
            method: "len".to_string(),
            args: vec![],
        };
        assert!(super::expr_has_result_projection(&expr));
    }

    #[test]
    #[timeout(30000)]
    fn nested_in_method_call_args() {
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(var("x")),
            method: "push".to_string(),
            args: vec![final_expr(var("result"))],
        };
        assert!(super::expr_has_result_projection(&expr));
    }

    #[test]
    #[timeout(30000)]
    fn nested_in_logic_fn_call() {
        let expr = PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![deref(var("result"))],
        };
        assert!(super::expr_has_result_projection(&expr));
    }

    #[test]
    #[timeout(30000)]
    fn no_result_anywhere() {
        assert!(!super::expr_has_result_projection(&eq(
            deref(var("x")),
            final_expr(var("y"))
        )));
    }
}
