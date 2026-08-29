// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for AST-level matching logic in `eager_instantiation.rs`.
//!
//! These tests exercise the pure expression pattern matching functions used
//! by the eager existential instantiation subsystem. No AYEncoder is needed —
//! all tests operate on PureExpr ASTs and verify structural matching, variable
//! binding, normalization, and bound-variable detection.
//!
//! Coverage targets:
//! - `flatten_nested_existentials`: nested Exists flattening, triggered Exists stop
//! - `normalize_deref_final`: Deref/Final wrapper normalization into variable names
//! - `exprs_structurally_equal`: structural equality comparison
//! - `expr_mentions_bound_var`: bound variable detection with shadowing
//! - `try_match_expr`: pattern matching with bound variable binding
//! - `try_match_method_call`: postcondition_mut call matching
//! - `try_match_resolve_call`: resolve() call matching
//! - `collect_ground_postcondition_mut_calls`: ground call collection
//! - `collect_ground_resolve_calls`: ground resolve call collection
//!
//! Part of #1946 (eager_instantiation.rs unit tests).

use std::collections::HashMap;

use trust_wp_core::formula::ExprSort;

use super::*;
use crate::verify::{
    collect_ground_postcondition_mut_calls, collect_ground_resolve_calls, expr_mentions_bound_var,
    exprs_structurally_equal, flatten_nested_existentials, normalize_deref_final, try_match_expr,
    try_match_method_call, try_match_resolve_call, MethodCallPattern,
};

fn sorted_var(name: &str, sort: ExprSort) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(sort))
}

// ── flatten_nested_existentials ─────────────────────────────────────

/// Single Exists flattens to one bound variable + body.
#[test]
#[timeout(30000)]
fn flatten_single_exists() {
    // exists<x> x > 0
    let expr = exists("x", gt(var("x"), int(0)));
    let result = flatten_nested_existentials(&expr);
    assert!(result.is_some());
    let (vars, body) = result.unwrap();
    assert_eq!(vars, vec!["x".to_string()]);
    assert_eq!(*body, gt(var("x"), int(0)));
}

/// Nested Exists collects all bound variables in order.
#[test]
#[timeout(30000)]
fn flatten_nested_exists_collects_all_vars() {
    // exists<x> exists<y> exists<z> x + y > z
    let expr = exists(
        "x",
        exists("y", exists("z", gt(add(var("x"), var("y")), var("z")))),
    );
    let result = flatten_nested_existentials(&expr);
    assert!(result.is_some());
    let (vars, body) = result.unwrap();
    assert_eq!(
        vars,
        vec!["x".to_string(), "y".to_string(), "z".to_string()]
    );
    assert_eq!(*body, gt(add(var("x"), var("y")), var("z")));
}

/// Non-existential expression returns None.
#[test]
#[timeout(30000)]
fn flatten_non_existential_returns_none() {
    let expr = gt(var("x"), int(0));
    assert!(flatten_nested_existentials(&expr).is_none());
}

/// Forall (not Exists) returns None.
#[test]
#[timeout(30000)]
fn flatten_forall_returns_none() {
    let expr = forall("x", gt(var("x"), int(0)));
    assert!(flatten_nested_existentials(&expr).is_none());
}

/// Triggered Exists stops flattening — user-provided triggers mean E-matching
/// handles that level, so we shouldn't eagerly instantiate it.
#[test]
#[timeout(30000)]
fn flatten_triggered_exists_stops() {
    // exists<x> (triggered) body
    let expr = exists_with_triggers("x", gt(var("x"), int(0)), vec![vec![var("x")]]);
    assert!(flatten_nested_existentials(&expr).is_none());
}

/// Nested Exists where inner has triggers stops at the triggered level.
#[test]
#[timeout(30000)]
fn flatten_stops_at_triggered_inner_exists() {
    // exists<x> exists<y, triggers=[y]> body
    let inner = exists_with_triggers("y", gt(var("y"), int(0)), vec![vec![var("y")]]);
    let expr = exists("x", inner.clone());
    let result = flatten_nested_existentials(&expr);
    assert!(result.is_some());
    let (vars, body) = result.unwrap();
    // Only x is collected; y is skipped because it has triggers
    assert_eq!(vars, vec!["x".to_string()]);
    // Body is the triggered Exists (not flattened further)
    assert_eq!(*body, inner);
}

// ── normalize_deref_final ───────────────────────────────────────────

/// Deref(Var("x")) normalizes to Var("x") (by-value dereference identity).
#[test]
#[timeout(30000)]
fn normalize_deref_var_is_identity() {
    let expr = deref(var("x"));
    assert_eq!(normalize_deref_final(&expr), var("x"));
}

/// Final(Var("x")) normalizes to Var("x_final").
#[test]
#[timeout(30000)]
fn normalize_final_var_appends_suffix() {
    let expr = final_expr(var("x"));
    assert_eq!(normalize_deref_final(&expr), var("x_final"));
}

/// Nested Final(Final(Var("x"))) normalizes to Var("x_final_final").
#[test]
#[timeout(30000)]
fn normalize_nested_final_accumulates_suffixes() {
    let expr = final_expr(final_expr(var("x")));
    assert_eq!(normalize_deref_final(&expr), var("x_final_final"));
}

/// Mixed Deref+Final: Deref(Final(Var("x"))) = Final normalizes first,
/// then Deref is identity, giving Var("x_final").
#[test]
#[timeout(30000)]
fn normalize_deref_final_mixed() {
    let expr = deref(final_expr(var("x")));
    assert_eq!(normalize_deref_final(&expr), var("x_final"));
}

/// Final(Deref(Var("x"))) = Deref collapses to Var("x"), then Final adds _final.
#[test]
#[timeout(30000)]
fn normalize_final_deref_mixed() {
    let expr = final_expr(deref(var("x")));
    assert_eq!(normalize_deref_final(&expr), var("x_final"));
}

/// Normalization recurses into BinOp.
#[test]
#[timeout(30000)]
fn normalize_recurses_into_binop() {
    let expr = eq(deref(var("a")), final_expr(var("b")));
    let expected = eq(var("a"), var("b_final"));
    assert_eq!(normalize_deref_final(&expr), expected);
}

/// Normalization recurses into MethodCall receiver and args.
#[test]
#[timeout(30000)]
fn normalize_recurses_into_method_call() {
    let expr = method_call(
        deref(var("self")),
        "postcondition_mut",
        vec![final_expr(var("s"))],
    );
    let expected = method_call(var("self"), "postcondition_mut", vec![var("s_final")]);
    assert_eq!(normalize_deref_final(&expr), expected);
}

/// Normalization recurses into LogicFnCall args.
#[test]
#[timeout(30000)]
fn normalize_recurses_into_logic_fn_call() {
    let expr = logic_fn_call("resolve", vec![deref(var("f"))]);
    let expected = logic_fn_call("resolve", vec![var("f")]);
    assert_eq!(normalize_deref_final(&expr), expected);
}

/// Leaf expressions (Int, Bool, Var) pass through unchanged.
#[test]
#[timeout(30000)]
fn normalize_leaves_unchanged() {
    assert_eq!(normalize_deref_final(&int(42)), int(42));
    assert_eq!(normalize_deref_final(&bool_expr(true)), bool_expr(true));
    assert_eq!(normalize_deref_final(&var("x")), var("x"));
}

/// Final wrapping a non-Var expression keeps the Final wrapper.
#[test]
#[timeout(30000)]
fn normalize_final_non_var_keeps_wrapper() {
    // Final(x + 1) — inner normalizes to x+1 which is not a Var, so Final is kept
    let expr = final_expr(add(var("x"), int(1)));
    let normalized = normalize_deref_final(&expr);
    assert_eq!(normalized, final_expr(add(var("x"), int(1))));
}

// ── exprs_structurally_equal ────────────────────────────────────────

/// Identical expressions are structurally equal.
#[test]
#[timeout(30000)]
fn structural_equal_identical() {
    let a = gt(var("x"), int(0));
    let b = gt(var("x"), int(0));
    assert!(exprs_structurally_equal(&a, &b));
}

/// Different expressions are not structurally equal.
#[test]
#[timeout(30000)]
fn structural_equal_different() {
    let a = gt(var("x"), int(0));
    let b = gt(var("y"), int(0));
    assert!(!exprs_structurally_equal(&a, &b));
}

/// Different operator, same operands — not equal.
#[test]
#[timeout(30000)]
fn structural_equal_different_op() {
    let a = gt(var("x"), int(0));
    let b = lt(var("x"), int(0));
    assert!(!exprs_structurally_equal(&a, &b));
}

/// Nested vars ignore sort annotations inside compound expressions.
#[test]
#[timeout(30000)]
fn structural_equal_nested_var_ignores_sort_in_binop() {
    let with_sort = gt(add(sorted_var("x", ExprSort::Int), int(1)), int(0));
    let without_sort = gt(add(var("x"), int(1)), int(0));

    assert!(exprs_structurally_equal(&with_sort, &without_sort));
}

/// Logic function arguments recurse through nested vars when comparing structure.
#[test]
#[timeout(30000)]
fn structural_equal_nested_var_ignores_sort_in_logic_fn_args() {
    let with_sort = logic_fn_call("f", vec![sorted_var("x", ExprSort::Int)]);
    let without_sort = logic_fn_call("f", vec![var("x")]);

    assert!(exprs_structurally_equal(&with_sort, &without_sort));
}

// ── expr_mentions_bound_var ─────────────────────────────────────────

/// Simple variable mention detected.
#[test]
#[timeout(30000)]
fn mentions_bound_var_simple() {
    let expr = var("x");
    let bound = vec!["x".to_string()];
    assert!(expr_mentions_bound_var(&expr, &bound));
}

/// Non-bound variable not detected.
#[test]
#[timeout(30000)]
fn mentions_bound_var_not_bound() {
    let expr = var("y");
    let bound = vec!["x".to_string()];
    assert!(!expr_mentions_bound_var(&expr, &bound));
}

/// Bound variable in nested BinOp detected.
#[test]
#[timeout(30000)]
fn mentions_bound_var_in_binop() {
    let expr = gt(add(var("y"), int(1)), var("x"));
    let bound = vec!["x".to_string()];
    assert!(expr_mentions_bound_var(&expr, &bound));
}

/// Bound variable in MethodCall args detected.
#[test]
#[timeout(30000)]
fn mentions_bound_var_in_method_call() {
    let expr = method_call(var("self"), "postcondition_mut", vec![var("x")]);
    let bound = vec!["x".to_string()];
    assert!(expr_mentions_bound_var(&expr, &bound));
}

/// Quantifier-bound variable shadows outer bound variable.
#[test]
#[timeout(30000)]
fn mentions_bound_var_quantifier_shadows() {
    // forall<x> x > 0 — inner x refers to the quantifier's x, not the outer
    let expr = forall("x", gt(var("x"), int(0)));
    let bound = vec!["x".to_string()];
    assert!(!expr_mentions_bound_var(&expr, &bound));
}

/// Let-bound variable shadows outer bound variable.
#[test]
#[timeout(30000)]
fn mentions_bound_var_let_shadows() {
    // let x = 1 in x > 0 — inner x is let-bound, not the outer
    let expr = let_bind("x", int(1), gt(var("x"), int(0)));
    let bound = vec!["x".to_string()];
    // The value part (int(1)) doesn't mention bound vars, and the body's x is shadowed
    assert!(!expr_mentions_bound_var(&expr, &bound));
}

/// Bound variable in Let value (not shadowed) is detected.
#[test]
#[timeout(30000)]
fn mentions_bound_var_in_let_value() {
    // let y = x + 1 in y > 0
    let expr = let_bind("y", add(var("x"), int(1)), gt(var("y"), int(0)));
    let bound = vec!["x".to_string()];
    assert!(expr_mentions_bound_var(&expr, &bound));
}

/// Constants don't mention bound variables.
#[test]
#[timeout(30000)]
fn mentions_bound_var_constants() {
    let bound = vec!["x".to_string()];
    assert!(!expr_mentions_bound_var(&int(42), &bound));
    assert!(!expr_mentions_bound_var(&bool_expr(true), &bound));
}

/// Deref/Final/View/Old wrappers are traversed.
#[test]
#[timeout(30000)]
fn mentions_bound_var_through_wrappers() {
    let bound = vec!["x".to_string()];
    assert!(expr_mentions_bound_var(&deref(var("x")), &bound));
    assert!(expr_mentions_bound_var(&final_expr(var("x")), &bound));
    assert!(expr_mentions_bound_var(&view(var("x")), &bound));
    assert!(expr_mentions_bound_var(&old(var("x")), &bound));
}

// ── try_match_expr ──────────────────────────────────────────────────

/// Bound variable in body matches any ground expression, creating a binding.
#[test]
#[timeout(30000)]
fn try_match_bound_var_creates_binding() {
    let body = var("x");
    let ground = int(42);
    let bound = vec!["x".to_string()];
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = Vec::new();

    assert!(try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
    assert_eq!(new_bindings.len(), 1);
    assert_eq!(new_bindings[0].0, "x");
    assert_eq!(new_bindings[0].1, int(42));
}

/// Bound variable with existing consistent binding succeeds.
#[test]
#[timeout(30000)]
fn try_match_bound_var_existing_consistent() {
    let body = var("x");
    let ground = int(42);
    let bound = vec!["x".to_string()];
    let mut existing: HashMap<String, PureExpr> = HashMap::new();
    existing.insert("x".to_string(), int(42));
    let mut new_bindings = Vec::new();

    assert!(try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
    assert!(new_bindings.is_empty()); // No new binding needed
}

/// Bound variable with conflicting existing binding fails.
#[test]
#[timeout(30000)]
fn try_match_bound_var_existing_conflict() {
    let body = var("x");
    let ground = int(42);
    let bound = vec!["x".to_string()];
    let mut existing: HashMap<String, PureExpr> = HashMap::new();
    existing.insert("x".to_string(), int(99)); // Conflict
    let mut new_bindings = Vec::new();

    assert!(!try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
}

/// Bound variable with consistent in-round binding succeeds.
#[test]
#[timeout(30000)]
fn try_match_bound_var_inround_consistent() {
    let body = var("x");
    let ground = int(42);
    let bound = vec!["x".to_string()];
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = vec![("x".to_string(), int(42))];

    assert!(try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
}

/// Bound variable with conflicting in-round binding fails.
#[test]
#[timeout(30000)]
fn try_match_bound_var_inround_conflict() {
    let body = var("x");
    let ground = int(42);
    let bound = vec!["x".to_string()];
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = vec![("x".to_string(), int(99))];

    assert!(!try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
}

/// Free variable matches same-named ground variable.
#[test]
#[timeout(30000)]
fn try_match_free_var_same_name() {
    let body = var("y");
    let ground = var("y");
    let bound = vec!["x".to_string()]; // y is not bound
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = Vec::new();

    assert!(try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
}

/// Free variable doesn't match different-named ground variable.
#[test]
#[timeout(30000)]
fn try_match_free_var_different_name() {
    let body = var("y");
    let ground = var("z");
    let bound = vec!["x".to_string()]; // y is not bound
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = Vec::new();

    assert!(!try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
}

/// LogicFnCall matches recursively on name and args.
#[test]
#[timeout(30000)]
fn try_match_logic_fn_call_recursive() {
    // body: f(x, y) where x is bound
    let body = logic_fn_call("f", vec![var("x"), var("y")]);
    // ground: f(42, y)
    let ground = logic_fn_call("f", vec![int(42), var("y")]);
    let bound = vec!["x".to_string()];
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = Vec::new();

    assert!(try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
    assert_eq!(new_bindings.len(), 1);
    assert_eq!(new_bindings[0].0, "x");
    assert_eq!(new_bindings[0].1, int(42));
}

/// LogicFnCall with different names doesn't match.
#[test]
#[timeout(30000)]
fn try_match_logic_fn_call_different_name() {
    let body = logic_fn_call("f", vec![var("x")]);
    let ground = logic_fn_call("g", vec![int(42)]);
    let bound = vec!["x".to_string()];
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = Vec::new();

    assert!(!try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
}

/// LogicFnCall with different arg count doesn't match.
#[test]
#[timeout(30000)]
fn try_match_logic_fn_call_different_arity() {
    let body = logic_fn_call("f", vec![var("x")]);
    let ground = logic_fn_call("f", vec![int(42), int(43)]);
    let bound = vec!["x".to_string()];
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = Vec::new();

    assert!(!try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
}

/// MethodCall matches recursively on receiver, method name, and args.
#[test]
#[timeout(30000)]
fn try_match_method_call_recursive() {
    // body: x.foo(y) where x,y are bound
    let body = method_call(var("x"), "foo", vec![var("y")]);
    // ground: a.foo(b)
    let ground = method_call(var("a"), "foo", vec![var("b")]);
    let bound = vec!["x".to_string(), "y".to_string()];
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = Vec::new();

    assert!(try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
    assert_eq!(new_bindings.len(), 2);
    // Check bindings (order may vary based on matching sequence)
    let x_binding = new_bindings.iter().find(|(n, _)| n == "x").unwrap();
    let y_binding = new_bindings.iter().find(|(n, _)| n == "y").unwrap();
    assert_eq!(x_binding.1, var("a"));
    assert_eq!(y_binding.1, var("b"));
}

/// MethodCall with different method name doesn't match.
#[test]
#[timeout(30000)]
fn try_match_method_call_different_method() {
    let body = method_call(var("x"), "foo", vec![]);
    let ground = method_call(var("a"), "bar", vec![]);
    let bound = vec!["x".to_string()];
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = Vec::new();

    assert!(!try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
}

/// Non-matching expression types fall back to structural equality.
#[test]
#[timeout(30000)]
fn try_match_fallback_structural_equal() {
    let body = int(42);
    let ground = int(42);
    let bound: Vec<String> = Vec::new();
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = Vec::new();

    assert!(try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
}

/// Non-matching expression types with different values fail.
#[test]
#[timeout(30000)]
fn try_match_fallback_structural_not_equal() {
    let body = int(42);
    let ground = int(99);
    let bound: Vec<String> = Vec::new();
    let existing: HashMap<String, PureExpr> = HashMap::new();
    let mut new_bindings = Vec::new();

    assert!(!try_match_expr(
        &body,
        &ground,
        &bound,
        &existing,
        &mut new_bindings
    ));
}

// ── try_match_method_call (MethodCallPattern level) ─────────────────

/// Matching postcondition_mut calls with bound variable binding.
#[test]
#[timeout(30000)]
fn match_method_call_pattern_binds_vars() {
    // body: st.postcondition_mut(x) where st,x are bound
    let body_recv = var("st");
    let body_args = vec![var("x")];
    let body_call = MethodCallPattern {
        receiver: &body_recv,
        args: &body_args,
    };

    // ground: f.postcondition_mut(42)
    let ground_recv = var("f");
    let ground_args = vec![int(42)];
    let ground_call = MethodCallPattern {
        receiver: &ground_recv,
        args: &ground_args,
    };

    let bound = vec!["st".to_string(), "x".to_string()];
    let existing: HashMap<String, PureExpr> = HashMap::new();

    let result = try_match_method_call(&body_call, &ground_call, &bound, &existing);
    assert!(result.is_some());
    let bindings = result.unwrap();
    assert_eq!(bindings.len(), 2);
    let st_binding = bindings.iter().find(|(n, _)| n == "st").unwrap();
    let x_binding = bindings.iter().find(|(n, _)| n == "x").unwrap();
    assert_eq!(st_binding.1, var("f"));
    assert_eq!(x_binding.1, int(42));
}

/// Method call with different arg counts doesn't match.
#[test]
#[timeout(30000)]
fn match_method_call_pattern_arity_mismatch() {
    let body_recv = var("st");
    let body_args = vec![var("x"), var("y")];
    let body_call = MethodCallPattern {
        receiver: &body_recv,
        args: &body_args,
    };

    let ground_recv = var("f");
    let ground_args = vec![int(42)];
    let ground_call = MethodCallPattern {
        receiver: &ground_recv,
        args: &ground_args,
    };

    let bound = vec!["st".to_string(), "x".to_string(), "y".to_string()];
    let existing: HashMap<String, PureExpr> = HashMap::new();

    assert!(try_match_method_call(&body_call, &ground_call, &bound, &existing).is_none());
}

/// Method call matching with pre-existing consistent binding.
#[test]
#[timeout(30000)]
fn match_method_call_pattern_with_existing_binding() {
    let body_recv = var("st");
    let body_args = vec![var("x")];
    let body_call = MethodCallPattern {
        receiver: &body_recv,
        args: &body_args,
    };

    let ground_recv = var("f");
    let ground_args = vec![int(42)];
    let ground_call = MethodCallPattern {
        receiver: &ground_recv,
        args: &ground_args,
    };

    let bound = vec!["st".to_string(), "x".to_string()];
    let mut existing: HashMap<String, PureExpr> = HashMap::new();
    existing.insert("st".to_string(), var("f")); // Pre-bound, consistent

    let result = try_match_method_call(&body_call, &ground_call, &bound, &existing);
    assert!(result.is_some());
    let bindings = result.unwrap();
    // Only x is newly bound; st was already bound
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].0, "x");
    assert_eq!(bindings[0].1, int(42));
}

/// Method call matching with conflicting pre-existing binding fails.
#[test]
#[timeout(30000)]
fn match_method_call_pattern_conflicting_binding() {
    let body_recv = var("st");
    let body_args = vec![var("x")];
    let body_call = MethodCallPattern {
        receiver: &body_recv,
        args: &body_args,
    };

    let ground_recv = var("f");
    let ground_args = vec![int(42)];
    let ground_call = MethodCallPattern {
        receiver: &ground_recv,
        args: &ground_args,
    };

    let bound = vec!["st".to_string(), "x".to_string()];
    let mut existing: HashMap<String, PureExpr> = HashMap::new();
    existing.insert("st".to_string(), var("g")); // Conflict: bound to g, not f

    assert!(try_match_method_call(&body_call, &ground_call, &bound, &existing).is_none());
}

// ── try_match_resolve_call ──────────────────────────────────────────

/// Resolve call matching binds a bound variable.
#[test]
#[timeout(30000)]
fn match_resolve_call_binds_var() {
    // body: resolve(x) where x is bound
    let body_arg = var("x");
    // ground: resolve(f_final)
    let ground_arg = var("f_final");
    let bound = vec!["x".to_string()];
    let existing: HashMap<String, PureExpr> = HashMap::new();

    let result = try_match_resolve_call(&body_arg, &ground_arg, &bound, &existing);
    assert!(result.is_some());
    let bindings = result.unwrap();
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].0, "x");
    assert_eq!(bindings[0].1, var("f_final"));
}

/// Resolve call with non-matching free variable fails.
#[test]
#[timeout(30000)]
fn match_resolve_call_free_var_mismatch() {
    let body_arg = var("y"); // not bound
    let ground_arg = var("f");
    let bound = vec!["x".to_string()]; // y is free
    let existing: HashMap<String, PureExpr> = HashMap::new();

    assert!(try_match_resolve_call(&body_arg, &ground_arg, &bound, &existing).is_none());
}

/// Resolve call with matching free variable succeeds.
#[test]
#[timeout(30000)]
fn match_resolve_call_free_var_match() {
    let body_arg = var("f"); // not bound, must match by name
    let ground_arg = var("f");
    let bound = vec!["x".to_string()]; // f is free
    let existing: HashMap<String, PureExpr> = HashMap::new();

    let result = try_match_resolve_call(&body_arg, &ground_arg, &bound, &existing);
    assert!(result.is_some());
    let bindings = result.unwrap();
    assert!(bindings.is_empty()); // No new binding — free var matched by name
}

// ── collect_ground_postcondition_mut_calls ───────────────────────────

/// Collects postcondition_mut calls from flat preconditions.
#[test]
#[timeout(30000)]
fn collect_ground_postcondition_mut_flat() {
    // requires: f.postcondition_mut(s1, s2)
    let reqs = [method_call(
        var("f"),
        "postcondition_mut",
        vec![var("s1"), var("s2")],
    )];
    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert_eq!(calls.len(), 1);
    assert_eq!(*calls[0].receiver, var("f"));
    assert_eq!(calls[0].args.len(), 2);
}

/// Quantifier-bound calls are excluded from ground collection.
#[test]
#[timeout(30000)]
fn collect_ground_postcondition_mut_excludes_quantified() {
    // requires: forall<x> x.postcondition_mut(s)
    let reqs = [forall(
        "x",
        method_call(var("x"), "postcondition_mut", vec![var("s")]),
    )];
    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert!(calls.is_empty());
}

/// Multiple preconditions: only ground calls collected.
#[test]
#[timeout(30000)]
fn collect_ground_postcondition_mut_mixed() {
    let reqs = [
        method_call(var("f"), "postcondition_mut", vec![var("s1")]),
        forall(
            "x",
            method_call(var("x"), "postcondition_mut", vec![var("s")]),
        ),
    ];
    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert_eq!(calls.len(), 1);
}

/// Non-postcondition_mut methods are not collected.
#[test]
#[timeout(30000)]
fn collect_ground_postcondition_mut_ignores_other_methods() {
    let reqs = [method_call(var("f"), "precondition", vec![var("s")])];
    let calls = collect_ground_postcondition_mut_calls(&reqs);
    assert!(calls.is_empty());
}

// ── collect_ground_resolve_calls ────────────────────────────────────

/// Collects resolve() calls from preconditions.
#[test]
#[timeout(30000)]
fn collect_ground_resolve_flat() {
    let reqs = [logic_fn_call("resolve", vec![var("f")])];
    let calls = collect_ground_resolve_calls(&reqs);
    assert_eq!(calls.len(), 1);
    assert_eq!(*calls[0], var("f"));
}

/// Quantifier-bound resolve args are excluded.
#[test]
#[timeout(30000)]
fn collect_ground_resolve_excludes_quantified() {
    let reqs = [forall("x", logic_fn_call("resolve", vec![var("x")]))];
    let calls = collect_ground_resolve_calls(&reqs);
    assert!(calls.is_empty());
}

/// Non-resolve logic function calls are not collected.
#[test]
#[timeout(30000)]
fn collect_ground_resolve_ignores_other_fns() {
    let reqs = [logic_fn_call("other_fn", vec![var("f")])];
    let calls = collect_ground_resolve_calls(&reqs);
    assert!(calls.is_empty());
}

/// Multi-arg resolve calls are not collected (resolve takes exactly 1 arg).
#[test]
#[timeout(30000)]
fn collect_ground_resolve_ignores_multi_arg() {
    let reqs = [logic_fn_call("resolve", vec![var("f"), var("g")])];
    let calls = collect_ground_resolve_calls(&reqs);
    assert!(calls.is_empty());
}
