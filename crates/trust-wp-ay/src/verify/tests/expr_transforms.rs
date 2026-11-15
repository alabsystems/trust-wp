// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use ntest::timeout;

use crate::{
    tests::helpers::{add, forall, gt, int, let_bind, logic_fn_call, match_expr, var},
    verify::{expr_mentions_bound_var, flatten_nested_existentials, substitute_vars_in_expr},
    BinOp, Pattern, PureExpr,
};

// --- flatten_nested_existentials trigger boundary (#1245) ---

/// `flatten_nested_existentials` returns None when the outermost exists
/// has user-provided triggers — E-matching handles the entire chain.
#[test]
#[timeout(30000)]
fn flatten_nested_existentials_stops_at_user_triggered_exists() {
    // exists<a> {:pattern f(a)} exists<b> g(b)
    // Outer has triggers → E-matching handles it → return None.
    let inner = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: None,
        body: Arc::new(logic_fn_call("g", vec![var("b")])),
        triggers: vec![],
    };
    let outer = PureExpr::Exists {
        var: "a".to_string(),
        var_sort: None,
        body: Arc::new(inner.clone()),
        triggers: vec![vec![logic_fn_call("f", vec![var("a")])]],
    };

    let result = flatten_nested_existentials(&outer);
    assert!(
        result.is_none(),
        "outermost triggered exists should return None — E-matching handles it"
    );
}

/// Triggerless nested existentials still fully flatten (regression guard).
#[test]
#[timeout(30000)]
fn flatten_nested_existentials_flattens_triggerless_chain() {
    // exists<a> exists<b> g(a, b)  — no triggers anywhere
    let body_expr = logic_fn_call("g", vec![var("a"), var("b")]);
    let inner = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: None,
        body: Arc::new(body_expr.clone()),
        triggers: vec![],
    };
    let outer = PureExpr::Exists {
        var: "a".to_string(),
        var_sort: None,
        body: Arc::new(inner),
        triggers: vec![],
    };

    let (vars, body) = flatten_nested_existentials(&outer).unwrap();
    assert_eq!(vars, vec!["a", "b"], "should flatten both triggerless vars");
    assert_eq!(*body, body_expr, "body should be innermost non-exists expr");
}

/// Triggerless outer with triggered inner: collect only outer variable,
/// leave triggered inner as body (#1245 main scenario).
#[test]
#[timeout(30000)]
fn flatten_nested_existentials_stops_at_triggered_inner() {
    // exists<a> exists<b> {:pattern g(b)} h(a, b)
    // Only collect "a" — inner "b" has triggers so E-matching handles it.
    let body_expr = logic_fn_call("h", vec![var("a"), var("b")]);
    let inner = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: None,
        body: Arc::new(body_expr),
        triggers: vec![vec![logic_fn_call("g", vec![var("b")])]],
    };
    let outer = PureExpr::Exists {
        var: "a".to_string(),
        var_sort: None,
        body: Arc::new(inner.clone()),
        triggers: vec![],
    };

    let result = flatten_nested_existentials(&outer);
    assert!(result.is_some(), "triggerless outer should return Some");
    let (vars, body) = result.unwrap();

    assert_eq!(vars, vec!["a"], "should collect only triggerless outer var");
    assert_eq!(
        *body, inner,
        "body should be the triggered inner exists (not descended into)"
    );
}

// --- expr_mentions_bound_var match arm shadowing (#1246) ---

/// `expr_mentions_bound_var` does not shadow match arm pattern bindings,
/// causing false positives when a match arm binds a name colliding with
/// a bound variable.
#[test]
#[timeout(30000)]
fn expr_mentions_bound_var_false_positive_on_match_arm_shadow() {
    // match x { a => a + 1 }  where "a" is also a bound variable name.
    // The "a" in the arm body refers to the pattern binding, not outer bound.
    let expr = match_expr(
        var("x"),
        vec![(Pattern::Binding("a".to_string()), add(var("a"), int(1)))],
    );
    let bound_vars = vec!["a".to_string()];

    let result = expr_mentions_bound_var(&expr, &bound_vars);

    // Match arm binds "a", so the body's reference to "a" is the pattern
    // binding — not the outer bound variable. Should return false. (#1246)
    assert!(
        !result,
        "match arm binding should shadow outer bound variable"
    );
}

// --- substitute_vars_in_expr capture-avoiding substitution (#1247) ---

/// Capture-avoiding substitution alpha-renames let binders to prevent
/// free variables in substitution values from being captured.
#[test]
#[timeout(30000)]
fn substitute_vars_alpha_renames_let_to_avoid_capture() {
    // let x = 1 in y   with binding { y -> Var("x") }
    // Naive result: let x = 1 in x  (WRONG — free "x" captured by let)
    // Correct: let x$α0 = 1 in x  (alpha-renamed binder, free "x" preserved)
    let expr = let_bind("x", int(1), var("y"));
    let mut binding = HashMap::new();
    binding.insert("y".to_string(), var("x"));

    let result = substitute_vars_in_expr(&expr, &binding);

    // After fix: let binder is alpha-renamed, body references free "x".
    match &result {
        PureExpr::Let { var: v, body, .. } => {
            assert_ne!(
                v, "x",
                "let binder should be alpha-renamed to avoid capture"
            );
            assert_eq!(
                **body,
                var("x"),
                "body should reference the free variable x (from substitution)"
            );
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

/// Capture-avoiding substitution also works for quantifier binders.
#[test]
#[timeout(30000)]
fn substitute_vars_alpha_renames_forall_to_avoid_capture() {
    // forall x. y > x   with binding { y -> Var("x") }
    // Naive: forall x. x > x  (WRONG — free "x" captured by forall)
    // Correct: forall x$α0. x > x$α0
    let expr = forall("x", gt(var("y"), var("x")));
    let mut binding = HashMap::new();
    binding.insert("y".to_string(), var("x"));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Forall { var: v, body, .. } => {
            assert_ne!(
                v, "x",
                "forall binder should be alpha-renamed to avoid capture"
            );
            // The body should reference free "x" (from substitution) and
            // the renamed bound variable
            match body.as_ref() {
                PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
                    assert_eq!(**lhs, var("x"), "lhs should be free x (from substitution)");
                    assert_eq!(
                        **rhs,
                        PureExpr::Var(v.clone(), None),
                        "rhs should reference the renamed bound variable"
                    );
                }
                other => panic!("expected BinOp(Gt), got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// When no capture conflict exists, substitution does not rename.
#[test]
#[timeout(30000)]
fn substitute_vars_no_rename_when_no_capture() {
    // let x = 1 in y   with binding { y -> Var("z") }
    // No capture: "z" doesn't conflict with let-bound "x"
    let expr = let_bind("x", int(1), var("y"));
    let mut binding = HashMap::new();
    binding.insert("y".to_string(), var("z"));

    let result = substitute_vars_in_expr(&expr, &binding);

    match &result {
        PureExpr::Let { var: v, body, .. } => {
            assert_eq!(v, "x", "no rename needed — binder stays as x");
            assert_eq!(**body, var("z"), "body should have y substituted to z");
        }
        other => panic!("expected Let, got {other:?}"),
    }
}
