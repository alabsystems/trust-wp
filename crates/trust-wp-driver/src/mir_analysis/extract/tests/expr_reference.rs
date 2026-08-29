// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;
// ── expr_references_var_name tests (#1450) ──────────────────────────

#[test]
fn expr_references_var_name_finds_direct_var() {
    let expr = PureExpr::Var("pair".to_string(), None);
    assert!(expr_references_var_name(&expr, "pair"));
    assert!(!expr_references_var_name(&expr, "other"));
}

#[test]
fn expr_references_var_name_finds_nested_in_logic_fn_call() {
    // tuple_get_1(pair) — the typical projected-write LHS pattern
    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![PureExpr::Var("pair".to_string(), None)],
    };
    assert!(expr_references_var_name(&expr, "pair"));
    assert!(!expr_references_var_name(&expr, "other"));
}

#[test]
fn expr_references_var_name_finds_in_method_call_receiver() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("v".to_string(), None)),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    assert!(expr_references_var_name(&expr, "v"));
    assert!(!expr_references_var_name(&expr, "w"));
}

#[test]
fn expr_references_var_name_finds_in_binop() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    assert!(expr_references_var_name(&expr, "x"));
    assert!(!expr_references_var_name(&expr, "y"));
}

#[test]
fn expr_references_var_name_returns_false_for_literals() {
    assert!(!expr_references_var_name(&PureExpr::Int(42), "x"));
    assert!(!expr_references_var_name(&PureExpr::Bool(true), "x"));
}

/// Forall/Exists bound variable shadows the search name. (#1468)
#[test]
fn expr_references_var_name_forall_bound_var_shadowing() {
    // forall(|i| i > 0): bound `i` is not a free reference to "i"
    let forall_expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Var("i".to_string(), None)),
        triggers: vec![],
    };
    assert!(
        !expr_references_var_name(&forall_expr, "i"),
        "forall-bound `i` should NOT be detected as free reference"
    );
    // But a different name IS free
    assert!(!expr_references_var_name(&forall_expr, "j"));

    // forall(|j| i > j): `i` is free here
    let forall_free = PureExpr::Forall {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Var("i".to_string(), None)),
        triggers: vec![],
    };
    assert!(
        expr_references_var_name(&forall_free, "i"),
        "Free `i` inside forall(|j| ...) should be detected"
    );

    // Same for Exists
    let exists_expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
        triggers: vec![],
    };
    assert!(!expr_references_var_name(&exists_expr, "x"));
}

#[test]
fn expr_references_var_name_checks_quantifier_triggers() {
    let forall_trigger = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![PureExpr::Var("x".to_string(), None)]],
    };
    assert!(
        expr_references_var_name(&forall_trigger, "x"),
        "free vars inside triggers should count as references"
    );

    let shadowed_trigger = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![PureExpr::Var("x".to_string(), None)]],
    };
    assert!(
        !expr_references_var_name(&shadowed_trigger, "x"),
        "quantifier binders should shadow trigger references too"
    );
}

/// Let-bound variable shadows in body but not in value. (#1468)
#[test]
fn expr_references_var_name_let_bound_var_shadowing() {
    // let x = x + 1; body(x): free `x` in value
    let let_expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::Var("x".to_string(), None)),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    assert!(
        expr_references_var_name(&let_expr, "x"),
        "Free `x` in let value should be detected"
    );

    // let x = 42; body(x): no free `x`
    let let_no_free = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::Int(42)),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    assert!(
        !expr_references_var_name(&let_no_free, "x"),
        "let-bound `x` in body should NOT be detected as free reference"
    );
}

/// Match-arm pattern bindings shadow the search name. (#1468)
#[test]
fn expr_references_var_name_match_pattern_shadowing() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    // match 0 { x => x > 0 }: `x` in body is pattern-bound
    let match_expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Int(0)),
        arms: vec![MatchArm {
            pattern: Pattern::Binding("x".to_string()),
            body: PureExpr::Var("x".to_string(), None),
        }],
    };
    assert!(
        !expr_references_var_name(&match_expr, "x"),
        "Pattern-bound `x` should NOT be detected as free reference"
    );

    // match x { _ => 0 }: scrutinee references free `x`
    let match_scrutinee = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: PureExpr::Int(0),
        }],
    };
    assert!(expr_references_var_name(&match_scrutinee, "x"));
}

/// Closure parameters shadow the search name. (#1468)
#[test]
fn expr_references_var_name_closure_param_shadowing() {
    // |x| x + 1: `x` is a closure param
    let closure_expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    assert!(
        !expr_references_var_name(&closure_expr, "x"),
        "Closure-param `x` should NOT be detected as free reference"
    );

    // |y| x + y: `x` is free
    let closure_free = PureExpr::Closure {
        params: vec![("y".to_string(), None)],
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    assert!(expr_references_var_name(&closure_free, "x"));
}

#[test]
fn expr_mentions_any_fallback_arg_respects_binder_shadowing() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let fallback_arg_names: HashSet<String> = std::iter::once("arg0".to_string()).collect();

    let forall_shadowed = PureExpr::Forall {
        var: "arg0".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Var("arg0".to_string(), None)),
        triggers: vec![],
    };
    assert!(
        !expr_mentions_any_fallback_arg(&forall_shadowed, &fallback_arg_names),
        "forall binder should shadow fallback arg in body"
    );

    let match_shadowed = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Int(0)),
        arms: vec![MatchArm {
            pattern: Pattern::Binding("arg0".to_string()),
            body: PureExpr::Var("arg0".to_string(), None),
        }],
    };
    assert!(
        !expr_mentions_any_fallback_arg(&match_shadowed, &fallback_arg_names),
        "match pattern binding should shadow fallback arg in arm body"
    );

    let let_shadowed = PureExpr::Let {
        var: "arg0".to_string(),
        value: Arc::new(PureExpr::Int(1)),
        body: Arc::new(PureExpr::Var("arg0".to_string(), None)),
    };
    assert!(
        !expr_mentions_any_fallback_arg(&let_shadowed, &fallback_arg_names),
        "let binder should shadow fallback arg in body"
    );

    let closure_shadowed = PureExpr::Closure {
        params: vec![("arg0".to_string(), None)],
        body: Arc::new(PureExpr::Var("arg0".to_string(), None)),
    };
    assert!(
        !expr_mentions_any_fallback_arg(&closure_shadowed, &fallback_arg_names),
        "closure params should shadow fallback arg in body"
    );
}

#[test]
fn expr_mentions_any_fallback_arg_checks_quantifier_triggers() {
    let fallback_arg_names: HashSet<String> = std::iter::once("arg0".to_string()).collect();

    let trigger_ref = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![PureExpr::Var("arg0".to_string(), None)]],
    };
    assert!(
        expr_mentions_any_fallback_arg(&trigger_ref, &fallback_arg_names),
        "fallback args inside triggers should be detected"
    );

    let trigger_shadowed = PureExpr::Forall {
        var: "arg0".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![PureExpr::Var("arg0".to_string(), None)]],
    };
    assert!(
        !expr_mentions_any_fallback_arg(&trigger_shadowed, &fallback_arg_names),
        "quantifier binders should shadow fallback args in triggers too"
    );
}
