// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::formula::{BinOp, MatchArm, Pattern, PureExpr};

fn focus_vars(names: &[&str]) -> HashSet<String> {
    names.iter().map(|name| (*name).to_string()).collect()
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

#[test]
fn expr_references_focus_vars_var_match_and_miss() {
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&var("x"), &focus));
    assert!(!super::expr_references_focus_vars(&var("y"), &focus));
}

#[test]
fn expr_references_focus_vars_nested_binop() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(1)),
        BinOp::Add,
        Arc::new(PureExpr::BinOp(
            Arc::new(var("z")),
            BinOp::Eq,
            Arc::new(var("x")),
        )),
    );
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

#[test]
fn expr_references_focus_vars_forall_body() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("i")),
            BinOp::Eq,
            Arc::new(var("x")),
        )),
        triggers: Vec::new(),
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

#[test]
fn expr_references_focus_vars_match_arm_body() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("v")),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: var("x"),
        }],
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

// === Strengthening tests: negative cases (Part of #901) ===

/// Forall with no focus vars in body or triggers must return false.
/// Guards against regression to "always true" for quantifier arms.
#[test]
fn expr_references_focus_vars_forall_no_match() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("i")),
            BinOp::Eq,
            Arc::new(var("y")),
        )),
        triggers: Vec::new(),
    };
    let focus = focus_vars(&["x"]);
    assert!(!super::expr_references_focus_vars(&expr, &focus));
}

/// Match with no focus vars in scrutinee or arm bodies must return false.
#[test]
fn expr_references_focus_vars_match_no_match() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("v")),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: var("y"),
        }],
    };
    let focus = focus_vars(&["x"]);
    assert!(!super::expr_references_focus_vars(&expr, &focus));
}

// === Strengthening tests: previously-untested variant coverage (#1710) ===

/// Exists body references focus var — exercises the Exists arm added in d3ebfc7a.
#[test]
fn expr_references_focus_vars_exists_body() {
    let expr = PureExpr::Exists {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("j")),
            BinOp::Eq,
            Arc::new(var("x")),
        )),
        triggers: Vec::new(),
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

/// Exists with no focus vars must return false.
#[test]
fn expr_references_focus_vars_exists_no_match() {
    let expr = PureExpr::Exists {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("j")),
            BinOp::Eq,
            Arc::new(PureExpr::Int(42)),
        )),
        triggers: Vec::new(),
    };
    let focus = focus_vars(&["x"]);
    assert!(!super::expr_references_focus_vars(&expr, &focus));
}

/// Forall with focus var only in a trigger — exercises the trigger traversal path.
#[test]
fn expr_references_focus_vars_forall_trigger_only() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("i")),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        )),
        triggers: vec![vec![var("x")]],
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

/// Let binding: focus var in value sub-expression.
#[test]
fn expr_references_focus_vars_let_value() {
    let expr = PureExpr::Let {
        var: "tmp".to_string(),
        value: Arc::new(var("x")),
        body: Arc::new(var("tmp")),
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

/// Let binding: focus var in body sub-expression.
#[test]
fn expr_references_focus_vars_let_body() {
    let expr = PureExpr::Let {
        var: "tmp".to_string(),
        value: Arc::new(PureExpr::Int(1)),
        body: Arc::new(var("x")),
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

/// Let binding: no focus vars anywhere.
#[test]
fn expr_references_focus_vars_let_no_match() {
    let expr = PureExpr::Let {
        var: "tmp".to_string(),
        value: Arc::new(PureExpr::Int(1)),
        body: Arc::new(var("tmp")),
    };
    let focus = focus_vars(&["x"]);
    assert!(!super::expr_references_focus_vars(&expr, &focus));
}

/// LetAssume: focus var in assumption.
#[test]
fn expr_references_focus_vars_let_assume_assumption() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::BinOp(
            Arc::new(var("x")),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
        body: Arc::new(var("y")),
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

/// LetAssume: focus var in body only.
#[test]
fn expr_references_focus_vars_let_assume_body() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(var("x")),
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

/// LetAssume: no focus vars anywhere.
#[test]
fn expr_references_focus_vars_let_assume_no_match() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(var("y")),
    };
    let focus = focus_vars(&["x"]);
    assert!(!super::expr_references_focus_vars(&expr, &focus));
}

/// LetObligation: focus var in obligation.
#[test]
fn expr_references_focus_vars_let_obligation_obligation() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::BinOp(
            Arc::new(var("x")),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )),
        body: Arc::new(PureExpr::Int(1)),
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

/// LetObligation: no focus vars.
#[test]
fn expr_references_focus_vars_let_obligation_no_match() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(PureExpr::Int(1)),
    };
    let focus = focus_vars(&["x"]);
    assert!(!super::expr_references_focus_vars(&expr, &focus));
}

/// Closure: focus var in body.
#[test]
fn expr_references_focus_vars_closure_body() {
    let expr = PureExpr::Closure {
        params: vec![("p".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("p")),
            BinOp::Add,
            Arc::new(var("x")),
        )),
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

/// Closure: no focus vars in body.
#[test]
fn expr_references_focus_vars_closure_no_match() {
    let expr = PureExpr::Closure {
        params: vec![("p".to_string(), None)],
        body: Arc::new(var("p")),
    };
    let focus = focus_vars(&["x"]);
    assert!(!super::expr_references_focus_vars(&expr, &focus));
}

/// Match with focus var in scrutinee but not in arm bodies — verifies
/// scrutinee traversal is independent of arm body traversal.
#[test]
fn expr_references_focus_vars_match_scrutinee_only() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: var("y"),
        }],
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
}

/// Wrapper expressions should recurse into the wrapped term rather than
/// dropping focus vars hidden behind view/final/old/deref layers.
#[test]
fn expr_references_focus_vars_wrappers_recurse() {
    let focus = focus_vars(&["x"]);

    let deref_expr = PureExpr::Deref(Arc::new(var("x")));
    let final_expr = PureExpr::Final(Arc::new(var("x")));
    let view_expr = PureExpr::View(Arc::new(var("x")));
    let old_expr = PureExpr::Old(Arc::new(var("x")));
    let deref_miss = PureExpr::Deref(Arc::new(var("y")));
    let final_miss = PureExpr::Final(Arc::new(var("y")));
    let view_miss = PureExpr::View(Arc::new(var("y")));
    let old_miss = PureExpr::Old(Arc::new(var("y")));

    assert!(super::expr_references_focus_vars(&deref_expr, &focus));
    assert!(super::expr_references_focus_vars(&final_expr, &focus));
    assert!(super::expr_references_focus_vars(&view_expr, &focus));
    assert!(super::expr_references_focus_vars(&old_expr, &focus));
    assert!(!super::expr_references_focus_vars(&deref_miss, &focus));
    assert!(!super::expr_references_focus_vars(&final_miss, &focus));
    assert!(!super::expr_references_focus_vars(&view_miss, &focus));
    assert!(!super::expr_references_focus_vars(&old_miss, &focus));
}

/// ITE traversal must inspect the condition and both branches. Dropping any of
/// the three lanes would silently discard connected ghost assumptions.
#[test]
fn expr_references_focus_vars_ite_reaches_all_children() {
    let focus = focus_vars(&["x"]);

    let cond_expr = PureExpr::Ite(
        Arc::new(var("x")),
        Arc::new(PureExpr::Int(1)),
        Arc::new(PureExpr::Int(0)),
    );
    let then_expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(var("x")),
        Arc::new(PureExpr::Int(0)),
    );
    let else_expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::Int(1)),
        Arc::new(var("x")),
    );
    let miss_expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::Int(1)),
        Arc::new(var("y")),
    );

    assert!(super::expr_references_focus_vars(&cond_expr, &focus));
    assert!(super::expr_references_focus_vars(&then_expr, &focus));
    assert!(super::expr_references_focus_vars(&else_expr, &focus));
    assert!(!super::expr_references_focus_vars(&miss_expr, &focus));
}

/// Method-call traversal must cover both receiver and argument expressions.
#[test]
fn expr_references_focus_vars_method_call_receiver_and_args() {
    let focus = focus_vars(&["x"]);

    let receiver_expr = PureExpr::MethodCall {
        receiver: Arc::new(var("x")),
        method: "len".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    let args_expr = PureExpr::MethodCall {
        receiver: Arc::new(var("seq")),
        method: "get".to_string(),
        args: vec![var("x")],
    };
    let miss_expr = PureExpr::MethodCall {
        receiver: Arc::new(var("seq")),
        method: "get".to_string(),
        args: vec![var("y")],
    };

    assert!(super::expr_references_focus_vars(&receiver_expr, &focus));
    assert!(super::expr_references_focus_vars(&args_expr, &focus));
    assert!(!super::expr_references_focus_vars(&miss_expr, &focus));
}

/// Logic function calls should retain focus vars appearing in any argument.
#[test]
fn expr_references_focus_vars_logic_fn_args() {
    let expr = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![PureExpr::Int(0), var("x")],
    };
    let miss_expr = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![PureExpr::Int(0), var("y")],
    };
    let focus = focus_vars(&["x"]);
    assert!(super::expr_references_focus_vars(&expr, &focus));
    assert!(!super::expr_references_focus_vars(&miss_expr, &focus));
}
