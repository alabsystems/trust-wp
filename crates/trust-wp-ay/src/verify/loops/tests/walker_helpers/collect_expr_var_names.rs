// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `collect_expr_var_names` (#2116).

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::formula::{BinOp, ExprSort, MatchArm, Pattern, PureExpr};

use super::super::collect_expr_var_names;

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn seq_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Seq))
}

fn view(expr: PureExpr) -> PureExpr {
    PureExpr::View(Arc::new(expr))
}

fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

fn collect(expr: &PureExpr) -> HashSet<&str> {
    let mut names = HashSet::new();
    collect_expr_var_names(expr, &mut names);
    names
}

#[test]
fn collect_var_names_simple_var() {
    let expr = var("x");
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["x"]));
}

#[test]
fn collect_var_names_view_var() {
    let expr = view(seq_var("produced"));
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["produced"]));
}

#[test]
fn collect_var_names_binop() {
    let expr = PureExpr::BinOp(Arc::new(var("a")), BinOp::Add, Arc::new(var("b")));
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["a", "b"]));
}

#[test]
fn collect_var_names_method_call_with_receiver() {
    let expr = method_call(view(seq_var("produced")), "len", vec![]);
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["produced"]));
}

#[test]
fn collect_var_names_nested_binop_with_method() {
    // produced@.len() <= 1 — should collect "produced"
    let expr = PureExpr::BinOp(
        Arc::new(method_call(view(seq_var("produced")), "len", vec![])),
        BinOp::Le,
        Arc::new(PureExpr::Int(1)),
    );
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["produced"]));
}

#[test]
fn collect_var_names_empty_on_literals() {
    assert!(collect(&PureExpr::Int(42)).is_empty());
    assert!(collect(&PureExpr::Bool(true)).is_empty());
}

#[test]
fn collect_var_names_logic_fn_call_args() {
    let expr = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![var("x"), var("y")],
    };
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["x", "y"]));
}

/// Forall with triggers: trigger-only free variables must still be collected,
/// but the bound variable itself must stay shadowed.
#[test]
fn collect_var_names_forall_trigger_only_var() {
    // forall x. body(x) :pattern (f(anchor))
    // "anchor" appears only in the trigger, not in the body.
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(var("x")),
        triggers: vec![vec![PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![var("anchor")],
        }]],
    };
    let names = collect(&expr);
    assert!(
        names.contains("anchor"),
        "trigger-only variable 'anchor' must be collected; got {names:?}"
    );
    assert!(
        !names.contains("x"),
        "forall-bound variable 'x' must stay shadowed; got {names:?}"
    );
}

/// Exists with triggers: same gap as Forall.
#[test]
fn collect_var_names_exists_trigger_only_var() {
    let expr = PureExpr::Exists {
        var: "y".to_string(),
        var_sort: None,
        body: Arc::new(var("y")),
        triggers: vec![vec![var("witness")]],
    };
    let names = collect(&expr);
    assert!(
        names.contains("witness"),
        "trigger-only variable 'witness' must be collected; got {names:?}"
    );
    assert!(
        !names.contains("y"),
        "exists-bound variable 'y' must stay shadowed; got {names:?}"
    );
}

/// Multiple triggers with nested expressions.
#[test]
fn collect_var_names_multi_trigger_nested() {
    // forall x. body(x) :pattern (f(a)) :pattern (g(b), h(c))
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(var("x")),
        triggers: vec![
            vec![method_call(var("a"), "f", vec![])],
            vec![var("b"), var("c")],
        ],
    };
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["a", "b", "c"]));
}

#[test]
fn collect_var_names_let_bound_var_stays_shadowed() {
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(var("outer")),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("x")),
            BinOp::Add,
            Arc::new(var("free")),
        )),
    };
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["outer", "free"]));
}

#[test]
fn collect_var_names_match_pattern_bindings_stay_shadowed() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("scrutinee")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Binding("bound".to_string()),
                body: var("bound"),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: var("free"),
            },
        ],
    };
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["scrutinee", "free"]));
}

// ── UnOp / Deref / Old / Final / LetAssume / LetObligation / Ite gaps (#2514) ──

#[test]
fn collect_var_names_unop_recurse() {
    let expr = PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, Arc::new(var("flag")));
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["flag"]));
}

#[test]
fn collect_var_names_deref_var() {
    let expr = PureExpr::Deref(Arc::new(var("r")));
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["r"]));
}

#[test]
fn collect_var_names_old_var() {
    let expr = PureExpr::Old(Arc::new(var("x")));
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["x"]));
}

#[test]
fn collect_var_names_final_var() {
    let expr = PureExpr::Final(Arc::new(var("x")));
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["x"]));
}

#[test]
fn collect_var_names_ite() {
    let expr = PureExpr::Ite(
        Arc::new(var("cond")),
        Arc::new(var("then_val")),
        Arc::new(var("else_val")),
    );
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["cond", "then_val", "else_val"]));
}

#[test]
fn collect_var_names_let_assume() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(var("guard")),
        body: Arc::new(var("result")),
    };
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["guard", "result"]));
}

#[test]
fn collect_var_names_let_obligation() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(var("proof")),
        body: Arc::new(var("value")),
    };
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["proof", "value"]));
}

#[test]
fn collect_var_names_closure_params_stay_shadowed() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("x")),
            BinOp::Add,
            Arc::new(var("captured")),
        )),
    };
    let names = collect(&expr);
    assert_eq!(names, HashSet::from(["captured"]));
}
