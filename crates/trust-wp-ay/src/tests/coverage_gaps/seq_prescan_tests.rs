// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `encoder/seq/prescan.rs` functions with zero external test coverage
//! (#2514).
//!
//! Targets:
//! - `expr_produces_seq`: predicate for Seq-producing expressions (0 test refs)
//! - `collect_view_names_as_seq`: collects variable names needing Seq sort (0 test refs)
//!
//! Both are pure functions on PureExpr — no encoder state needed.

use std::{collections::HashSet, sync::Arc};

use ntest::timeout;
use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

use crate::encoder::seq::{collect_view_names_as_seq, expr_produces_seq};

// ── Helpers ──────────────────────────────────────────────────────────

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
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

fn logic_fn_call(name: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args,
    }
}

fn collect_names(expr: &PureExpr) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_view_names_as_seq(expr, &mut names);
    names
}

// ── expr_produces_seq ────────────────────────────────────────────────

/// `push_back` method produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_push_back() {
    let expr = method_call(view(var("v")), "push_back", vec![PureExpr::Int(1)]);
    assert!(expr_produces_seq(&expr), "push_back should produce Seq");
}

/// `concat` method produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_concat() {
    let expr = method_call(view(var("v")), "concat", vec![view(var("w"))]);
    assert!(expr_produces_seq(&expr), "concat should produce Seq");
}

/// `reverse` method produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_reverse() {
    let expr = method_call(view(var("v")), "reverse", vec![]);
    assert!(expr_produces_seq(&expr), "reverse should produce Seq");
}

/// `subsequence` method produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_subsequence() {
    let expr = method_call(
        view(var("v")),
        "subsequence",
        vec![PureExpr::Int(0), PureExpr::Int(3)],
    );
    assert!(expr_produces_seq(&expr), "subsequence should produce Seq");
}

/// `seq_empty` logic fn call produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_seq_empty() {
    let expr = logic_fn_call("seq_empty", vec![]);
    assert!(expr_produces_seq(&expr), "seq_empty should produce Seq");
}

/// `Seq::empty` logic fn call produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_qualified_empty() {
    let expr = logic_fn_call("Seq::empty", vec![]);
    assert!(expr_produces_seq(&expr), "Seq::empty should produce Seq");
}

/// `seq` logic fn call (constructor) produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_constructor() {
    let expr = logic_fn_call("seq", vec![PureExpr::Int(1), PureExpr::Int(2)]);
    assert!(expr_produces_seq(&expr), "seq![...] should produce Seq");
}

/// Plain variable does NOT produce Seq.
#[test]
#[timeout(30000)]
fn produces_seq_plain_var() {
    assert!(!expr_produces_seq(&var("x")));
}

/// Int literal does NOT produce Seq.
#[test]
#[timeout(30000)]
fn produces_seq_int_literal() {
    assert!(!expr_produces_seq(&PureExpr::Int(42)));
}

/// `len` method does NOT produce Seq.
#[test]
#[timeout(30000)]
fn produces_seq_len_is_not_seq() {
    let expr = method_call(view(var("v")), "len", vec![]);
    assert!(!expr_produces_seq(&expr), "len does not produce Seq");
}

/// Unknown logic fn does NOT produce Seq.
#[test]
#[timeout(30000)]
fn produces_seq_unknown_fn() {
    let expr = logic_fn_call("my_predicate", vec![var("x")]);
    assert!(
        !expr_produces_seq(&expr),
        "unknown fn should not produce Seq"
    );
}

/// View wrapping a Seq-producing call still produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_view_of_push_back() {
    let inner = method_call(view(var("v")), "push_back", vec![PureExpr::Int(1)]);
    let expr = view(inner);
    assert!(
        expr_produces_seq(&expr),
        "View(push_back(...)) should produce Seq"
    );
}

/// Old wrapping a Seq-producing call still produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_old_of_seq_empty() {
    let expr = PureExpr::Old(Arc::new(logic_fn_call("seq_empty", vec![])));
    assert!(
        expr_produces_seq(&expr),
        "Old(seq_empty) should produce Seq"
    );
}

/// Deref wrapping a Seq-producing call still produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_deref_of_seq() {
    let expr = PureExpr::Deref(Arc::new(logic_fn_call("seq", vec![PureExpr::Int(1)])));
    assert!(
        expr_produces_seq(&expr),
        "Deref(seq![1]) should produce Seq"
    );
}

/// Final wrapping a Seq-producing call still produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_final_of_seq() {
    let expr = PureExpr::Final(Arc::new(logic_fn_call("seq_empty", vec![])));
    assert!(
        expr_produces_seq(&expr),
        "Final(seq_empty) should produce Seq"
    );
}

/// Ite with Seq-producing then-branch produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_ite_then_branch() {
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(logic_fn_call("seq_empty", vec![])),
        Arc::new(PureExpr::Int(0)),
    );
    assert!(
        expr_produces_seq(&expr),
        "Ite with seq_empty in then-branch should produce Seq"
    );
}

/// Match with Seq-producing arm body produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_match_arm() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: logic_fn_call("seq_empty", vec![]),
        }],
    };
    assert!(
        expr_produces_seq(&expr),
        "Match with seq_empty arm should produce Seq"
    );
}

/// Let with Seq-producing body produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_let_body() {
    let expr = PureExpr::Let {
        var: "tmp".to_string(),
        value: Arc::new(PureExpr::Int(0)),
        body: Arc::new(logic_fn_call("seq_empty", vec![])),
    };
    assert!(
        expr_produces_seq(&expr),
        "Let with seq_empty body should produce Seq"
    );
}

/// LetAssume with Seq-producing body produces Seq.
#[test]
#[timeout(30000)]
fn produces_seq_let_assume_body() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(logic_fn_call("seq_empty", vec![])),
    };
    assert!(
        expr_produces_seq(&expr),
        "LetAssume with seq_empty body should produce Seq"
    );
}

// ── collect_view_names_as_seq ────────────────────────────────────────

/// View(Var("x")) collects "x_view" (via resolve_view_var_name) and
/// does NOT collect bare "x" (inside_view flag).
#[test]
#[timeout(30000)]
fn collect_view_var_gets_view_name() {
    let names = collect_names(&view(var("x")));
    assert!(
        names.contains("x_view"),
        "View(Var(x)) should collect x_view: got {names:?}"
    );
    assert!(
        !names.contains("x"),
        "View(Var(x)) should NOT collect bare x (inside_view): got {names:?}"
    );
}

/// Bare Var("result") collects "result" directly.
#[test]
#[timeout(30000)]
fn collect_bare_var_gets_name() {
    let names = collect_names(&var("result"));
    assert!(
        names.contains("result"),
        "bare Var(result) should be collected: got {names:?}"
    );
}

/// Int literal collects nothing.
#[test]
#[timeout(30000)]
fn collect_int_literal_empty() {
    let names = collect_names(&PureExpr::Int(42));
    assert!(names.is_empty(), "Int literal should collect nothing");
}

/// Old(Var("x")) collects "x" (Old is transparent, not inside View).
#[test]
#[timeout(30000)]
fn collect_old_var() {
    let expr = PureExpr::Old(Arc::new(var("x")));
    let names = collect_names(&expr);
    assert!(
        names.contains("x"),
        "Old(Var(x)) should collect x: got {names:?}"
    );
}

/// View(Final(Var("x"))): collects the view-resolved name but NOT bare "x".
#[test]
#[timeout(30000)]
fn collect_view_final_var_suppresses_bare() {
    let expr = view(PureExpr::Final(Arc::new(var("x"))));
    let names = collect_names(&expr);
    // View(Final(Var(x))) resolves to "final_x_view" or similar via resolve_view_var_name
    // The bare "x" should NOT be collected due to inside_view=true
    assert!(
        !names.contains("x"),
        "View(Final(Var(x))): bare x should NOT be collected (inside_view=true): got {names:?}"
    );
}

/// Ite branches are both traversed.
#[test]
#[timeout(30000)]
fn collect_ite_both_branches() {
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(var("a")),
        Arc::new(var("b")),
    );
    let names = collect_names(&expr);
    assert!(names.contains("a"), "Ite then-branch should be collected");
    assert!(names.contains("b"), "Ite else-branch should be collected");
}

/// Match arm bodies are traversed.
#[test]
#[timeout(30000)]
fn collect_match_arm_bodies() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Int(0)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Wildcard,
                body: var("arm1"),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: var("arm2"),
            },
        ],
    };
    let names = collect_names(&expr);
    assert!(names.contains("arm1"), "first arm body should be collected");
    assert!(
        names.contains("arm2"),
        "second arm body should be collected"
    );
}

/// Let body is traversed.
#[test]
#[timeout(30000)]
fn collect_let_body() {
    let expr = PureExpr::Let {
        var: "tmp".to_string(),
        value: Arc::new(PureExpr::Int(0)),
        body: Arc::new(var("result")),
    };
    let names = collect_names(&expr);
    assert!(
        names.contains("result"),
        "Let body should be collected: got {names:?}"
    );
}

/// LetAssume body is traversed.
#[test]
#[timeout(30000)]
fn collect_let_assume_body() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(var("x")),
    };
    let names = collect_names(&expr);
    assert!(
        names.contains("x"),
        "LetAssume body should be collected: got {names:?}"
    );
}

/// LetObligation body is traversed.
#[test]
#[timeout(30000)]
fn collect_let_obligation_body() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(var("x")),
    };
    let names = collect_names(&expr);
    assert!(
        names.contains("x"),
        "LetObligation body should be collected: got {names:?}"
    );
}

/// Deref(Var("r")) collects "r" (Deref is transparent outside View).
#[test]
#[timeout(30000)]
fn collect_deref_var() {
    let expr = PureExpr::Deref(Arc::new(var("r")));
    let names = collect_names(&expr);
    assert!(
        names.contains("r"),
        "Deref(Var(r)) should collect r: got {names:?}"
    );
}

/// Final(Var("x")) collects "x" (Final is transparent outside View).
#[test]
#[timeout(30000)]
fn collect_final_var() {
    let expr = PureExpr::Final(Arc::new(var("x")));
    let names = collect_names(&expr);
    assert!(
        names.contains("x"),
        "Final(Var(x)) should collect x: got {names:?}"
    );
}
