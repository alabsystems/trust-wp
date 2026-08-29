// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{borrow::Cow, collections::HashSet, sync::Arc};

use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use super::{collect_view_names_as_seq, expr_produces_seq, normalize_seq_receiver_for_scan};

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
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

// ── AC1: expr_produces_seq ──────────────────────────────────────────

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_recognizes_push_back() {
    let expr = method_call(var("s"), "push_back", vec![PureExpr::Int(1)]);
    assert!(expr_produces_seq(&expr), "push_back should produce Seq");
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_recognizes_concat() {
    let expr = method_call(var("s"), "concat", vec![var("t")]);
    assert!(expr_produces_seq(&expr), "concat should produce Seq");
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_recognizes_seq_macro() {
    let expr = logic_fn_call("seq", vec![PureExpr::Int(1)]);
    assert!(
        expr_produces_seq(&expr),
        "seq![...] macro should produce Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_recognizes_seq_empty() {
    let expr = logic_fn_call("seq_empty", vec![]);
    assert!(expr_produces_seq(&expr), "seq_empty() should produce Seq");
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_recognizes_seq_colon_empty() {
    let expr = logic_fn_call("Seq::empty", vec![]);
    assert!(expr_produces_seq(&expr), "Seq::empty() should produce Seq");
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_rejects_non_seq_method() {
    let expr = method_call(var("x"), "abs", vec![]);
    assert!(!expr_produces_seq(&expr), "abs should not produce Seq");
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_rejects_len() {
    let expr = method_call(var("s"), "len", vec![]);
    assert!(
        !expr_produces_seq(&expr),
        "len consumes Seq but returns Int"
    );
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_rejects_bare_var() {
    assert!(!expr_produces_seq(&var("s")), "bare Var is not Seq");
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_propagates_through_old() {
    let expr = PureExpr::Old(Arc::new(method_call(
        var("s"),
        "push_back",
        vec![PureExpr::Int(1)],
    )));
    assert!(
        expr_produces_seq(&expr),
        "Old(push_back) should propagate Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_propagates_through_view() {
    let expr = PureExpr::View(Arc::new(method_call(var("s"), "reverse", vec![])));
    assert!(
        expr_produces_seq(&expr),
        "View(reverse) should propagate Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_propagates_through_ite_branch() {
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(method_call(var("s"), "tail", vec![])),
        Arc::new(var("default")),
    );
    assert!(
        expr_produces_seq(&expr),
        "Ite with Seq-producing then-branch should produce Seq"
    );
}

// ── AC3: normalize_seq_receiver_for_scan ────────────────────────────

#[test]
#[timeout(30000)]
fn test_normalize_wraps_bare_var_in_view() {
    let input = var("v");
    let result = normalize_seq_receiver_for_scan(&input);
    assert!(
        matches!(result, Cow::Owned(PureExpr::View(_))),
        "bare Var should be wrapped in View, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_normalize_preserves_existing_view() {
    let input = PureExpr::View(Arc::new(var("v")));
    let result = normalize_seq_receiver_for_scan(&input);
    assert!(
        matches!(result, Cow::Borrowed(_)),
        "View(Var) should be borrowed (no wrapping), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_normalize_preserves_seq_producing_method() {
    let input = method_call(var("s"), "push_back", vec![PureExpr::Int(1)]);
    let result = normalize_seq_receiver_for_scan(&input);
    assert!(
        matches!(result, Cow::Borrowed(_)),
        "push_back result should not be wrapped, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_normalize_preserves_seq_constructor() {
    let input = logic_fn_call("seq", vec![PureExpr::Int(42)]);
    let result = normalize_seq_receiver_for_scan(&input);
    assert!(
        matches!(result, Cow::Borrowed(_)),
        "seq![] constructor should not be wrapped, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_normalize_preserves_old_of_view() {
    let input = PureExpr::Old(Arc::new(PureExpr::View(Arc::new(var("v")))));
    let result = normalize_seq_receiver_for_scan(&input);
    assert!(
        matches!(result, Cow::Borrowed(_)),
        "Old(View(Var)) should be borrowed, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_normalize_wraps_int_literal_in_view() {
    let input = PureExpr::Int(42);
    let result = normalize_seq_receiver_for_scan(&input);
    assert!(
        matches!(result, Cow::Owned(PureExpr::View(_))),
        "Int literal should be wrapped in View, got {result:?}"
    );
}

// ── collect_view_names_as_seq ───────────────────────────────────────

#[test]
#[timeout(30000)]
fn test_collect_view_names_tags_bare_var() {
    let mut names = HashSet::new();
    collect_view_names_as_seq(&var("result"), &mut names);
    assert!(
        names.contains("result"),
        "bare Var should be collected: {names:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_view_names_tags_view_var() {
    let mut names = HashSet::new();
    let expr = PureExpr::View(Arc::new(var("v")));
    collect_view_names_as_seq(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "View(Var) should produce v_view: {names:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_view_names_skips_bare_var_inside_view() {
    let mut names = HashSet::new();
    let expr = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Deref(
        Arc::new(var("x")),
    )))));
    collect_view_names_as_seq(&expr, &mut names);
    assert!(
        !names.contains("x"),
        "bare Var inside View(Final(Deref(...))) should NOT be tagged: {names:?}"
    );
}

// ── AC: pop_back detection ───────────────────────────────────────────

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_recognizes_pop_back() {
    let expr = method_call(var("s"), "pop_back", vec![]);
    assert!(expr_produces_seq(&expr), "pop_back should produce Seq");
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_recognizes_pop_back_ghost() {
    let expr = method_call(var("s"), "pop_back_ghost", vec![]);
    assert!(
        expr_produces_seq(&expr),
        "pop_back_ghost should produce Seq"
    );
}

// ── AC: nested View(Deref(x)) normalization ─────────────────────────

#[test]
#[timeout(30000)]
fn test_normalize_preserves_view_of_deref() {
    // View(Deref(Var("v"))) — the View wrapper is already present, so
    // normalize should borrow (not double-wrap).
    let input = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(var("v")))));
    let result = normalize_seq_receiver_for_scan(&input);
    assert!(
        matches!(result, Cow::Borrowed(_)),
        "View(Deref(Var)) should be borrowed (already View-wrapped), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_normalize_wraps_deref_var_in_view() {
    // Deref(Var("v")) without a View wrapper — normalize should add View.
    let input = PureExpr::Deref(Arc::new(var("v")));
    let result = normalize_seq_receiver_for_scan(&input);
    assert!(
        matches!(result, Cow::Owned(PureExpr::View(_))),
        "Deref(Var) without View wrapper should be wrapped, got {result:?}"
    );
}

// ── AC: Seq::empty as static method call ────────────────────────────

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_recognizes_static_seq_empty_method() {
    // Seq::empty() encoded as MethodCall { receiver: Var("Seq"), method: "empty", args: [] }
    let expr = method_call(var("Seq"), "empty", vec![]);
    assert!(
        expr_produces_seq(&expr),
        "Seq::empty() as static method call should produce Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_recognizes_static_seq_singleton_method() {
    // Seq::singleton(v) encoded as MethodCall { receiver: Var("Seq"), method: "singleton", args: [v] }
    let expr = method_call(var("Seq"), "singleton", vec![PureExpr::Int(1)]);
    assert!(
        expr_produces_seq(&expr),
        "Seq::singleton(v) as static method call should produce Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_recognizes_static_seq_singleton_logic_fn() {
    let expr = logic_fn_call("Seq::singleton", vec![PureExpr::Int(1)]);
    assert!(
        expr_produces_seq(&expr),
        "Seq::singleton(v) as logic function call should produce Seq"
    );
}

#[test]
#[timeout(30000)]
fn test_expr_produces_seq_rejects_non_seq_static_empty() {
    // SomeOtherType::empty() should NOT be detected as Seq
    let expr = method_call(var("HashMap"), "empty", vec![]);
    assert!(
        !expr_produces_seq(&expr),
        "HashMap::empty() should not produce Seq"
    );
}

// ── AC: collect_view_names_as_seq with nested View(Deref(x)) ────────

#[test]
#[timeout(30000)]
fn test_collect_view_names_nested_view_deref_collects_view_name() {
    let mut names = HashSet::new();
    // View(Deref(Var("x"))) should resolve to a view-derived name via
    // resolve_view_var_name, but should NOT collect bare "x".
    let expr = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(var("x")))));
    collect_view_names_as_seq(&expr, &mut names);
    assert!(
        !names.contains("x"),
        "bare Var inside View(Deref(...)) should NOT be tagged: {names:?}"
    );
    // The resolved view name (e.g., "x_view" or "deref_x_view") should be present
    assert!(
        !names.is_empty(),
        "View(Deref(Var(x))) should collect at least one view-derived name: {names:?}"
    );
}

// ── AC: collect_seq_view_names (integrated scanner) ─────────────────

use super::collect_seq_view_names;

#[test]
#[timeout(30000)]
fn test_scan_push_back_method_tags_receiver() {
    let mut names = HashSet::new();
    // v@.push_back(1) — the receiver View(Var("v")) should be tagged as Seq
    let expr = method_call(
        PureExpr::View(Arc::new(var("v"))),
        "push_back",
        vec![PureExpr::Int(1)],
    );
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "push_back receiver View(Var(v)) should tag v_view as Seq: {names:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_scan_concat_tags_receiver() {
    let mut names = HashSet::new();
    // v@.concat(w@) — concat is a Seq-only method, so the receiver is tagged.
    // The argument is only tagged via equality propagation (not direct method scan),
    // because `collect_seq_view_names` only tags receivers of Seq-only methods.
    let expr = method_call(
        PureExpr::View(Arc::new(var("v"))),
        "concat",
        vec![PureExpr::View(Arc::new(var("w")))],
    );
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "concat receiver should be tagged: {names:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_scan_equality_propagation_seq_to_var() {
    let mut names = HashSet::new();
    use trust_wp_core::formula::BinOp;
    // result == v@.push_back(1) — equality propagation should tag "result" as Seq
    let expr = PureExpr::BinOp(
        Arc::new(var("result")),
        BinOp::Eq,
        Arc::new(method_call(
            PureExpr::View(Arc::new(var("v"))),
            "push_back",
            vec![PureExpr::Int(1)],
        )),
    );
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("result"),
        "equality with Seq-producing RHS should tag LHS 'result': {names:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_scan_ext_eq_tags_both_sides() {
    let mut names = HashSet::new();
    // v@.ext_eq(w@) — ext_eq should tag both receiver and argument
    let expr = method_call(
        PureExpr::View(Arc::new(var("v"))),
        "ext_eq",
        vec![PureExpr::View(Arc::new(var("w")))],
    );
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "ext_eq receiver should be tagged: {names:?}"
    );
    assert!(
        names.contains("w_view"),
        "ext_eq argument should be tagged: {names:?}"
    );
}
