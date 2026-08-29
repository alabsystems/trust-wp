// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// --- expr_contains_embedded_existential tests ---
// Coverage gap: 16-line function with zero tests. This function controls whether
// postcondition negation uses a special embedded-existential path (mod.rs:693).
// Incorrect results cause either false verification (false negative = misses
// embedded existential) or unnecessary encoding complexity (false positive).

#[test]
#[timeout(30000)]
fn embedded_existential_detects_exists_inside_binop() {
    use super::expr_contains_embedded_existential;
    // A && exists(y, B(y))  — the exists is NOT top-level
    let expr = and(bool_expr(true), exists("y", bool_expr(true)));
    assert!(
        expr_contains_embedded_existential(&expr),
        "exists inside BinOp(And) should be detected as embedded"
    );
}

#[test]
#[timeout(30000)]
fn embedded_existential_top_level_returns_false() {
    use super::expr_contains_embedded_existential;
    // Top-level exists is handled by negate_existential_postcondition, not this path
    let expr = exists("y", bool_expr(true));
    assert!(
        !expr_contains_embedded_existential(&expr),
        "top-level exists should NOT be detected (handled separately)"
    );
}

#[test]
#[timeout(30000)]
fn embedded_existential_no_quantifier_returns_false() {
    use super::expr_contains_embedded_existential;
    let expr = eq(var("x"), int(42));
    assert!(
        !expr_contains_embedded_existential(&expr),
        "plain equality should not be detected"
    );
}

#[test]
#[timeout(30000)]
fn embedded_existential_detected_inside_logic_fn_call() {
    use super::expr_contains_embedded_existential;
    // f(exists(y, P(y))) — existential is inside a LogicFnCall argument.
    // Fixed in #2033: now recurses into LogicFnCall args.
    let expr = logic_fn_call("f", vec![exists("y", bool_expr(true))]);
    assert!(
        expr_contains_embedded_existential(&expr),
        "exists inside LogicFnCall arg should be detected (#2033)"
    );
}

#[test]
#[timeout(30000)]
fn embedded_existential_detected_inside_method_call() {
    use super::expr_contains_embedded_existential;
    use crate::tests::helpers::method_call;
    // x.f(exists(y, P(y))) — existential is inside a MethodCall argument.
    // Fixed in #2033: now recurses into MethodCall args and receiver.
    let expr = method_call(var("x"), "f", vec![exists("y", bool_expr(true))]);
    assert!(
        expr_contains_embedded_existential(&expr),
        "exists inside MethodCall arg should be detected (#2033)"
    );
}

#[test]
#[timeout(30000)]
fn embedded_existential_detected_inside_ite_condition() {
    use super::expr_contains_embedded_existential;
    use crate::tests::helpers::ite;
    // ite(exists(y, P(y)), true, false) — exists in condition
    let expr = ite(
        exists("y", bool_expr(true)),
        bool_expr(true),
        bool_expr(false),
    );
    assert!(
        expr_contains_embedded_existential(&expr),
        "exists inside ITE condition should be detected"
    );
}

#[test]
#[timeout(30000)]
fn embedded_existential_detected_inside_unop() {
    use super::expr_contains_embedded_existential;
    // NOT(exists(y, P(y))) — exists inside UnOp
    let expr = not(exists("y", bool_expr(true)));
    assert!(
        expr_contains_embedded_existential(&expr),
        "exists inside NOT should be detected"
    );
}

#[test]
#[timeout(30000)]
fn embedded_existential_detected_inside_view() {
    use super::expr_contains_embedded_existential;
    use crate::tests::helpers::view;
    // view(exists(y, P(y))) — exists inside View wrapper
    // View IS handled by expr_contains_embedded_existential (line 137)
    let expr = view(exists("y", bool_expr(true)));
    assert!(
        expr_contains_embedded_existential(&expr),
        "exists inside View should be detected"
    );
}

#[test]
#[timeout(30000)]
fn embedded_existential_detected_inside_deref() {
    use super::expr_contains_embedded_existential;
    use crate::tests::helpers::deref;
    // *(exists(y, P(y))) — exists inside Deref
    // Deref IS handled by expr_contains_embedded_existential (line 137)
    let expr = deref(exists("y", bool_expr(true)));
    assert!(
        expr_contains_embedded_existential(&expr),
        "exists inside Deref should be detected"
    );
}

#[test]
#[timeout(30000)]
fn embedded_existential_detected_inside_old() {
    use super::expr_contains_embedded_existential;
    use crate::tests::helpers::old;
    // old(exists(y, P(y))) — existential inside Old wrapper.
    // Fixed in #2033: now recurses into Old (matching contains_any_existential).
    let expr = old(exists("y", bool_expr(true)));
    assert!(
        expr_contains_embedded_existential(&expr),
        "exists inside Old should be detected (#2033)"
    );
}

#[test]
#[timeout(30000)]
fn embedded_existential_detected_inside_final() {
    use super::expr_contains_embedded_existential;
    // ^(exists(y, P(y))) — existential inside Final wrapper.
    // Fixed in #2033: now recurses into Final.
    let expr = PureExpr::Final(Arc::new(exists("y", bool_expr(true))));
    assert!(
        expr_contains_embedded_existential(&expr),
        "exists inside Final should be detected (#2033)"
    );
}

// --- expr_contains_embedded_universal tests ---

#[test]
#[timeout(30000)]
fn embedded_universal_detects_forall_inside_binop() {
    use super::expr_contains_embedded_universal;
    let expr = and(bool_expr(true), forall("x", bool_expr(true)));
    assert!(
        expr_contains_embedded_universal(&expr),
        "forall inside BinOp(And) should be detected as embedded"
    );
}

#[test]
#[timeout(30000)]
fn embedded_universal_top_level_returns_false() {
    use super::expr_contains_embedded_universal;
    let expr = forall("x", bool_expr(true));
    assert!(
        !expr_contains_embedded_universal(&expr),
        "top-level forall should NOT be detected (handled separately)"
    );
}

// --- is_axiom_only_function: logic_fns guard (#2082) ---
// The logic_fns guard at axiom_detection.rs:90-95 rejects functions that have
// Open-mode logic functions, because their defining axioms can make quantified
// postconditions provable (making them lemmas, not axioms).

#[test]
#[timeout(30000)]
fn test_axiom_only_false_when_open_logic_fns_present() {
    let ensures = vec![forall("x", bool_expr(true))];
    let logic_fn = LogicFnDef::new(
        "id".to_string(),
        "test::id".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);
    assert!(
        !is_axiom_only_function(&[], &ensures, None, None, None, Some(&[logic_fn])),
        "Open-mode logic fn should prevent axiom-only classification"
    );
}

#[test]
#[timeout(30000)]
fn test_axiom_only_true_when_opaque_logic_fns_present() {
    let ensures = vec![forall("x", bool_expr(true))];
    let mut logic_fn = LogicFnDef::new(
        "id".to_string(),
        "test::id".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);
    logic_fn.set_is_opaque(true);
    assert!(
        is_axiom_only_function(&[], &ensures, None, None, None, Some(&[logic_fn])),
        "Opaque logic fn should not prevent axiom-only classification"
    );
}

#[test]
#[timeout(30000)]
fn test_axiom_only_true_when_empty_logic_fns() {
    let ensures = vec![forall("x", bool_expr(true))];
    let empty: Vec<trust_wp_core::logic::LogicFnDef> = vec![];
    assert!(
        is_axiom_only_function(&[], &ensures, None, None, None, Some(&empty)),
        "Empty logic_fns slice should not prevent axiom-only classification"
    );
}

// --- has_open_logic_fns (#2082) ---

#[test]
#[timeout(30000)]
fn test_has_open_logic_fns_none() {
    use super::has_open_logic_fns;
    assert!(!has_open_logic_fns(None));
}

#[test]
#[timeout(30000)]
fn test_has_open_logic_fns_empty() {
    use super::has_open_logic_fns;
    let empty: Vec<trust_wp_core::logic::LogicFnDef> = vec![];
    assert!(!has_open_logic_fns(Some(&empty)));
}

#[test]
#[timeout(30000)]
fn test_has_open_logic_fns_with_open() {
    use super::has_open_logic_fns;
    let logic_fn = LogicFnDef::new(
        "f".to_string(),
        "test::f".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);
    assert!(has_open_logic_fns(Some(&[logic_fn])));
}

#[test]
#[timeout(30000)]
fn test_has_open_logic_fns_with_opaque_open() {
    use super::has_open_logic_fns;
    let mut logic_fn = LogicFnDef::new(
        "f".to_string(),
        "test::f".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);
    logic_fn.set_is_opaque(true);
    assert!(
        !has_open_logic_fns(Some(&[logic_fn])),
        "Opaque Open-mode fn should not count"
    );
}

// --- expr_contains_embedded_existential (#2575) ---

#[test]
#[timeout(30000)]
fn expr_contains_embedded_existential_detects_exists_inside_forall() {
    use super::expr_contains_embedded_existential;
    // forall z. exists y. result == Some(y) — the exists is embedded inside forall.
    // Before #2575, this returned false because Forall was not traversed.
    let post = PureExpr::Forall {
        var: "z".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(exists(
            "y",
            eq(var("result"), logic_fn_call("Some", vec![var("y")])),
        )),
        triggers: vec![],
    };
    assert!(
        expr_contains_embedded_existential(&post),
        "forall wrapping an exists should be detected as containing an embedded existential"
    );
}

#[test]
#[timeout(30000)]
fn expr_contains_embedded_existential_top_level_exists_returns_false() {
    use super::expr_contains_embedded_existential;
    // Top-level exists is handled by negate_existential_postcondition, not this path.
    let post = exists(
        "y",
        eq(var("result"), logic_fn_call("Some", vec![var("y")])),
    );
    assert!(
        !expr_contains_embedded_existential(&post),
        "top-level exists should return false (handled separately)"
    );
}

#[test]
#[timeout(30000)]
fn expr_contains_embedded_existential_forall_without_exists_returns_false() {
    use super::expr_contains_embedded_existential;
    // forall z. z > 0 — no existential inside.
    let post = PureExpr::Forall {
        var: "z".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(gt(var("z"), int(0))),
        triggers: vec![],
    };
    assert!(
        !expr_contains_embedded_existential(&post),
        "forall without inner existential should return false"
    );
}

#[test]
#[timeout(30000)]
fn expr_contains_embedded_existential_nested_forall_exists() {
    use super::expr_contains_embedded_existential;
    // forall x. forall z. exists y. P(x, y, z)
    let inner = exists("y", eq(var("y"), var("z")));
    let mid = PureExpr::Forall {
        var: "z".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(inner),
        triggers: vec![],
    };
    let post = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(mid),
        triggers: vec![],
    };
    assert!(
        expr_contains_embedded_existential(&post),
        "nested forall wrapping exists should be detected"
    );
}

#[test]
#[timeout(30000)]
fn test_has_open_logic_fns_default_mode_returns_false() {
    use super::has_open_logic_fns;
    // Default-mode logic functions should NOT count as open — only Open mode does.
    // This ensures the predicate `f.mode == LogicMode::Open` correctly excludes
    // Default, OpenSelf, and Prophetic modes (axiom_detection.rs:125).
    let logic_fn = LogicFnDef::new(
        "f".to_string(),
        "test::f".to_string(),
        vec!["x".to_string()],
        var("x"),
    );
    // LogicFnDef::new defaults to LogicMode::Default
    assert!(
        !has_open_logic_fns(Some(&[logic_fn])),
        "Default-mode logic fn should not count as open"
    );
}
