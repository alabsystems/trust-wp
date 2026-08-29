// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// --- is_axiom_only_function ---

/// Helper: construct a tuple0 body (trivial unit value).
fn tuple0_body() -> PureExpr {
    let name = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(0);
    logic_fn_call(&name, vec![])
}

#[test]
#[timeout(30000)]
fn test_axiom_only_true_positive() {
    // No requires, universal ensures, trivial body, no invariants, no ghost
    let ensures = vec![forall("x", bool_expr(true))];
    assert!(is_axiom_only_function(
        &[],
        &ensures,
        None,
        None,
        None,
        None
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_true_positive_with_tuple0_body() {
    let ensures = vec![forall("x", bool_expr(true))];
    let body = tuple0_body();
    assert!(is_axiom_only_function(
        &[],
        &ensures,
        Some(&body),
        None,
        None,
        None,
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_false_when_requires_present() {
    let requires = vec![bool_expr(true)];
    let ensures = vec![forall("x", bool_expr(true))];
    assert!(!is_axiom_only_function(
        &requires, &ensures, None, None, None, None,
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_false_when_ensures_empty() {
    assert!(!is_axiom_only_function(&[], &[], None, None, None, None));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_false_when_ensures_reference_result() {
    // ensures: forall x. result == x
    let ensures = vec![forall("y", eq(var("result"), var("y")))];
    assert!(
        expr_contains_result_var(&ensures[0]),
        "sanity: ensures should contain result"
    );
    assert!(!is_axiom_only_function(
        &[],
        &ensures,
        None,
        None,
        None,
        None
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_false_when_type_invariants_present() {
    let ensures = vec![forall("x", bool_expr(true))];
    let invariants = vec![trust_wp_core::type_invariant_def! {
        type_name: "Counter".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: bool_expr(true),
        is_newtype: false,
        element_invariant_method: None,
    }];
    assert!(!is_axiom_only_function(
        &[],
        &ensures,
        None,
        Some(&invariants),
        None,
        None,
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_false_when_ghost_context_present() {
    let ensures = vec![forall("x", bool_expr(true))];
    let ghost = vec![bool_expr(true)];
    assert!(!is_axiom_only_function(
        &[],
        &ensures,
        None,
        None,
        Some(&ghost),
        None,
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_false_when_body_non_trivial() {
    let ensures = vec![forall("x", bool_expr(true))];
    let body = var("x"); // non-trivial body
    assert!(!is_axiom_only_function(
        &[],
        &ensures,
        Some(&body),
        None,
        None,
        None,
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_false_when_ensures_not_universal() {
    // ensures is a plain expression, not Forall
    let ensures = vec![eq(var("a"), var("b"))];
    assert!(!is_axiom_only_function(
        &[],
        &ensures,
        None,
        None,
        None,
        None
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_false_when_ensures_is_exists() {
    let ensures = vec![exists("x", bool_expr(true))];
    assert!(!is_axiom_only_function(
        &[],
        &ensures,
        None,
        None,
        None,
        None
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_nested_forall_accepted() {
    // Forall { body: Forall { .. } } should be accepted
    let ensures = vec![forall("x", forall("y", bool_expr(true)))];
    assert!(is_axiom_only_function(
        &[],
        &ensures,
        None,
        None,
        None,
        None
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_forall_wrapping_exists_accepted() {
    // Forall { body: Exists { .. } } — outer is Forall, so it's universal
    let ensures = vec![forall("x", exists("y", bool_expr(true)))];
    assert!(is_axiom_only_function(
        &[],
        &ensures,
        None,
        None,
        None,
        None
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_multiple_universal_ensures() {
    // Multiple forall postconditions should all be checked
    let ensures = vec![forall("x", bool_expr(true)), forall("y", bool_expr(true))];
    assert!(is_axiom_only_function(
        &[],
        &ensures,
        None,
        None,
        None,
        None
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_mixed_ensures_rejected() {
    // One universal, one non-universal => not axiom-only
    let ensures = vec![forall("x", bool_expr(true)), eq(var("a"), var("b"))];
    assert!(!is_axiom_only_function(
        &[],
        &ensures,
        None,
        None,
        None,
        None
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_empty_type_invariants_still_axiom() {
    // Empty type_invariants slice is not the same as "has invariants"
    let ensures = vec![forall("x", bool_expr(true))];
    let empty_invariants: Vec<TypeInvariantDef> = vec![];
    assert!(is_axiom_only_function(
        &[],
        &ensures,
        None,
        Some(&empty_invariants),
        None,
        None,
    ));
}

#[test]
#[timeout(30000)]
fn test_axiom_only_empty_ghost_context_still_axiom() {
    // Empty ghost_context slice is not the same as "has ghost context"
    let ensures = vec![forall("x", bool_expr(true))];
    let empty_ghost: Vec<PureExpr> = vec![];
    assert!(is_axiom_only_function(
        &[],
        &ensures,
        None,
        None,
        Some(&empty_ghost),
        None,
    ));
}
