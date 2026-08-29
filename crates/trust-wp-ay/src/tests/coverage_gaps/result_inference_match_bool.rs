// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for result_inference.rs: match-scrutinee detection, Bool sort
//! inference, and no-signal default behavior.
//!
//! Complements `result_inference_sort_detection.rs` which covers
//! `expr_contains_result_var` traversal and constructor-equality patterns.
//!
//! Coverage targets:
//! - `expr_match_datatype_for_result` — scrutinee-based datatype detection
//! - `expr_requires_result_bool` — Bool-signal edge cases
//! - `result_is_bool_by_postcondition` — empty/no-signal defaults
//! - `result_match_datatype_from_postcondition` — no-signal, mixed match+eq
//!
//! Part of #2177 (result_inference.rs zero test coverage).

use super::*;
use crate::{
    encoder::match_enc::MatchDatatypeKind,
    verify::{
        expr_match_datatype_for_result, expr_requires_result_bool, result_is_bool_by_postcondition,
        result_match_datatype_from_postcondition,
    },
};

// ── expr_match_datatype_for_result: direct API tests ────────────────

/// Direct test: match result { Some(v) => v, _ => 0 } → OptionInt.
#[test]
#[timeout(30000)]
fn expr_match_datatype_direct_option() {
    let expr = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );
    assert_eq!(
        expr_match_datatype_for_result(&expr),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Direct test: scrutinee is not `result` → None.
#[test]
#[timeout(30000)]
fn expr_match_datatype_non_result_scrutinee() {
    let expr = match_expr(
        var("x"),
        vec![(
            Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("v".to_string()))),
            },
            var("v"),
        )],
    );
    assert_eq!(expr_match_datatype_for_result(&expr), None);
}

/// Direct test: Int literal → None.
#[test]
#[timeout(30000)]
fn expr_match_datatype_int_literal() {
    assert_eq!(expr_match_datatype_for_result(&int(42)), None);
}

// ── Match-scrutinee via result_match_datatype_from_postcondition ─────

/// match result { Some(v) => ..., None => ... } → OptionInt.
#[test]
#[timeout(30000)]
fn match_scrutinee_option_constructors() {
    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                gt(var("v"), int(0)),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                bool_expr(false),
            ),
        ],
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// match result { Ok(v) => ..., Err(e) => ... } → ResultIntInt.
#[test]
#[timeout(30000)]
fn match_scrutinee_result_constructors() {
    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                gt(var("v"), int(0)),
            ),
            (
                Pattern::Constructor {
                    name: "Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                bool_expr(false),
            ),
        ],
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::ResultIntInt),
    );
}

/// match result { _ => 0 } — wildcard only, no constructors → None.
#[test]
#[timeout(30000)]
fn match_scrutinee_wildcard_only_no_datatype() {
    let ensures = vec![match_expr(var("result"), vec![(Pattern::Wildcard, int(0))])];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}

/// Nested: match x { _ => match result { Some(v) => v, _ => 0 } }.
#[test]
#[timeout(30000)]
fn match_scrutinee_nested_in_arm_body() {
    let inner_match = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );
    let ensures = vec![match_expr(var("x"), vec![(Pattern::Wildcard, inner_match)])];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Qualified constructor names: std::option::Option::Some.
#[test]
#[timeout(30000)]
fn match_scrutinee_qualified_constructor_names() {
    let ensures = vec![match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "std::option::Option::Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "std::option::Option::None".to_string(),
                    inner: None,
                },
                int(0),
            ),
        ],
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

// ── expr_requires_result_bool: Bool-signal patterns ─────────────────

/// !result (bare negation) requires Bool sort.
#[test]
#[timeout(30000)]
fn requires_result_bool_bare_not() {
    assert!(expr_requires_result_bool(&not(var("result"))));
}

/// Bare `result` as postcondition expression → Bool.
#[test]
#[timeout(30000)]
fn requires_result_bool_bare_result() {
    assert!(expr_requires_result_bool(&var("result")));
}

/// result != false → Bool.
#[test]
#[timeout(30000)]
fn requires_result_bool_ne_false() {
    assert!(expr_requires_result_bool(&ne(
        var("result"),
        bool_expr(false)
    )));
}

/// result == false → Bool.
#[test]
#[timeout(30000)]
fn requires_result_bool_eq_false() {
    assert!(expr_requires_result_bool(&eq(
        var("result"),
        bool_expr(false)
    )));
}

/// false == result → Bool (reversed operand order).
#[test]
#[timeout(30000)]
fn requires_result_bool_eq_reversed() {
    assert!(expr_requires_result_bool(&eq(
        bool_expr(true),
        var("result")
    )));
}

/// !!result (double negation) → Bool.
#[test]
#[timeout(30000)]
fn requires_result_bool_double_not() {
    assert!(expr_requires_result_bool(&not(not(var("result")))));
}

/// result > 0 → NOT Bool (comparison context, not Bool context).
#[test]
#[timeout(30000)]
fn requires_result_bool_gt_not_bool() {
    assert!(!expr_requires_result_bool(&gt(var("result"), int(0))));
}

/// result == 42 → NOT Bool (Int literal, not Bool literal).
#[test]
#[timeout(30000)]
fn requires_result_bool_eq_int_not_bool() {
    assert!(!expr_requires_result_bool(&eq(var("result"), int(42))));
}

/// and(result, x > 0) → Bool via And connector.
#[test]
#[timeout(30000)]
fn requires_result_bool_and_connector() {
    assert!(expr_requires_result_bool(&and(
        var("result"),
        gt(var("x"), int(0))
    )));
}

/// or(x > 0, result) → Bool via Or connector.
#[test]
#[timeout(30000)]
fn requires_result_bool_or_connector() {
    assert!(expr_requires_result_bool(&or(
        gt(var("x"), int(0)),
        var("result")
    )));
}

/// implies(x > 0, result) → Bool via Implies connector.
#[test]
#[timeout(30000)]
fn requires_result_bool_implies_connector() {
    assert!(expr_requires_result_bool(&implies(
        gt(var("x"), int(0)),
        var("result")
    )));
}

/// forall x. result == (x > 0) → Bool through quantifier recursion.
#[test]
#[timeout(30000)]
fn requires_result_bool_forall_eq_bool_expr() {
    assert!(expr_requires_result_bool(&forall(
        "x",
        eq(var("result"), gt(var("x"), int(0)))
    )));
}

/// old(result == true) stays Bool through sort-preserving wrappers.
#[test]
#[timeout(30000)]
fn requires_result_bool_old_wrapper() {
    assert!(expr_requires_result_bool(&old(eq(
        var("result"),
        bool_expr(true)
    ))));
}

/// let_obligation(true, result == xs.contains(1)) uses the Bool-only oracle.
#[test]
#[timeout(30000)]
fn requires_result_bool_let_obligation_contains_method() {
    assert!(expr_requires_result_bool(&let_obligation(
        bool_expr(true),
        eq(
            var("result"),
            method_call(var("xs"), "contains", vec![int(1)])
        )
    )));
}

/// ite(result, 1, 0) → Bool: `result` as Ite condition means Bool sort.
///
/// Production code (result_inference.rs:103) recurses into the Ite condition.
/// This positive case was missing from W3's original 25 tests — only the
/// negative case (result in then-branch) was covered by the companion file.
#[test]
#[timeout(30000)]
fn requires_result_bool_ite_condition_positive() {
    assert!(expr_requires_result_bool(&ite(
        var("result"),
        int(1),
        int(0)
    )));
}

/// ite(x > 0, result, 0) → NOT Bool: `result` in then-branch, not condition.
///
/// Production code (result_inference.rs:103) only recurses into the condition,
/// NOT the then/else branches. A `result` in the then-branch does not imply
/// Bool sort — it could be any sort used as a value.
#[test]
#[timeout(30000)]
fn requires_result_bool_ite_then_branch_not_bool() {
    assert!(!expr_requires_result_bool(&ite(
        gt(var("x"), int(0)),
        var("result"),
        int(0)
    )));
}

/// ite(x > 0, 1, result) → NOT Bool: `result` in else-branch, not condition.
#[test]
#[timeout(30000)]
fn requires_result_bool_ite_else_branch_not_bool() {
    assert!(!expr_requires_result_bool(&ite(
        gt(var("x"), int(0)),
        int(1),
        var("result")
    )));
}

// ── result_is_bool_by_postcondition: no-signal defaults ─────────────

/// Postconditions with no result references → not Bool.
#[test]
#[timeout(30000)]
fn result_is_bool_no_result_references() {
    let ensures = vec![gt(var("x"), int(0)), lt(var("y"), int(100))];
    assert!(!result_is_bool_by_postcondition(&ensures));
}

/// Empty postcondition list → not Bool.
#[test]
#[timeout(30000)]
fn result_is_bool_empty_ensures() {
    let ensures: Vec<PureExpr> = vec![];
    assert!(!result_is_bool_by_postcondition(&ensures));
}

// ── result_match_datatype_from_postcondition: no-signal defaults ────

/// Only Int comparisons on result → None (default Int).
#[test]
#[timeout(30000)]
fn result_datatype_no_constructor_signals() {
    let ensures = vec![gt(var("result"), int(0)), lt(var("result"), int(100))];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}

/// Empty postcondition list → None.
#[test]
#[timeout(30000)]
fn result_datatype_empty_ensures() {
    let ensures: Vec<PureExpr> = vec![];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}

/// Non-constructor logic fn call → None.
#[test]
#[timeout(30000)]
fn result_datatype_result_in_logic_fn_no_constructor() {
    let ensures = vec![eq(var("result"), logic_fn_call("custom_fn", vec![int(1)]))];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}

// ── Mixed match-scrutinee + constructor-eq across clauses ───────────

/// Match (OptionInt) + constructor eq (OptionInt) → consistent → OptionInt.
#[test]
#[timeout(30000)]
fn mixed_match_and_constructor_eq_consistent() {
    let ensures = vec![
        match_expr(
            var("result"),
            vec![
                (
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                    },
                    gt(var("v"), int(0)),
                ),
                (Pattern::Wildcard, bool_expr(true)),
            ],
        ),
        ne(var("result"), var("None")),
    ];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Match (OptionInt) + constructor eq (ResultIntInt) → conflict → None.
#[test]
#[timeout(30000)]
fn mixed_match_and_constructor_eq_conflict() {
    let ensures = vec![
        match_expr(
            var("result"),
            vec![(
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            )],
        ),
        eq(var("result"), logic_fn_call("Ok", vec![int(1)])),
    ];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}
