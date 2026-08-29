// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq encoding (Part of #111).
//!
//! Includes sequence view, len, index, `push_back`, error handling, and axiom tests.
//! Split from encoding.rs per #395.

use super::*;

// =============================================================================
// Seq View, Len, and Index Tests
// =============================================================================

#[test]
#[timeout(30000)]
fn test_encode_seq_view() {
    // View(Var("v")) without Seq context creates an Int-typed variable (#544).
    // Views default to Int (numeric types like u8@, i32@). Seq sort is only
    // assigned when the View is used as a Seq method receiver or compared
    // with a Seq-producing expression.
    let mut encoder = AYEncoder::new();

    let expr = view(var("v"));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "View encoding should succeed: {:?}",
        result.as_ref().err()
    );

    // Verify v_view variable was created
    assert!(
        encoder.vars_for_test().contains_key("v_view"),
        "Should create v_view variable"
    );
}

/// Verify that a View used as a Seq method receiver gets Seq sort,
/// while a standalone View (numeric context) gets Int sort (#544).
#[test]
#[timeout(30000)]
fn test_view_sort_numeric_vs_collection() {
    // Numeric view: a@ != 0 where a: u8 — no Seq context, View should be Int
    let mut encoder_numeric = AYEncoder::new();
    let numeric_expr = ne(view(var("a")), int(0));
    let result = encoder_numeric.encode_pure(&numeric_expr);
    assert!(
        result.is_ok(),
        "Numeric view encoding should succeed: {result:?}"
    );
    assert!(
        encoder_numeric.vars_for_test().contains_key("a_view"),
        "Should create a_view variable"
    );
    // No Seq functions should be initialized for numeric views
    assert!(
        encoder_numeric.seq_state_for_test().funcs_is_none(),
        "Seq functions should NOT be initialized for numeric view"
    );

    // Collection view: v@.len() > 0 — Seq context from method call
    let mut encoder_seq = AYEncoder::new();
    let seq_expr = gt(method_call(view(var("v")), "len", vec![]), int(0));
    let result = encoder_seq.encode_pure(&seq_expr);
    assert!(
        result.is_ok(),
        "Seq view encoding should succeed: {result:?}"
    );
    assert!(
        encoder_seq.vars_for_test().contains_key("v_view"),
        "Should create v_view variable"
    );
    // Seq functions must be initialized for collection views
    assert!(
        encoder_seq.seq_state_for_test().funcs_is_some(),
        "Seq functions should be initialized for collection view"
    );
}

/// Verify equality propagation: (^self)@ == `self@.push_back(v)`
/// should mark `final_self_view` as Seq even though it's not a method receiver.
#[test]
#[timeout(30000)]
fn test_view_sort_equality_propagation() {
    let mut encoder = AYEncoder::new();

    // (^self)@ == self@.push_back(v)
    let final_view = view(final_expr(var("self")));
    let push_back = method_call(view(var("self")), "push_back", vec![var("v")]);
    let eq_expr = eq(final_view, push_back);

    let result = encoder.encode_pure(&eq_expr);
    assert!(
        result.is_ok(),
        "Equality with push_back should encode: {result:?}"
    );
    // Both self_view and final_self_view should exist as Seq variables
    assert!(
        encoder.vars_for_test().contains_key("self_view"),
        "equality propagation should create 'self_view'; found: {:?}",
        encoder.vars_for_test().keys().collect::<Vec<_>>()
    );
    assert!(
        encoder.vars_for_test().contains_key("final_self_view"),
        "equality propagation should create 'final_self_view'; found: {:?}",
        encoder.vars_for_test().keys().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_seq_len() {
    // Test seq.len() method call encoding and semantic non-negativity (#661).
    let mut encoder = AYEncoder::new();

    // v@.len()
    let expr = method_call(view(var("v")), "len", vec![]);

    let len_term = encoder
        .encode_pure(&expr)
        .expect("seq.len() encoding should succeed");

    // Seq functions must be initialized for len() calls
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "Seq functions should be initialized after encoding len()"
    );

    // Semantic: len(v@) >= 0 should hold (negation is UNSAT)
    let zero = encoder.solver.int_const(0);
    let len_lt_zero = encoder.solver.lt(len_term, zero);
    encoder.assert_term(len_lt_zero);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "len(v@) < 0 should be UNSAT (len is non-negative), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_seq_len_without_view() {
    // Without View wrapper or _view evidence, bare v.len() falls back to UF
    // dispatch (#756). Ambiguous Seq promotion requires corroborating _view
    // evidence to avoid breaking FMap dispatch (#994).
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("v"), "len", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "v.len() encoding should succeed: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "v.len() without _view evidence should not initialize Seq functions"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_old_seq_len_uses_prefixed_view() {
    // old(v@.len()) should use the prefixed view variable
    let mut encoder = AYEncoder::new();

    let expr = old(method_call(view(var("v")), "len", vec![]));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "old(v@.len()) encoding should succeed: {result:?}"
    );
    assert!(
        encoder.vars_for_test().contains_key("old_v_view"),
        "old(v@.len()) should create old_v_view"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_seq_len_on_old_view() {
    // old(v@).len() should use old_v_view without wrapping in a View
    let mut encoder = AYEncoder::new();

    // old(v@).len()
    let expr = method_call(old(view(var("v"))), "len", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "old(v@).len() encoding should succeed: {result:?}"
    );
    assert!(
        encoder.vars_for_test().contains_key("old_v_view"),
        "old(v@).len() should create old_v_view"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_seq_index_logic() {
    // Test seq.index_logic(i) returns a usable SMT term (#661).
    let mut encoder = AYEncoder::new();

    // v@.index_logic(0)
    let expr = method_call(view(var("v")), "index_logic", vec![int(0)]);

    let index_term = encoder
        .encode_pure(&expr)
        .expect("seq.index_logic() encoding should succeed");

    // Semantic: index_logic(0) can equal 42 (SAT — unconstrained sequence)
    let forty_two = encoder.solver.int_const(42);
    let eq_term = encoder.solver.eq(index_term, forty_two);
    encoder.assert_term(eq_term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "v@.index_logic(0) == 42 should be Sat (unconstrained seq), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_seq_index_on_old_view() {
    // old(v@).index_logic(i) should route through old_v_view.
    let mut encoder = AYEncoder::new();

    let expr = method_call(old(view(var("v"))), "index_logic", vec![int(0)]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "old(v@).index_logic(i) encoding should succeed: {result:?}"
    );
    assert!(
        encoder.vars_for_test().contains_key("old_v_view"),
        "old(v@).index_logic(i) should create old_v_view"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_seq_index_alias() {
    // Verify "index" produces the same SMT term as "index_logic" (#415, #661).
    // Encode both forms on separate encoders and check they behave identically:
    // if v@.index(0) == 42 is SAT, v@.index_logic(0) == 42 must also be SAT.
    let mut enc_alias = AYEncoder::new();
    let mut enc_logic = AYEncoder::new();

    let make_index = |method: &str| method_call(view(var("v")), method, vec![int(0)]);

    let alias_term = enc_alias
        .encode_pure(&make_index("index"))
        .expect("index alias should encode");
    let logic_term = enc_logic
        .encode_pure(&make_index("index_logic"))
        .expect("index_logic should encode");

    // Both should be SAT when constrained to the same value
    let val = enc_alias.solver.int_const(99);
    let eq_alias = enc_alias.solver.eq(alias_term, val);
    enc_alias.assert_term(eq_alias);
    let alias_result = enc_alias.check_sat();
    assert!(
        matches!(alias_result, SolveResult::Sat),
        "v@.index(0) == 99 should be Sat, got {alias_result:?}"
    );

    let val2 = enc_logic.solver.int_const(99);
    let eq_logic = enc_logic.solver.eq(logic_term, val2);
    enc_logic.assert_term(eq_logic);
    let logic_result = enc_logic.check_sat();
    assert!(
        matches!(logic_result, SolveResult::Sat),
        "v@.index_logic(0) == 99 should be Sat, got {logic_result:?}"
    );
}

// =============================================================================
// Seq push_back Tests
// =============================================================================

#[test]
#[timeout(30000)]
fn test_encode_seq_push_back() {
    // Test push_back initializes Seq funcs and satisfies len axiom (#661).
    let mut encoder = AYEncoder::new();

    // v@.push_back(42)
    let expr = method_call(view(var("v")), "push_back", vec![int(42)]);

    let _push_term = encoder
        .encode_pure(&expr)
        .expect("seq.push_back() encoding should succeed");

    // Seq functions must be initialized
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "Seq functions should be initialized after push_back"
    );

    // Semantic: len(push_back(v, 42)) == len(v) + 1 (UNSAT negation)
    let len_push = method_call(
        method_call(view(var("v")), "push_back", vec![int(42)]),
        "len",
        vec![],
    );
    let len_orig = method_call(view(var("v")), "len", vec![]);
    let len_plus_1 = add(len_orig, int(1));
    let eq_expr = eq(len_push, len_plus_1);

    // Use a fresh encoder to avoid variable conflicts
    let mut enc2 = AYEncoder::new();
    let formula = enc2
        .encode_pure(&eq_expr)
        .expect("axiom formula should encode");
    let neg = enc2.solver.not(formula);
    enc2.assert_term(neg);
    let result = enc2.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "len(push_back(v, 42)) != len(v) + 1 should be UNSAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_seq_push_back_on_old_view() {
    // old(v@).push_back(val) should use old_v_view as receiver
    let mut encoder = AYEncoder::new();

    // old(v@).push_back(42)
    let expr = method_call(old(view(var("v"))), "push_back", vec![int(42)]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "old(v@).push_back(val) encoding should succeed: {result:?}"
    );
    assert!(
        encoder.vars_for_test().contains_key("old_v_view"),
        "old(v@).push_back(val) should create old_v_view"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_seq_push_back_then_len() {
    // Verify push_back(v, 42).len() > v@.len() via UNSAT (#661).
    let mut encoder = AYEncoder::new();

    // v@.push_back(42).len()
    let push_then_len = method_call(
        method_call(view(var("v")), "push_back", vec![int(42)]),
        "len",
        vec![],
    );

    // v@.len()
    let v_len = method_call(view(var("v")), "len", vec![]);

    // push_back(v, 42).len() > v@.len()
    let gt_expr = gt(push_then_len, v_len);

    let formula = encoder
        .encode_pure(&gt_expr)
        .expect("chained expression should encode");

    // NOT(push_back(v, 42).len() > v@.len()) should be UNSAT
    let neg = encoder.solver.not(formula);
    encoder.assert_term(neg);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "push_back(v, 42).len() > v@.len() should always hold (UNSAT negation), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_seq_push_back_then_len_on_old_view() {
    // old(v@).push_back(val).len() should use old_v_view as receiver
    let mut encoder = AYEncoder::new();

    // old(v@).push_back(42).len()
    let expr = method_call(
        method_call(old(view(var("v"))), "push_back", vec![int(42)]),
        "len",
        vec![],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "old(v@).push_back(val).len() encoding should succeed: {result:?}"
    );
    assert!(
        encoder.vars_for_test().contains_key("old_v_view"),
        "old(v@).push_back(val).len() should create old_v_view"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_old_seq_push_back_then_len() {
    // old(v@.push_back(val).len()) should use the prefixed view variable
    let mut encoder = AYEncoder::new();

    let expr = old(method_call(
        method_call(view(var("v")), "push_back", vec![int(42)]),
        "len",
        vec![],
    ));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "old(v@.push_back(val).len()) encoding should succeed: {result:?}"
    );
    assert!(
        encoder.vars_for_test().contains_key("old_v_view"),
        "old(v@.push_back(val).len()) should create old_v_view"
    );
}
