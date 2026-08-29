// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `encoder/seq_synth.rs` (#1946 Phase 3).
//!
//! Coverage targets:
//! - `try_synthesize_len_zero_seq_value`: detects `View(Var("x")).len() == 0`
//!   and creates concrete empty SeqValue
//! - `try_reconstruct_flat_push_back_chain`: detects flat push_back assumptions
//!   and builds chained SeqValue
//! - `try_synthesize_index_mut_seq_value`: detects IndexMut point-write pattern
//!   and creates SeqValue with Array store
//! - `extract_index_mut_pattern`: pattern extraction for IndexMut detection
//!
//! The len-zero and push-back chain tests require a properly initialized encoder
//! with sort hints registered before synthesis, matching the production pipeline
//! in `verify/setup.rs`.

use ntest::timeout;

use super::*;

/// Helper: set up encoder with sort hints and encode all requirements.
/// This mirrors the production pipeline in `verify/setup.rs`.
fn setup_encoder_with_requires(requires: &[PureExpr]) -> AYEncoder {
    let mut encoder = AYEncoder::new();
    encoder.register_sort_hints(requires);
    for req in requires {
        let term = encoder.encode_pure(req).expect("encode req");
        encoder.assert_term(term);
    }
    encoder
}

// ── try_synthesize_len_zero_seq_value tests ──────────────────────────

/// `View(Var("x")).len() == 0` should create a concrete empty SeqValue for x_view.
#[test]
#[timeout(30000)]
fn test_len_zero_synthesis_creates_seq_value() {
    let len_zero = eq(method_call(view(var("x")), "len", vec![]), int(0));
    let mut encoder = setup_encoder_with_requires(std::slice::from_ref(&len_zero));

    encoder
        .try_synthesize_len_zero_seq_value(&len_zero, None)
        .expect("len zero synthesis should succeed");

    // Verify that x_view now has a registered SeqValue.
    let x_view_term = *encoder
        .vars_for_test()
        .get("x_view")
        .expect("x_view should be registered");
    assert!(
        encoder.seq_state_for_test().has_seq_value(&x_view_term),
        "x_view should have a SeqValue after len-zero synthesis"
    );
}

/// Reversed orientation `0 == View(Var("x")).len()` should also trigger synthesis.
#[test]
#[timeout(30000)]
fn test_len_zero_synthesis_reversed_orientation() {
    let len_zero = eq(int(0), method_call(view(var("x")), "len", vec![]));
    let mut encoder = setup_encoder_with_requires(std::slice::from_ref(&len_zero));

    encoder
        .try_synthesize_len_zero_seq_value(&len_zero, None)
        .expect("reversed len zero synthesis should succeed");

    let x_view_term = *encoder.vars_for_test().get("x_view").unwrap();
    assert!(
        encoder.seq_state_for_test().has_seq_value(&x_view_term),
        "x_view should have a SeqValue with reversed orientation"
    );
}

/// Bare Seq carriers from proof_assert facts should also seed empty SeqValues.
#[test]
#[timeout(30000)]
fn test_len_zero_synthesis_bare_seq_carrier() {
    let len_zero = eq(method_call(var("x"), "len", vec![]), int(0));
    let mut encoder = setup_encoder_with_requires(std::slice::from_ref(&len_zero));

    encoder
        .try_synthesize_len_zero_seq_value(&len_zero, None)
        .expect("bare len zero synthesis should succeed");

    assert_eq!(
        encoder.var_sort("x"),
        Some(&ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int)),
        "bare Seq carrier should be rebound onto the Seq sort before synthesis"
    );

    let x_term = *encoder
        .vars_for_test()
        .get("x")
        .expect("x should be registered");
    assert!(
        encoder.seq_state_for_test().has_seq_value(&x_term),
        "bare Seq carrier should get a SeqValue after len-zero synthesis"
    );
}

/// Non-len-zero expressions should be no-ops.
#[test]
#[timeout(30000)]
fn test_len_zero_synthesis_non_matching_is_noop() {
    let len_zero = eq(method_call(view(var("x")), "len", vec![]), int(0));
    let mut encoder = setup_encoder_with_requires(&[len_zero]);
    let x_view_term = *encoder.vars_for_test().get("x_view").unwrap();
    let had_seq_value = encoder.seq_state_for_test().has_seq_value(&x_view_term);

    // Not a len==0 pattern: x > 0
    let non_matching = gt(var("x"), int(0));
    encoder
        .try_synthesize_len_zero_seq_value(&non_matching, None)
        .expect("non-matching should succeed without error");

    assert_eq!(
        encoder.seq_state_for_test().has_seq_value(&x_view_term),
        had_seq_value,
        "non-matching expr should not change SeqValue synthesis state"
    );
}

/// View(Final(...)) receiver should NOT trigger len-zero synthesis.
#[test]
#[timeout(30000)]
fn test_len_zero_synthesis_final_receiver_skipped() {
    let expr = eq(
        method_call(view(final_expr(var("x"))), "len", vec![]),
        int(0),
    );
    let mut encoder = setup_encoder_with_requires(std::slice::from_ref(&expr));
    let before = encoder
        .vars_for_test()
        .get("final_x_view")
        .copied()
        .map(|term| encoder.seq_state_for_test().has_seq_value(&term));

    encoder
        .try_synthesize_len_zero_seq_value(&expr, None)
        .expect("final receiver should succeed but be a no-op");

    // View(Final) should not change synthesis state; setup may have already
    // created state for this diagnostic under latest ay.
    if let Some(&fxv_term) = encoder.vars_for_test().get("final_x_view") {
        assert_eq!(
            Some(encoder.seq_state_for_test().has_seq_value(&fxv_term)),
            before,
            "View(Final) should not change SeqValue synthesis state"
        );
    }
}

/// Already-registered SeqValue should not be overwritten.
#[test]
#[timeout(30000)]
fn test_len_zero_synthesis_no_overwrite() {
    let len_zero = eq(method_call(view(var("x")), "len", vec![]), int(0));
    let mut encoder = setup_encoder_with_requires(std::slice::from_ref(&len_zero));

    // Synthesize once.
    encoder
        .try_synthesize_len_zero_seq_value(&len_zero, None)
        .unwrap();

    let x_view_term = *encoder.vars_for_test().get("x_view").unwrap();
    assert!(
        encoder.seq_state_for_test().has_seq_value(&x_view_term),
        "first synthesis should create SeqValue"
    );

    let count_before = encoder.seq_state_for_test().seq_values_len();

    // Synthesize again — should be a no-op (early return due to contains_key guard).
    encoder
        .try_synthesize_len_zero_seq_value(&len_zero, None)
        .unwrap();

    assert_eq!(
        encoder.seq_state_for_test().seq_values_len(),
        count_before,
        "second synthesis should not add a new SeqValue entry"
    );
}

// ── try_reconstruct_flat_push_back_chain tests ──────────────────────

/// Flat push_back chain with len==0 base and 2+ pushes should create chained SeqValue.
#[test]
#[timeout(30000)]
fn test_flat_push_back_chain_basic() {
    let all_requires = vec![
        eq(method_call(view(var("x")), "len", vec![]), int(0)),
        eq(
            view(final_expr(var("x"))),
            method_call(view(var("x")), "push_back", vec![int(10)]),
        ),
        eq(
            view(final_expr(var("x"))),
            method_call(view(var("x")), "push_back", vec![int(20)]),
        ),
    ];

    let mut encoder = setup_encoder_with_requires(&all_requires);

    // Synthesize len-zero base first (required for chain reconstruction).
    for req in &all_requires {
        encoder
            .try_synthesize_len_zero_seq_value(req, None)
            .expect("len-zero synthesis should succeed");
    }

    encoder
        .try_reconstruct_flat_push_back_chain(&all_requires, None)
        .expect("flat push_back chain reconstruction should succeed");

    // Verify final_x_view has a SeqValue now.
    let fxv_term = *encoder
        .vars_for_test()
        .get("final_x_view")
        .expect("final_x_view should be registered");
    assert!(
        encoder.seq_state_for_test().has_seq_value(&fxv_term),
        "final_x_view should have a SeqValue after chain reconstruction"
    );
}

/// Bare proof_assert-style Seq carriers should also reconstruct a chained
/// post-state SeqValue.
#[test]
#[timeout(30000)]
fn test_flat_push_back_chain_basic_bare_seq_carriers() {
    let all_requires = vec![
        eq(method_call(var("x"), "len", vec![]), int(0)),
        eq(
            final_expr(var("x")),
            method_call(var("x"), "push_back", vec![int(10)]),
        ),
        eq(
            final_expr(var("x")),
            method_call(var("x"), "push_back", vec![int(20)]),
        ),
    ];

    let mut encoder = setup_encoder_with_requires(&all_requires);

    for req in &all_requires {
        encoder
            .try_synthesize_len_zero_seq_value(req, None)
            .expect("bare len-zero synthesis should succeed");
    }

    encoder
        .try_reconstruct_flat_push_back_chain(&all_requires, None)
        .expect("bare flat push_back chain reconstruction should succeed");

    let x_final_term = *encoder
        .vars_for_test()
        .get("x_final")
        .expect("x_final should be registered");
    assert!(
        encoder.seq_state_for_test().has_seq_value(&x_final_term),
        "x_final should have a SeqValue after bare chain reconstruction"
    );
}

/// Single push_back (< 2 values) should NOT trigger chain reconstruction.
/// Note: `setup_encoder_with_requires` calls `encode_pure` which may create a
/// SeqValue for `final_x_view` as part of normal push_back encoding. We verify
/// that `try_reconstruct_flat_push_back_chain` does NOT add a *new* entry
/// (i.e., the seq_values count is unchanged), confirming the < 2 guard works.
#[test]
#[timeout(30000)]
fn test_flat_push_back_chain_single_push_no_chain() {
    let all_requires = vec![
        eq(method_call(view(var("x")), "len", vec![]), int(0)),
        eq(
            view(final_expr(var("x"))),
            method_call(view(var("x")), "push_back", vec![int(10)]),
        ),
    ];

    let mut encoder = setup_encoder_with_requires(&all_requires);

    for req in &all_requires {
        encoder
            .try_synthesize_len_zero_seq_value(req, None)
            .unwrap();
    }

    let count_before = encoder.seq_state_for_test().seq_values_len();

    encoder
        .try_reconstruct_flat_push_back_chain(&all_requires, None)
        .unwrap();

    // Chain reconstruction should be a no-op for a single push_back (< 2 guard).
    assert_eq!(
        encoder.seq_state_for_test().seq_values_len(),
        count_before,
        "single push_back should not trigger chain reconstruction (count unchanged)"
    );
}

/// No len==0 base means chain reconstruction should skip.
/// Same approach: verify seq_values count is unchanged after the call.
#[test]
#[timeout(30000)]
fn test_flat_push_back_chain_no_len_zero_base_skips() {
    let all_requires = vec![
        eq(
            view(final_expr(var("x"))),
            method_call(view(var("x")), "push_back", vec![int(10)]),
        ),
        eq(
            view(final_expr(var("x"))),
            method_call(view(var("x")), "push_back", vec![int(20)]),
        ),
    ];

    let mut encoder = setup_encoder_with_requires(&all_requires);

    let count_before = encoder.seq_state_for_test().seq_values_len();

    // No len_zero synthesis — the chain should skip because base has no len==0.
    encoder
        .try_reconstruct_flat_push_back_chain(&all_requires, None)
        .unwrap();

    assert_eq!(
        encoder.seq_state_for_test().seq_values_len(),
        count_before,
        "no len-zero base should not add new SeqValue entries via chain reconstruction"
    );
}

// ── extract_index_mut_pattern tests ─────────────────────────────────

/// Form 1: MethodCall { receiver: View(Final(Var("a"))), method: "index_logic", args: [idx] }
#[test]
#[timeout(30000)]
fn test_extract_index_mut_pattern_form1() {
    let index_side = method_call(view(final_expr(var("a"))), "index_logic", vec![int(2)]);
    let value_side = int(42);

    let result = AYEncoder::extract_index_mut_pattern(&index_side, &value_side, None);
    assert!(result.is_some(), "Form 1 index_logic pattern should match");
    let (target_name, _idx, _val) = result.unwrap();
    assert_eq!(target_name, "final_a_view");
}

/// Form 1 also works with "index" method name.
#[test]
#[timeout(30000)]
fn test_extract_index_mut_pattern_index_method() {
    let index_side = method_call(view(final_expr(var("a"))), "index", vec![int(0)]);
    let value_side = int(99);

    let result = AYEncoder::extract_index_mut_pattern(&index_side, &value_side, None);
    assert!(result.is_some(), "index method name should also match");
}

/// Non-Final receiver should NOT match.
#[test]
#[timeout(30000)]
fn test_extract_index_mut_pattern_non_final_returns_none() {
    let index_side = method_call(view(var("a")), "index_logic", vec![int(0)]);
    let value_side = int(42);

    let result = AYEncoder::extract_index_mut_pattern(&index_side, &value_side, None);
    assert!(
        result.is_none(),
        "View(Var) (non-Final) should not match index_mut pattern"
    );
}

/// Wrong method name should NOT match.
#[test]
#[timeout(30000)]
fn test_extract_index_mut_pattern_wrong_method_returns_none() {
    let index_side = method_call(view(final_expr(var("a"))), "len", vec![]);
    let value_side = int(42);

    let result = AYEncoder::extract_index_mut_pattern(&index_side, &value_side, None);
    assert!(
        result.is_none(),
        "len method should not match index_mut pattern"
    );
}

/// Form 2: View(MethodCall { receiver: Final(Var("a")), method: "index_logic" })
#[test]
#[timeout(30000)]
fn test_extract_index_mut_pattern_form2() {
    let inner = method_call(final_expr(var("a")), "index_logic", vec![int(3)]);
    let index_side = view(inner);
    let value_side = int(100);

    let result = AYEncoder::extract_index_mut_pattern(&index_side, &value_side, None);
    assert!(result.is_some(), "Form 2 View(MethodCall) should match");
    let (target_name, _idx, _val) = result.unwrap();
    assert_eq!(target_name, "final_a_view");
}

/// Wrong arity (2 args) should NOT match.
#[test]
#[timeout(30000)]
fn test_extract_index_mut_pattern_wrong_arity_returns_none() {
    let index_side = method_call(
        view(final_expr(var("a"))),
        "index_logic",
        vec![int(0), int(1)],
    );
    let value_side = int(42);

    let result = AYEncoder::extract_index_mut_pattern(&index_side, &value_side, None);
    assert!(
        result.is_none(),
        "2-arg index_logic should not match (expected 1 arg)"
    );
}

/// Form 2 with non-Final receiver should NOT match.
#[test]
#[timeout(30000)]
fn test_extract_index_mut_pattern_form2_non_final_returns_none() {
    let inner = method_call(var("a"), "index_logic", vec![int(0)]);
    let index_side = view(inner);
    let value_side = int(42);

    let result = AYEncoder::extract_index_mut_pattern(&index_side, &value_side, None);
    assert!(
        result.is_none(),
        "Form 2 with non-Final receiver should not match"
    );
}

/// Non-View, non-MethodCall expressions should return None.
#[test]
#[timeout(30000)]
fn test_extract_index_mut_pattern_leaf_returns_none() {
    let a = var("a");
    let val = int(42);
    let result = AYEncoder::extract_index_mut_pattern(&a, &val, None);
    assert!(result.is_none(), "plain Var should not match");

    let zero = int(0);
    let val2 = int(42);
    let result = AYEncoder::extract_index_mut_pattern(&zero, &val2, None);
    assert!(result.is_none(), "Int should not match");
}
