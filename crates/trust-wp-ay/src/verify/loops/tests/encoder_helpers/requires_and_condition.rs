// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// ── encode_and_assert_requires coverage (#2133) ────────────────────

/// Normal requires (non-Skolemizable) are encoded and asserted.
/// After asserting `x >= 0` and its negation `x < 0`, the encoder
/// should be UNSAT (Verified), confirming both constraints were asserted.
#[test]
#[timeout(30000)]
fn encode_and_assert_requires_normal_precondition() {
    let mut encoder = setup_loop_encoder(&[i_ge_zero()], None, &[], &LoopEncoderConfig::default())
        .expect("encoder setup should succeed");

    // Assert x >= 0 as a precondition
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];

    encode_and_assert_requires(&mut encoder, &requires)
        .expect("encoding non-skolemizable requires should succeed");

    // Now assert the negation (x < 0) to confirm the require was added
    let neg_term = encoder
        .encode_pure(&PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Int(0)),
        ))
        .expect("encoding negation should succeed");
    encoder.assert_term(neg_term);

    // x >= 0 AND x < 0 is contradictory → UNSAT → Verified
    let result = resolve_sat_result_lightweight(&mut encoder);
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x >= 0 AND x < 0 should be UNSAT (Verified), got {result:?}"
    );
}

/// Empty requires should succeed without error.
#[test]
#[timeout(30000)]
fn encode_and_assert_requires_empty() {
    let mut encoder = setup_loop_encoder(&[i_ge_zero()], None, &[], &LoopEncoderConfig::default())
        .expect("encoder setup should succeed");

    encode_and_assert_requires(&mut encoder, &[]).expect("empty requires should succeed");
}

// ── encode_and_assert_condition coverage (#2133) ───────────────────

/// Loop condition is encoded and asserted as a constraint.
/// After asserting `i < n` and its negation `i >= n`, the encoder
/// should be UNSAT, confirming the condition was actually asserted.
#[test]
#[timeout(30000)]
fn encode_and_assert_condition_basic() {
    let mut encoder = setup_loop_encoder(
        &[i_ge_zero()],
        Some(&i_lt_n()),
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    encode_and_assert_condition(&mut encoder, &i_lt_n())
        .expect("encoding loop condition i < n should succeed");

    // Assert the negation (i >= n) to confirm condition was added
    let neg_term = encoder
        .encode_pure(&PureExpr::BinOp(
            Arc::new(i_var()),
            BinOp::Ge,
            Arc::new(n_var()),
        ))
        .expect("encoding negation should succeed");
    encoder.assert_term(neg_term);

    // i < n AND i >= n is contradictory → UNSAT → Verified
    let result = resolve_sat_result_lightweight(&mut encoder);
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "i < n AND i >= n should be UNSAT (Verified), got {result:?}"
    );
}

/// Asserting contradictory condition (false) should make encoder UNSAT.
#[test]
#[timeout(30000)]
fn encode_and_assert_condition_false_is_unsat() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    encode_and_assert_condition(&mut encoder, &PureExpr::Bool(false))
        .expect("encoding false condition should succeed");

    let result = resolve_sat_result_lightweight(&mut encoder);
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "asserting false should produce UNSAT (Verified), got {result:?}"
    );
}
