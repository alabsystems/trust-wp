// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
    BinOp, NamedBindingValue, PureExpr,
};

use crate::{
    verify_function_with_modes, verify_loop_invariant, AYEncoder, BodyEffects,
    LoopVerificationContext, LoopVerificationResult, UnknownReason, VerificationRequest,
    VerificationResult,
};

#[test]
#[timeout(30000)]
fn test_try_new_pure_constructor() {
    let mut encoder = AYEncoder::try_new_pure().expect("try_new_pure should create solver");
    // Empty assertion set should be SAT; this validates the fallible constructor path.
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "empty assertion set should be Sat"
    );
}

#[test]
#[timeout(30000)]
fn test_loop_overall_preserves_unknown_reason() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Unknown(UnknownReason::Timeout),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };

    match result.overall() {
        VerificationResult::Unknown(reason) => {
            assert_eq!(
                reason.as_str(),
                "timeout",
                "Unknown reason should be 'timeout'"
            );
        }
        other => panic!("Expected Unknown(timeout), got {other:?}"),
    }
}

/// Regression test for #739: loop initialization should use tuple axioms.
#[test]
#[timeout(30000)]
fn test_loop_initialization_with_tuple_invariant_axiom() {
    let tuple_ctor = PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(2),
        args: vec![
            PureExpr::Var("x".to_string(), None),
            PureExpr::Var("y".to_string(), None),
        ],
    };

    let inv = PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![PureExpr::Var("t".to_string(), None)],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Var("x".to_string(), None)),
    );

    let mut pre_loop = HashMap::new();
    pre_loop.insert("t".to_string(), NamedBindingValue::untyped(tuple_ctor));

    let empty_map = HashMap::new();
    let ctx = LoopVerificationContext::new(
        &[],
        &[],
        std::slice::from_ref(&inv),
        &[],
        BodyEffects::new(&empty_map, &empty_map, &empty_map),
        &pre_loop,
    );
    let result = verify_loop_invariant(&ctx).expect("tuple loop-initialization VC should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "tuple constructor/getter invariant should verify in loop initialization: got {:?}",
        result.initialization
    );
}

/// Verify that the builder API for `LoopVerificationContext` and
/// `LoopEncoderConfig` produces working verification contexts without
/// struct-literal construction. Adding new fields to the structs will not
/// require changes to call sites using this pattern (#891 AC4).
#[test]
#[timeout(30000)]
fn test_loop_context_builder_api_additive_evolution() {
    use crate::LoopEncoderConfig;

    let inv = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Int(10)),
    );
    let empty_map = HashMap::new();
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );
    let mut pre_loop = HashMap::new();
    pre_loop.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    // Build context using builder API — no struct-literal coupling.
    //
    // BUDGET (#133 mass unit adjudication, 2026-08-27): this test's own solver
    // budget was raised 5s -> 20s as a LOAD-FLAKE guard. The VC here is trivial
    // (`0 >= 0` initialization) and solves in 0.02s solo, measured 3/3 at this
    // pin; in-suite it was returning `Unknown(Timeout)` because a 5s wall-clock
    // deadline can expire while the solve is starved under full-suite
    // parallelism. This is an API-shape test, so the deadline was never the
    // property under test. 20s stays inside the 30s ntest budget above.
    let config = LoopEncoderConfig::default().with_timeout(std::time::Duration::from_secs(20));
    let ctx = LoopVerificationContext::new(
        &[],
        &[],
        std::slice::from_ref(&inv),
        &["i"],
        BodyEffects::new(&body_effect, &empty_map, &empty_map),
        &pre_loop,
    )
    .with_loop_condition(&cond)
    .with_config(config);

    let result = verify_loop_invariant(&ctx).expect("builder-API loop VC should encode");
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "initialization should verify via builder API: got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify via builder API: got {:?}",
        result.preservation
    );
}

// Vacuity guard regression tests (#2414).
// Encoder-level unit tests are in encoder::solver::vacuity_guard_tests.
// These are pipeline-level integration tests using only the public API.

/// Integration test: contradictory preconditions should cause the verification
/// pipeline to demote Verified -> Unknown("vacuous proof: ...") instead of
/// returning a false Verified. This is the #2404 bug class.
#[test]
#[timeout(30000)]
fn test_vacuity_guard_contradictory_preconditions_pipeline() {
    // requires: x > 0 AND x < 0 (contradictory)
    // ensures: false (would be "verified" without vacuity guard)
    let requires = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Int(0)),
        ),
    ];
    let ensures = vec![PureExpr::Bool(false)];

    let body = PureExpr::Int(0);
    let request = VerificationRequest::new(&requires, &ensures).return_expr(Some(&body));
    let result = verify_function_with_modes(request).expect("encoding should succeed");

    match &result {
        VerificationResult::Unknown(reason) => {
            let msg = reason.as_str();
            assert!(
                msg.contains("vacuous"),
                "Unknown reason should mention vacuity, got: {msg}"
            );
        }
        VerificationResult::Verified(_) => {
            panic!("contradictory preconditions should NOT produce Verified (#2404 bug class)");
        }
        other => {
            panic!("expected Unknown(vacuous), got: {other:?}");
        }
    }
}

/// Integration test: legitimate verification should still produce Verified.
#[test]
#[timeout(30000)]
fn test_vacuity_guard_legitimate_verification_still_passes() {
    // requires: x > 0
    // ensures: x > 0 (trivially true given precondition)
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];

    let request = VerificationRequest::new(&requires, &ensures);
    let result = verify_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "legitimate verification should still produce Verified, got: {result:?}"
    );
}

// ── Function-level vacuity diagnostic tests (#2663) ─────────────────
//
// These tests exercise the function verification pipeline with realistic
// patterns to verify the vacuity guard correctly distinguishes genuine
// from vacuous proofs. They complement the mut-borrow vacuity tests in
// verify/mut_borrow/tests.rs and the encoder-level vacuity tests in
// encoder/solver/vacuity_guard_tests.rs.

/// Model of simple increment: `requires(x >= 0), ensures(result > x)`, body `x + 1`.
/// This is a straightforward provable postcondition — must NOT be vacuous.
#[test]
#[timeout(30000)]
fn test_vacuity_function_simple_increment_non_vacuous() {
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Var("x".to_string(), None)),
    )];
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    let request = VerificationRequest::new(&requires, &ensures).return_expr(Some(&body));
    let result = verify_function_with_modes(request).expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "simple increment should NOT produce a vacuous proof — base assertions are consistent. \
         Got: {result:?}"
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x + 1 > x should verify with requires(x >= 0). Got: {result:?}"
    );
}

/// Model of identity postcondition: `ensures(result == x)`, body `x`.
/// Trivially provable, must NOT be vacuous.
#[test]
#[timeout(30000)]
fn test_vacuity_function_identity_non_vacuous() {
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("x".to_string(), None)),
    )];
    let body = PureExpr::Var("x".to_string(), None);

    let request = VerificationRequest::new(&[], &ensures).return_expr(Some(&body));
    let result = verify_function_with_modes(request).expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "identity postcondition should NOT produce a vacuous proof. Got: {result:?}"
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "result == x with body x should verify. Got: {result:?}"
    );
}

/// Falsifiable postcondition: `requires(x > 0), ensures(result < 0)`, body `x`.
/// result = x > 0, but ensures says result < 0. Should FAIL, not be vacuously verified.
#[test]
#[timeout(30000)]
fn test_vacuity_function_falsifiable_postcondition_fails() {
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Int(0)),
    )];
    let body = PureExpr::Var("x".to_string(), None);

    let request = VerificationRequest::new(&requires, &ensures).return_expr(Some(&body));
    let result = verify_function_with_modes(request).expect("encoding should succeed");

    // Must fail — postcondition is false for x > 0.
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "falsifiable postcondition (x > 0 but ensures result < 0) must fail. Got: {result:?}"
    );
}

/// Multiple ensures clauses, all provable: each should verify non-vacuously.
/// `requires(x > 0), ensures(result > 0), ensures(result == x + 1)`, body `x + 1`.
#[test]
#[timeout(30000)]
fn test_vacuity_function_multiple_ensures_all_provable() {
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        ),
    ];
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    let request = VerificationRequest::new(&requires, &ensures).return_expr(Some(&body));
    let result = verify_function_with_modes(request).expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "multiple provable ensures should not be vacuous. Got: {result:?}"
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "all ensures clauses should verify with body x + 1. Got: {result:?}"
    );
}

/// Weakly contradictory precondition via `false` literal: should be caught as vacuous.
#[test]
#[timeout(30000)]
fn test_vacuity_function_false_precondition_is_vacuous() {
    // requires: false (explicitly contradictory)
    // ensures: result == 42 (any nonsensical postcondition)
    let requires = vec![PureExpr::Bool(false)];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    )];

    let request = VerificationRequest::new(&requires, &ensures);
    let result = verify_function_with_modes(request).expect("encoding should succeed");

    match &result {
        VerificationResult::Unknown(reason) if reason.as_str().contains("vacuous") => {}
        other => panic!("false precondition should produce Unknown(vacuous), got: {other:?}"),
    }
}

/// Subtly contradictory preconditions via impossible bounds.
/// `requires(x == 5), requires(x == 7)` — contradictory.
/// Any ensures should be detected as vacuous.
#[test]
#[timeout(30000)]
fn test_vacuity_function_subtly_contradictory_equality_preconditions() {
    let requires = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(5)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(7)),
        ),
    ];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    )];

    let request = VerificationRequest::new(&requires, &ensures);
    let result = verify_function_with_modes(request).expect("encoding should succeed");

    match &result {
        VerificationResult::Unknown(reason) if reason.as_str().contains("vacuous") => {}
        other => panic!(
            "contradictory equalities (x==5 ∧ x==7) should produce Unknown(vacuous), got: {other:?}"
        ),
    }
}
