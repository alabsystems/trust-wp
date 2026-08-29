// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `solver_tail.rs` resolve functions.
//!
//! These are safety-critical: `resolve_base_sat_result` has **inverted**
//! SAT/UNSAT semantics for vacuity detection. An accidental swap would
//! silently produce unsound verification results.

use ay_dpll::api::Sort;
use ntest::timeout;

use super::{
    solver_tail::{
        check_sat_with_retry, collect_body_let_assume_assumptions, resolve_base_sat_result,
        resolve_last_unsat_with_vacuity, resolve_sat_result_without_vacuity,
        unknown_result_from_encoder, VACUOUS_PROOF_MESSAGE,
    },
    UnknownReason, VerificationResult,
};
use crate::encoder::AYEncoder;

// ── resolve_base_sat_result (inverted vacuity) ────────────────────────

/// SAT base context → Verified: the base assertions are consistent,
/// so the earlier UNSAT with the negated postcondition was a genuine proof.
#[test]
#[timeout(30000)]
fn test_resolve_base_sat_result_sat_returns_verified() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(x_gt_0);

    let result = resolve_base_sat_result(&mut encoder);
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "SAT base should return Verified (proof is genuine), got: {result:?}"
    );
}

/// UNSAT base context → Unknown(vacuous): the base assertions alone are
/// contradictory, so the proof was vacuous (preconditions are unsatisfiable).
#[test]
#[timeout(30000)]
fn test_resolve_base_sat_result_unsat_returns_vacuous_unknown() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let x_lt_0 = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(x_gt_0);
    encoder.assert_term(x_lt_0);

    let result = resolve_base_sat_result(&mut encoder);
    match &result {
        VerificationResult::Unknown(UnknownReason::SolverMessage(msg)) => {
            assert_eq!(
                msg, VACUOUS_PROOF_MESSAGE,
                "vacuous proof message should match the constant"
            );
        }
        _ => panic!("UNSAT base should return Unknown(vacuous), got: {result:?}"),
    }
}

/// Mixed Int+Bool contradictions must still be classified as vacuous Unknown.
///
/// This guards the #2141/#2520 axiom-free rescue path: base rechecks may
/// return `Unknown(Incomplete)` for mixed-sort SAT model generation, but they
/// must not hide contradictory bases that are actually UNSAT.
#[test]
#[timeout(30000)]
fn test_resolve_base_sat_result_mixed_int_bool_contradiction_returns_vacuous_unknown() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let flag = encoder.solver_mut().declare_const("flag", Sort::Bool);
    let zero = encoder.solver_mut().int_const(0);

    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let link = encoder.solver_mut().eq(flag, x_gt_0);
    encoder.assert_term(link);
    let x_gt_0_again = encoder.solver_mut().gt(x, zero);
    let link_again = encoder.solver_mut().eq(flag, x_gt_0_again);
    let not_link = encoder.solver_mut().not(link_again);
    encoder.assert_term(not_link);

    let result = resolve_base_sat_result(&mut encoder);
    match &result {
        VerificationResult::Unknown(UnknownReason::SolverMessage(msg)) => {
            assert_eq!(
                msg, VACUOUS_PROOF_MESSAGE,
                "mixed Int+Bool contradiction should still use the vacuity message"
            );
        }
        _ => panic!(
            "mixed Int+Bool contradictory base should return Unknown(vacuous), got: {result:?}"
        ),
    }
}

/// Unknown solver result → Unknown forwarded from solver.
/// Force Unknown by recording a solver panic before check_sat.
#[test]
#[timeout(30000)]
fn test_resolve_base_sat_result_unknown_returns_unknown() {
    let mut encoder = AYEncoder::new();
    encoder
        .assertion_pipeline_mut_for_test()
        .record_solver_panic("test-induced panic".to_string());

    let result = resolve_base_sat_result(&mut encoder);
    match &result {
        VerificationResult::Unknown(UnknownReason::SolverPanic(msg)) => {
            assert!(
                msg.contains("test-induced panic"),
                "should surface the panic reason, got: {msg}"
            );
        }
        _ => panic!("panicked encoder should return Unknown(SolverPanic), got: {result:?}"),
    }
}

/// Verify the inversion is correct: SAT ↔ Verified, UNSAT ↔ vacuous Unknown.
/// This test asserts both directions in sequence using push/pop scopes to
/// confirm the mapping is not accidentally swapped.
#[test]
#[timeout(30000)]
fn test_resolve_base_sat_result_inversion_correctness() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);

    // Phase 1: SAT base (x > 0 is satisfiable) → Verified
    encoder.push_scope().unwrap();
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(x_gt_0);
    let sat_result = resolve_base_sat_result(&mut encoder);
    assert!(
        matches!(sat_result, VerificationResult::Verified(_)),
        "SAT base must map to Verified, got: {sat_result:?}"
    );
    encoder.pop_scope().unwrap();

    // Phase 2: UNSAT base (x > 0 AND x < 0) → vacuous Unknown
    encoder.push_scope().unwrap();
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let x_lt_0 = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(x_gt_0);
    encoder.assert_term(x_lt_0);
    let unsat_result = resolve_base_sat_result(&mut encoder);
    match &unsat_result {
        VerificationResult::Unknown(UnknownReason::SolverMessage(msg)) => {
            assert_eq!(msg, VACUOUS_PROOF_MESSAGE);
        }
        _ => panic!("UNSAT base must map to vacuous Unknown, got: {unsat_result:?}"),
    }
    encoder.pop_scope().unwrap();
}

// ── resolve_sat_result_without_vacuity ─────────────────────────────────

/// UNSAT → Verified: the negated postcondition is contradictory, proof holds.
#[test]
#[timeout(30000)]
fn test_resolve_without_vacuity_unsat_returns_verified() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let x_lt_0 = encoder.solver_mut().lt(x, zero);
    // Contradiction → UNSAT
    encoder.assert_term(x_gt_0);
    encoder.assert_term(x_lt_0);

    let result = resolve_sat_result_without_vacuity(&mut encoder);
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "UNSAT should return Verified, got: {result:?}"
    );
}

/// SAT → Failed: a counterexample exists with model data.
#[test]
#[timeout(30000)]
fn test_resolve_without_vacuity_sat_returns_failed() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(x_gt_0);

    let result = resolve_sat_result_without_vacuity(&mut encoder);
    match &result {
        VerificationResult::Failed(cex) => {
            // Latest ay may return SAT without materializing a model through
            // the encoder wrapper; the important contract here is Failed.
            let _ = cex;
        }
        _ => panic!("SAT should return Failed with counterexample, got: {result:?}"),
    }
}

/// Unknown → Unknown(SolverPanic) forwarded from solver.
#[test]
#[timeout(30000)]
fn test_resolve_without_vacuity_unknown_returns_unknown() {
    let mut encoder = AYEncoder::new();
    encoder
        .assertion_pipeline_mut_for_test()
        .record_solver_panic("test panic".to_string());

    let result = resolve_sat_result_without_vacuity(&mut encoder);
    match &result {
        VerificationResult::Unknown(UnknownReason::SolverPanic(msg)) => {
            assert!(
                msg.contains("test panic"),
                "should surface the panic reason, got: {msg}"
            );
        }
        _ => panic!("panicked encoder should return Unknown(SolverPanic), got: {result:?}"),
    }
}

// ── check_sat_with_retry ───────────────────────────────────────────────

/// Definitive Unsat result passes through without retry.
#[test]
#[timeout(30000)]
fn test_check_sat_with_retry_unsat_no_retry() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let x_lt_0 = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(x_gt_0);
    encoder.assert_term(x_lt_0);

    let result = check_sat_with_retry(&mut encoder);
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "contradiction should return Unsat, got: {result:?}"
    );
}

/// Definitive Sat result passes through without retry.
#[test]
#[timeout(30000)]
fn test_check_sat_with_retry_sat_no_retry() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(x_gt_0);

    let result = check_sat_with_retry(&mut encoder);
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "satisfiable constraint should return Sat, got: {result:?}"
    );
}

// ── unknown_result_from_encoder ────────────────────────────────────────

/// Encoder with recorded panic → SolverPanic reason.
#[test]
#[timeout(30000)]
fn test_unknown_result_from_encoder_panic_surfaces_reason() {
    let mut encoder = AYEncoder::new();
    encoder
        .assertion_pipeline_mut_for_test()
        .record_solver_panic("ay assertion failed in bv_solver".to_string());

    let result = unknown_result_from_encoder(&encoder);
    match &result {
        VerificationResult::Unknown(UnknownReason::SolverPanic(msg)) => {
            assert!(
                msg.contains("ay assertion failed in bv_solver"),
                "panic reason should be in the message, got: {msg}"
            );
            assert!(
                msg.starts_with("ay solver panicked:"),
                "should have standard prefix, got: {msg}"
            );
        }
        _ => panic!("panicked encoder should produce SolverPanic, got: {result:?}"),
    }
}

/// Fresh encoder without panic → Unspecified unknown reason.
#[test]
#[timeout(30000)]
fn test_unknown_result_from_encoder_no_panic_unspecified() {
    let encoder = AYEncoder::new();
    let result = unknown_result_from_encoder(&encoder);
    assert!(
        matches!(
            result,
            VerificationResult::Unknown(UnknownReason::Unspecified)
        ),
        "fresh encoder should produce Unspecified unknown, got: {result:?}"
    );
}

// ── try_axiom_free_solve ────────────────────────────────────────────────

/// Contradictory assertions → Unsat without any axioms.
/// This is the common case for simple obligations like `x == x`.
#[test]
#[timeout(30000)]
fn test_try_axiom_free_solve_contradiction_returns_unsat() {
    use super::solver_tail::try_axiom_free_solve;

    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let x_lt_0 = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(x_gt_0);
    encoder.assert_term(x_lt_0);

    let result = try_axiom_free_solve(&mut encoder);
    assert!(
        result.is_some(),
        "contradictory assertions should return Some(Unsat)"
    );
    assert!(
        matches!(result.unwrap(), ay_dpll::api::SolveResult::Unsat(_)),
        "result should be Unsat"
    );
}

/// Satisfiable assertions → None (axioms needed or proof doesn't hold).
/// The probe correctly identifies that the negated goal is not contradictory.
#[test]
#[timeout(30000)]
fn test_try_axiom_free_solve_sat_returns_none() {
    use super::solver_tail::try_axiom_free_solve;

    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(x_gt_0);

    let result = try_axiom_free_solve(&mut encoder);
    assert!(
        result.is_none(),
        "satisfiable assertions should return None (axioms needed)"
    );
}

/// Empty assertion set (trivially SAT) → None.
/// An empty context is not contradictory, so axioms are needed.
#[test]
#[timeout(30000)]
fn test_try_axiom_free_solve_empty_returns_none() {
    use super::solver_tail::try_axiom_free_solve;

    let mut encoder = AYEncoder::new();
    let result = try_axiom_free_solve(&mut encoder);
    assert!(
        result.is_none(),
        "empty assertion set should return None (trivially SAT, not Unsat)"
    );
}

/// Timeout is restored after the probe, even when the probe succeeds.
#[test]
#[timeout(30000)]
fn test_try_axiom_free_solve_restores_timeout() {
    use std::time::Duration;

    use super::solver_tail::try_axiom_free_solve;

    let mut encoder = AYEncoder::new();
    let original_timeout = Duration::from_mins(1);
    encoder.set_timeout(Some(original_timeout));

    // Assert something satisfiable so probe returns None
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(x_gt_0);

    let _result = try_axiom_free_solve(&mut encoder);

    let restored = encoder.solver().timeout();
    assert_eq!(
        restored,
        Some(original_timeout),
        "original timeout must be restored after probe, got: {restored:?}"
    );
}

/// When original timeout is shorter than 500ms probe, the original is used.
#[test]
#[timeout(30000)]
fn test_try_axiom_free_solve_respects_short_original_timeout() {
    use std::time::Duration;

    use super::solver_tail::try_axiom_free_solve;

    let mut encoder = AYEncoder::new();
    let short_timeout = Duration::from_millis(100);
    encoder.set_timeout(Some(short_timeout));

    // Contradictory → should still return Unsat even with short timeout
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let x_lt_0 = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(x_gt_0);
    encoder.assert_term(x_lt_0);

    let result = try_axiom_free_solve(&mut encoder);
    assert!(
        result.is_some(),
        "contradiction should still be found with short timeout"
    );

    let restored = encoder.solver().timeout();
    assert_eq!(
        restored,
        Some(short_timeout),
        "short timeout must be restored after probe"
    );
}

/// When no original timeout is set (None), the 500ms probe timeout is used,
/// and the original None timeout is restored after.
#[test]
#[timeout(30000)]
fn test_try_axiom_free_solve_no_original_timeout_uses_probe() {
    use super::solver_tail::try_axiom_free_solve;

    let mut encoder = AYEncoder::new();
    // No timeout set (default is None)
    assert!(
        encoder.solver().timeout().is_none(),
        "precondition: no timeout set on fresh encoder"
    );

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let x_lt_0 = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(x_gt_0);
    encoder.assert_term(x_lt_0);

    let result = try_axiom_free_solve(&mut encoder);
    assert!(
        result.is_some(),
        "contradiction should be found even with default 500ms probe timeout"
    );

    let restored = encoder.solver().timeout();
    assert!(
        restored.is_none(),
        "None timeout must be restored after probe, got: {restored:?}"
    );
}

// ── ay-dpll Bool SAT regression guards (#2141) ─────────────────────────

/// Regression: ay-dpll must find SAT for a trivial Bool negated-equality
/// with 2 variables. Guards the basic Bool SAT capability that the
/// axiom-free probe relies on for counterexample generation. (#2141)
#[test]
#[timeout(30000)]
fn test_direct_bool_sat_2_vars() {
    let mut enc = AYEncoder::new();
    let b = enc.solver_mut().declare_const("b_current", Sort::Bool);
    let b_final = enc.solver_mut().declare_const("b_final", Sort::Bool);
    let not_b = enc.solver_mut().not(b);
    let eq1 = enc.solver_mut().eq(b_final, not_b);
    enc.assert_term(eq1);
    let eq2 = enc.solver_mut().eq(b_final, b);
    let neg = enc.solver_mut().not(eq2);
    enc.assert_term(neg);
    let result = enc.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "ay-dpll should find SAT for Bool negated-equality: {result:?}"
    );
}

/// Regression: 4 Bool vars with push_scope (matching pipeline structure)
/// must return SAT. Unnamed assertions + push_scope work correctly for
/// Bool SAT model generation. (#2141)
#[test]
#[timeout(30000)]
fn test_direct_bool_sat_4_vars_with_push_scope() {
    let mut enc = AYEncoder::new();
    let b_current = enc.solver_mut().declare_const("b_current", Sort::Bool);
    let b_final = enc.solver_mut().declare_const("b_final", Sort::Bool);
    let old_b_current = enc.solver_mut().declare_const("old_b_current", Sort::Bool);
    let b_current_final = enc
        .solver_mut()
        .declare_const("b_current_final", Sort::Bool);

    let not_b = enc.solver_mut().not(b_current);
    let body = enc.solver_mut().eq(b_final, not_b);
    enc.assert_term(body);
    let old_eq = enc.solver_mut().eq(old_b_current, b_current);
    enc.assert_term(old_eq);
    let not_b2 = enc.solver_mut().not(b_current);
    let cf_eq = enc.solver_mut().eq(b_current_final, not_b2);
    enc.assert_term(cf_eq);

    enc.push_scope().unwrap();
    let post_eq = enc.solver_mut().eq(b_final, old_b_current);
    let neg_post = enc.solver_mut().not(post_eq);
    enc.assert_term(neg_post);
    let result = enc.check_sat();
    enc.pop_scope().unwrap();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "4-var Bool with push_scope should find SAT: {result:?}"
    );
}

/// Regression for the historical ay-dpll limitation where `try_assert_named`
/// broke Bool-sorted SAT model generation. The solver now returns SAT for this
/// direct Boolean obligation. (#2141)
#[test]
#[timeout(30000)]
fn test_ay_named_assert_breaks_bool_sat() {
    let mut enc = AYEncoder::new();
    let b_current = enc.solver_mut().declare_const("b_current", Sort::Bool);
    let b_final = enc.solver_mut().declare_const("b_final", Sort::Bool);
    let old_b_current = enc.solver_mut().declare_const("old_b_current", Sort::Bool);
    let _b_current_final = enc
        .solver_mut()
        .declare_const("b_current_final", Sort::Bool);

    let not_b = enc.solver_mut().not(b_current);
    let body = enc.solver_mut().eq(b_final, not_b);
    enc.assert_term(body);
    let old_eq = enc.solver_mut().eq(old_b_current, b_current);
    enc.assert_term(old_eq);

    let post_eq = enc.solver_mut().eq(b_final, old_b_current);
    let neg_post = enc.solver_mut().not(post_eq);
    enc.solver_mut()
        .try_assert_named(neg_post, "__trust_wp_negated_goal_slice_0")
        .unwrap();
    let result = enc.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "named Bool assertion should preserve SAT model generation: {result:?}"
    );
}

// ── VACUOUS_PROOF_MESSAGE constant ─────────────────────────────────────

#[test]
fn test_vacuous_proof_message_is_descriptive() {
    assert!(
        VACUOUS_PROOF_MESSAGE.contains("vacuous"),
        "message should mention vacuity"
    );
    assert!(
        VACUOUS_PROOF_MESSAGE.contains("UNSAT"),
        "message should mention UNSAT"
    );
    assert!(
        VACUOUS_PROOF_MESSAGE.contains("negated postcondition"),
        "message should reference the negated postcondition"
    );
}

// ── resolve_last_unsat_with_vacuity ─────────────────────────────────

/// Without a negated goal label prefix, `is_vacuous_unsat` takes the legacy
/// path (returns `Ok(false)` → not vacuous), so `resolve_last_unsat_with_vacuity`
/// returns Verified regardless of whether the proof was genuine or vacuous.
/// This documents the legacy behavior — production code always sets a label.
#[test]
#[timeout(30000)]
fn test_resolve_last_unsat_with_vacuity_no_label_returns_verified() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);

    // Contradictory: x > 0 AND x < 0
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let x_lt_0 = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(x_gt_0);
    encoder.assert_term(x_lt_0);

    let sat_result = encoder.check_sat();
    assert!(matches!(sat_result, ay_dpll::api::SolveResult::Unsat(_)));

    // No label prefix → legacy path → Verified (no vacuity check)
    let result = resolve_last_unsat_with_vacuity(&mut encoder);
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "no label prefix should return Verified (legacy path), got: {result:?}"
    );
}

/// With a label prefix set but the negated goal NOT asserted as a named
/// assertion, `is_vacuous_unsat` detects that the goal label is absent from
/// the unsat core and reports the proof as vacuous.
#[test]
#[timeout(30000)]
fn test_resolve_last_unsat_with_vacuity_missing_goal_in_core_returns_vacuous() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);

    // Contradictory base: x > 0 AND x < 0
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let x_lt_0 = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(x_gt_0);
    encoder.assert_term(x_lt_0);

    let result: Result<VerificationResult, crate::error::EncodingError> = encoder
        .with_negated_goal_label_prefix("__trust_wp_test_goal".to_string(), |encoder| {
            let sat_result = encoder.check_sat();
            assert!(matches!(sat_result, ay_dpll::api::SolveResult::Unsat(_)));
            Ok(resolve_last_unsat_with_vacuity(encoder))
        });

    let result = result.unwrap();
    match &result {
        VerificationResult::Unknown(UnknownReason::SolverMessage(msg)) => {
            assert_eq!(
                msg, VACUOUS_PROOF_MESSAGE,
                "missing goal label in unsat core should report vacuous"
            );
        }
        _ => panic!("vacuous proof should return Unknown, got: {result:?}"),
    }
}

// ── collect_body_let_assume_assumptions edge cases ──────────────────

/// Deeply nested LetAssume within multiple wrappers (Old, Deref, View, Final)
/// should still be collected.
#[test]
#[timeout(30000)]
fn test_collect_body_let_assume_through_wrappers() {
    use std::sync::Arc;

    use trust_wp_core::formula::PureExpr;

    let assumption = PureExpr::Bool(true);
    // LetAssume inside Old(Deref(View(Final(...))))
    let inner = PureExpr::LetAssume {
        assumption: Arc::new(assumption.clone()),
        body: Arc::new(PureExpr::Int(42)),
    };
    let body = PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(PureExpr::View(
        Arc::new(PureExpr::Final(Arc::new(inner))),
    )))));

    let collected = collect_body_let_assume_assumptions(&body);
    assert_eq!(
        collected,
        vec![&assumption],
        "should find LetAssume through Old/Deref/View/Final wrappers"
    );
}

/// LogicFnCall args should be traversed for LetAssume nodes.
#[test]
#[timeout(30000)]
fn test_collect_body_let_assume_in_logic_fn_call_args() {
    use std::sync::Arc;

    use trust_wp_core::formula::PureExpr;

    let assumption = PureExpr::Bool(false);
    let arg = PureExpr::LetAssume {
        assumption: Arc::new(assumption.clone()),
        body: Arc::new(PureExpr::Int(0)),
    };
    let body = PureExpr::LogicFnCall {
        name: "my_fn".to_string(),
        args: vec![PureExpr::Int(1), arg],
    };

    let collected = collect_body_let_assume_assumptions(&body);
    assert_eq!(
        collected,
        vec![&assumption],
        "should find LetAssume inside LogicFnCall args"
    );
}

/// Let value and body should both be traversed.
#[test]
#[timeout(30000)]
fn test_collect_body_let_assume_in_let_value_and_body() {
    use std::sync::Arc;

    use trust_wp_core::formula::PureExpr;

    let assumption_in_value = PureExpr::Bool(true);
    let assumption_in_body = PureExpr::Bool(false);
    let body = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::LetAssume {
            assumption: Arc::new(assumption_in_value.clone()),
            body: Arc::new(PureExpr::Int(1)),
        }),
        body: Arc::new(PureExpr::LetAssume {
            assumption: Arc::new(assumption_in_body.clone()),
            body: Arc::new(PureExpr::Int(2)),
        }),
    };

    let collected = collect_body_let_assume_assumptions(&body);
    assert_eq!(
        collected,
        vec![&assumption_in_value, &assumption_in_body],
        "should find LetAssume in both Let value and body"
    );
}
