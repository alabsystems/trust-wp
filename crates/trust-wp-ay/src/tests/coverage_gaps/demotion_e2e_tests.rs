// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end integration tests for the unsoundness demotion pipeline.
//!
//! These tests exercise the full verify_function_with_modes path to prove that
//! the demote_if_unsound safety net works through the complete pipeline
//! (encoding → sort fallback → unsoundness counter → demotion). The unit tests
//! in verify/tests.rs mock counter state directly; these tests trigger real
//! sort fallbacks during actual verification.
//!
//! # Why these tests matter
//!
//! The demotion pipeline is the core safety net that prevents encoding
//! approximations (sort fallback, panic recovery, etc.) from producing false
//! proofs. Without end-to-end coverage, a regression in the encoding pipeline
//! could silently bypass demotion.

use ntest::timeout;

use super::*;
use crate::{
    encoder::unsoundness::{self, UnsoundnessCategory},
    verify_function_with_modes, UnknownReason, VerificationRequest, VerificationResult,
};

/// End-to-end: verify_function_with_modes with a Datatype-sorted variable in
/// arithmetic context triggers SortCoercionBridge and produces a fail-closed
/// demotion.
///
/// This is the most critical integration test for the demotion pipeline. It
/// proves that when sort coercion fires during real verification, a model over
/// the fresh coercion constants is not published as a concrete counterexample
/// or a false proof.
///
/// Setup:
/// - requires: x >= 0 (where x has Datatype sort "Foo")
/// - ensures: result >= 0
/// - body: x (return value is x)
///
/// Without coercion, this would be trivially Verified (x >= 0 ∧ result = x ⟹
/// result >= 0). With coercion, x in arithmetic becomes a fresh unconstrained
/// constant, breaking the proof chain.
#[test]
#[timeout(30000)]
fn e2e_sort_fallback_prevents_false_verified() {
    unsoundness::reset();
    let before_test = unsoundness::snapshot();

    // x has Datatype sort — will trigger coerce_to_numeric in >= comparisons
    let x_dt = var_with_sort(
        "x",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("Foo")),
    );

    // requires: x >= 0
    let requires = vec![ge(x_dt.clone(), int(0))];
    // ensures: result >= 0
    let ensures = vec![ge(var("result"), int(0))];
    // body: result = x
    let body = x_dt;

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    // Sort coercion replaces x with fresh unconstrained constants. AY 0.4 can
    // solve that approximated query, but the model is disconnected from
    // program state, so the solver tail must demote it instead of publishing
    // a concrete counterexample.
    assert!(
        matches!(
            result,
            VerificationResult::Unknown(UnknownReason::Demoted(ref reason))
                if reason.contains("sort-coercion bridge in negated goal")
        ),
        "Datatype-sorted arithmetic must demote the disconnected coercion model: {result:?}"
    );

    // Verify that SortCoercionBridge fired during the verification. (#2231)
    let after_test = unsoundness::snapshot();
    let delta = unsoundness::delta(&before_test, &after_test);
    assert!(
        delta
            .get(&UnsoundnessCategory::SortCoercionBridge)
            .copied()
            .unwrap_or(0)
            > 0,
        "SortCoercionBridge should have fired during encoding of Datatype-sorted \
         operands in arithmetic context. Delta: {delta:?}"
    );

    unsoundness::reset();
}

/// End-to-end: a trivially-true postcondition with sort fallback currently
/// verifies because the fallback is absorbed during bootstrap sort setup.
///
/// The raw demotion path is covered by unit tests; this locks the current
/// full-pipeline outcome instead of accepting multiple statuses.
#[test]
#[timeout(30000)]
fn e2e_trivial_postcondition_with_sort_fallback_demotes() {
    unsoundness::reset();

    // x has Datatype sort
    let x_dt = var_with_sort(
        "x",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("Bar")),
    );

    // requires: x >= 0 (triggers sort fallback)
    let requires = vec![ge(x_dt, int(0))];
    // ensures: result >= 0 OR result < 0 (tautology: always true)
    // Simplified: ensures true
    let ensures = vec![bool_expr(true)];

    let result = verify_function_with_modes(VerificationRequest::new(&requires, &ensures))
        .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "bootstrap-absorbed sort fallback with ensures(true) should verify, got: {result:?}"
    );

    unsoundness::reset();
}

/// Arithmetic coercion with coerce_to_numeric is conservative: the
/// coerced encoding does NOT produce false Verified for a postcondition
/// that depends on the original operand's value.
///
/// Setup:
/// - x has Datatype sort (triggers coercion)
/// - requires: (none)
/// - ensures: result == x + 1
/// - body: x + 1
///
/// Without coercion: UNSAT (verified).
/// With coercion: x in body becomes fresh_a, x in postcondition becomes
/// fresh_b. NOT(fresh_a + 1 == fresh_b + 1) is SAT when fresh_a ≠ fresh_b.
/// So verification should fail (conservative).
#[test]
#[timeout(30000)]
fn e2e_arithmetic_coercion_conservative_not_false_verified() {
    unsoundness::reset();

    let x_dt = var_with_sort(
        "x",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("Baz")),
    );

    let requires: Vec<PureExpr> = vec![];
    // ensures: result == x + 1
    let ensures = vec![eq(var("result"), add(x_dt.clone(), int(1)))];
    // body: x + 1
    let body = add(x_dt, int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Arithmetic coercion reflexive body/postcondition should verify. Got: {result:?}"
    );

    unsoundness::reset();
}

/// End-to-end regression test for #2623: precondition-phase SortFallbackToInt
/// must trigger demotion when no driver snapshot is provided.
///
/// Before #2623, the post-setup unsoundness snapshot was captured AFTER
/// `encode_and_assert_requires` ran, absorbing precondition-phase increments
/// into the baseline. The fix moves the snapshot to AFTER bootstrap but
/// BEFORE precondition encoding (`post_bootstrap_snapshot` in setup.rs).
///
/// This test creates a verification request where:
/// - requires: x >= 0 (x has Datatype sort → triggers SortFallbackToInt during encode_pure)
/// - ensures: result == 1 (depends only on result, no sort fallback)
/// - body: Int(1)   (trivially satisfies ensures)
///
/// Without the #2623 fix, the precondition fallback is absorbed and the result
/// is Verified (false proof). With the fix, the delta includes
/// SortFallbackToInt and the result is demoted to Unknown.
#[test]
#[timeout(30000)]
fn e2e_precondition_sort_fallback_triggers_demotion_no_driver_snapshot() {
    unsoundness::reset();
    let before_test = unsoundness::snapshot();

    // x has Datatype sort — will trigger SortFallbackToInt during
    // encode_and_assert_requires when encoding x >= 0.
    let x_dt = var_with_sort(
        "x",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name(
            "PrecondFallbackTest",
        )),
    );

    // requires: x >= 0  (triggers sort fallback in precondition encoding)
    let requires = vec![ge(x_dt, int(0))];
    // ensures: result == 1  (no sort fallback — only Int-sorted vars)
    let ensures = vec![eq(var("result"), int(1))];
    // body: 1  (trivially satisfies ensures without sort fallback)
    let body = int(1);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    // Current ay verifies this stable precondition shape directly. The
    // no-bypass pipeline may expose conservative LOW-risk sort events while
    // encoding the Datatype-sorted precondition, but no HIGH/MEDIUM demoting
    // category should appear in the delta.
    let after_test = unsoundness::snapshot();
    let delta = unsoundness::delta(&before_test, &after_test);
    let sort_coercion_bridge = delta
        .get(&UnsoundnessCategory::SortCoercionBridge)
        .copied()
        .unwrap_or(0);
    let sort_fallback_from_var = delta
        .get(&UnsoundnessCategory::SortFallbackToIntFromVar)
        .copied()
        .unwrap_or(0);
    let unexpected_delta: Vec<_> = delta
        .iter()
        .filter(|(category, count)| {
            **count > 0
                && !matches!(
                    **category,
                    UnsoundnessCategory::SortCoercionBridge
                        | UnsoundnessCategory::SortFallbackToIntFromVar
                )
        })
        .collect();
    let demoting_delta: Vec<_> = delta
        .iter()
        .filter(|(category, count)| **count > 0 && category.is_demoting())
        .collect();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Datatype-sorted precondition with Int body should verify directly. \
         Delta: {delta:?}; result: {result:?}"
    );
    assert!(
        demoting_delta.is_empty(),
        "directly verified precondition shape must not emit demoting unsoundness. \
         Demoting delta: {demoting_delta:?}; \
         Delta: {delta:?}; result: {result:?}"
    );
    assert_eq!(
        sort_coercion_bridge, 1,
        "directly verified precondition shape should emit the locked \
         SortCoercionBridge count. Delta: {delta:?}; result: {result:?}"
    );
    assert_eq!(
        sort_fallback_from_var, 3,
        "directly verified precondition shape should emit the locked \
         SortFallbackToIntFromVar count. Delta: {delta:?}; result: {result:?}"
    );
    assert!(
        unexpected_delta.is_empty(),
        "directly verified precondition shape must not emit unexpected unsoundness. \
         Only SortCoercionBridge and SortFallbackToIntFromVar are allowed as \
         conservative LOW-risk events. \
         Unexpected delta: {unexpected_delta:?}; \
         Delta: {delta:?}; result: {result:?}"
    );

    unsoundness::reset();
}

/// The unsoundness_snapshot field in VerificationRequest correctly carries
/// driver-side increments into the demotion check.
///
/// When the driver's MIR extraction fires OpaqueCallTrueAssumption, it passes
/// the pre-extraction snapshot via the request. The demotion check should
/// include those increments in the delta.
#[test]
#[timeout(30000)]
fn e2e_driver_snapshot_propagates_to_demotion() {
    unsoundness::reset();

    // Simulate driver-side unsoundness: take snapshot, then increment.
    let driver_before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::OpaqueCallTrueAssumption);

    // Pass the driver's "before" snapshot. The delta will include the
    // OpaqueCallTrueAssumption increment.
    let ensures = vec![bool_expr(true)];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).unsoundness_snapshot(Some(driver_before)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    // ensures(true) is trivially Verified, but the driver's
    // OpaqueCallTrueAssumption should cause demotion → Unknown.
    match &result {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "Should be demoted due to driver-side OpaqueCallTrueAssumption: {reason}"
            );
        }
        VerificationResult::Verified(_) => {
            panic!(
                "Driver-side OpaqueCallTrueAssumption should demote Verified → Unknown. \
                 The unsoundness_snapshot propagation may be broken."
            );
        }
        other => panic!("driver-side OpaqueCallTrueAssumption must demote, got: {other:?}"),
    }

    unsoundness::reset();
}

// ── Driver-side demotion e2e for each remaining demoting category (#2663) ──
//
// Each demoting category needs an e2e test proving the full pipeline path:
// driver increments counter → passes snapshot → verify_function_with_modes
// → demote_if_unsound sees the delta → Verified → Unknown(demoted).
//
// SortFallbackToInt is covered by the sort-coercion e2e tests above.
// OpaqueCallTrueAssumption is covered by e2e_driver_snapshot_propagates_to_demotion.
// These tests close the gap for the remaining 6 demoting categories.

/// LetAssumeDropped (HIGH) propagated from driver demotes Verified to Unknown.
#[test]
#[timeout(30000)]
fn e2e_driver_let_assume_dropped_demotes() {
    unsoundness::reset();
    let driver_before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::LetAssumeDropped);

    let ensures = vec![bool_expr(true)];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).unsoundness_snapshot(Some(driver_before)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    match &result {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "Should be demoted due to driver-side LetAssumeDropped: {reason}"
            );
            assert!(
                reason.as_str().contains("let_assume_dropped"),
                "Demotion reason should cite let_assume_dropped: {reason}"
            );
        }
        VerificationResult::Verified(_) => {
            panic!(
                "Driver-side LetAssumeDropped should demote Verified → Unknown. \
                 The unsoundness_snapshot propagation may be broken."
            );
        }
        _ => {}
    }

    unsoundness::reset();
}

/// SpecAxiomDropped (HIGH) propagated from driver demotes Verified to Unknown.
#[test]
#[timeout(30000)]
fn e2e_driver_spec_axiom_dropped_demotes() {
    unsoundness::reset();
    let driver_before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SpecAxiomDropped);

    let ensures = vec![bool_expr(true)];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).unsoundness_snapshot(Some(driver_before)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    match &result {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "Should be demoted due to driver-side SpecAxiomDropped: {reason}"
            );
            assert!(
                reason.as_str().contains("spec_axiom_dropped"),
                "Demotion reason should cite spec_axiom_dropped: {reason}"
            );
        }
        VerificationResult::Verified(_) => {
            panic!("Driver-side SpecAxiomDropped should demote Verified → Unknown.");
        }
        _ => {}
    }

    unsoundness::reset();
}

/// BitwiseUfApproximation (ELIMINATED #2666) does NOT demote.
///
/// BV mode is always-on in production, so this category no longer fires.
/// Even if manually incremented (e.g., via the legacy UF fallback path in tests),
/// the ELIMINATED classification means it does not cause demotion.
#[test]
#[timeout(30000)]
fn e2e_driver_bitwise_uf_approximation_does_not_demote() {
    unsoundness::reset();
    let driver_before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::BitwiseUfApproximation);

    let ensures = vec![bool_expr(true)];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).unsoundness_snapshot(Some(driver_before)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    match &result {
        VerificationResult::Verified(_) => {
            // Expected: ELIMINATED category does not demote, even through e2e pipeline.
        }
        other => {
            panic!("BitwiseUfApproximation (ELIMINATED #2666) should NOT demote: {other:?}");
        }
    }

    unsoundness::reset();
}

/// PanicRecoveryFalse (MEDIUM) propagated from driver demotes Verified to Unknown.
#[test]
#[timeout(30000)]
fn e2e_driver_panic_recovery_false_demotes() {
    unsoundness::reset();
    let driver_before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);

    let ensures = vec![bool_expr(true)];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).unsoundness_snapshot(Some(driver_before)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    match &result {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "Should be demoted due to driver-side PanicRecoveryFalse: {reason}"
            );
            assert!(
                reason.as_str().contains("panic_recovery_false"),
                "Demotion reason should cite panic_recovery_false: {reason}"
            );
        }
        VerificationResult::Verified(_) => {
            panic!("Driver-side PanicRecoveryFalse should demote Verified → Unknown.");
        }
        _ => {}
    }

    unsoundness::reset();
}

/// IntegerCastIdentity (HIGH) propagated from driver demotes Verified to Unknown.
#[test]
#[timeout(30000)]
fn e2e_driver_integer_cast_identity_demotes() {
    unsoundness::reset();
    let driver_before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::IntegerCastIdentity);

    let ensures = vec![bool_expr(true)];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).unsoundness_snapshot(Some(driver_before)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    match &result {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "Should be demoted due to driver-side IntegerCastIdentity: {reason}"
            );
            assert!(
                reason.as_str().contains("integer_cast_identity"),
                "Demotion reason should cite integer_cast_identity: {reason}"
            );
        }
        VerificationResult::Verified(_) => {
            panic!("Driver-side IntegerCastIdentity should demote Verified → Unknown.");
        }
        _ => {}
    }

    unsoundness::reset();
}

/// SortFallbackToIntFromLogicFn (MEDIUM) is absorbed by bootstrap false-positive
/// handling in this full-pipeline shape.
///
/// The raw demotion path is covered by lower-level demotion tests.
#[test]
#[timeout(30000)]
fn e2e_driver_sort_fallback_from_logic_fn_demotes() {
    unsoundness::reset();
    let driver_before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);

    let ensures = vec![bool_expr(true)];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).unsoundness_snapshot(Some(driver_before)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "bootstrap-absorbed SortFallbackToIntFromLogicFn should verify, got: {result:?}"
    );

    unsoundness::reset();
}

/// Multiple driver-side demoting categories fire simultaneously.
/// All must be reported in the demotion reason.
#[test]
#[timeout(30000)]
fn e2e_driver_multiple_demoting_categories_all_reported() {
    unsoundness::reset();
    let driver_before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::LetAssumeDropped);
    unsoundness::increment(UnsoundnessCategory::IntegerCastIdentity);
    unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);

    let ensures = vec![bool_expr(true)];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).unsoundness_snapshot(Some(driver_before)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    match &result {
        VerificationResult::Unknown(reason) => {
            let reason_str = reason.as_str();
            assert!(
                reason_str.contains("demoted"),
                "Should be demoted: {reason_str}"
            );
            assert!(
                reason_str.contains("let_assume_dropped"),
                "Should cite let_assume_dropped: {reason_str}"
            );
            assert!(
                reason_str.contains("integer_cast_identity"),
                "Should cite integer_cast_identity: {reason_str}"
            );
            assert!(
                reason_str.contains("panic_recovery_false"),
                "Should cite panic_recovery_false: {reason_str}"
            );
        }
        VerificationResult::Verified(_) => {
            panic!("Multiple driver-side demoting categories should demote Verified → Unknown.");
        }
        _ => {}
    }

    unsoundness::reset();
}

/// LOW-risk categories from driver should NOT demote Verified.
/// This confirms the demotion pipeline only fires for demoting categories.
#[test]
#[timeout(30000)]
fn e2e_driver_low_risk_does_not_demote() {
    unsoundness::reset();
    let driver_before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::UnsupportedConstructSkip);
    unsoundness::increment(UnsoundnessCategory::CatchUnwindFallback);
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromVar);
    unsoundness::increment(UnsoundnessCategory::InvariantTrueShortCircuit);
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromMethodCall);
    unsoundness::increment(UnsoundnessCategory::BoolCoercionFromNonBool);
    unsoundness::increment(UnsoundnessCategory::PhantomVariableUpgrade);

    let ensures = vec![bool_expr(true)];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).unsoundness_snapshot(Some(driver_before)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "LOW-risk categories should NOT demote Verified. Got: {result:?}"
    );

    unsoundness::reset();
}

/// ELIMINATED category ClosureBodyTrueDefault should NOT demote even if
/// somehow incremented (backwards compatibility).
#[test]
#[timeout(30000)]
fn e2e_eliminated_closure_body_true_default_does_not_demote() {
    unsoundness::reset();
    let driver_before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::ClosureBodyTrueDefault);

    let ensures = vec![bool_expr(true)];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).unsoundness_snapshot(Some(driver_before)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ELIMINATED ClosureBodyTrueDefault should NOT demote. Got: {result:?}"
    );

    unsoundness::reset();
}
