// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use crate::{
    encoder::unsoundness::{self, UnsoundnessCategory},
    verify::{
        demote_if_unsound, merge_pre_verification_and_post_bootstrap_snapshots, VerificationResult,
    },
    UnknownReason,
};

// --- Unsoundness demotion (#2106) ---

/// Verified result with no unsoundness counters passes through unchanged.
#[test]
#[timeout(30000)]
fn demote_if_unsound_no_counters_passes_through() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    let result = crate::verify::VerificationResult::Verified(None);
    let demoted = demote_if_unsound(&before, result);
    assert!(
        matches!(demoted, crate::verify::VerificationResult::Verified(_)),
        "no unsoundness counters should leave Verified unchanged: {demoted:?}"
    );
    unsoundness::reset();
}

/// Verified result with LOW-risk counters passes through unchanged.
#[test]
#[timeout(30000)]
fn demote_if_unsound_low_risk_passes_through() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    // Increment a LOW risk category during "verification"
    unsoundness::increment(UnsoundnessCategory::UnsupportedConstructSkip);
    unsoundness::increment(UnsoundnessCategory::CatchUnwindFallback);
    let result = crate::verify::VerificationResult::Verified(None);
    let demoted = demote_if_unsound(&before, result);
    assert!(
        matches!(demoted, crate::verify::VerificationResult::Verified(_)),
        "LOW risk unsoundness should NOT demote Verified: {demoted:?}"
    );
    unsoundness::reset();
}

/// Verified result with HIGH-risk counter is demoted to Unknown.
#[test]
#[timeout(30000)]
fn demote_if_unsound_high_risk_demotes_verified() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    // Increment a HIGH risk category during "verification"
    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
    let result = crate::verify::VerificationResult::Verified(None);
    let demoted = demote_if_unsound(&before, result);
    match &demoted {
        crate::verify::VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "demoted reason should contain 'demoted': {reason}"
            );
            assert!(
                reason.as_str().contains("sort_fallback_to_int"),
                "demoted reason should list the category: {reason}"
            );
        }
        other => panic!("HIGH risk should demote Verified to Unknown, got: {other:?}"),
    }
    unsoundness::reset();
}

/// MEDIUM-risk counter also demotes Verified.
#[test]
#[timeout(30000)]
fn demote_if_unsound_medium_risk_demotes_verified() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);
    let result = crate::verify::VerificationResult::Verified(None);
    let demoted = demote_if_unsound(&before, result);
    assert!(
        matches!(demoted, crate::verify::VerificationResult::Unknown(_)),
        "MEDIUM risk should demote Verified to Unknown: {demoted:?}"
    );
    unsoundness::reset();
}

/// Non-Verified results pass through unchanged even with demoting counters.
#[test]
#[timeout(30000)]
fn demote_if_unsound_non_verified_passes_through() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::LetAssumeDropped);
    let result = crate::verify::VerificationResult::Unknown(UnknownReason::Timeout);
    let demoted = demote_if_unsound(&before, result);
    match &demoted {
        crate::verify::VerificationResult::Unknown(reason) => {
            assert!(
                matches!(reason, UnknownReason::Timeout),
                "Unknown reason should be preserved unchanged"
            );
        }
        other => panic!("Unknown should pass through unchanged: {other:?}"),
    }
    unsoundness::reset();
}

/// Pre-existing counters from previous functions are not counted against
/// the current function. Only the delta matters.
#[test]
#[timeout(30000)]
fn demote_if_unsound_ignores_pre_existing_counters() {
    unsoundness::reset();
    // Simulate previous function's unsoundness
    unsoundness::increment(UnsoundnessCategory::ClosureBodyTrueDefault);
    unsoundness::increment(UnsoundnessCategory::ClosureBodyTrueDefault);
    // Snapshot AFTER previous function's counters are set
    let before = unsoundness::snapshot();
    // This function's verification produces no new unsoundness
    let result = crate::verify::VerificationResult::Verified(None);
    let demoted = demote_if_unsound(&before, result);
    assert!(
        matches!(demoted, crate::verify::VerificationResult::Verified(_)),
        "pre-existing counters should not affect current function: {demoted:?}"
    );
    unsoundness::reset();
}

// --- Per-phase loop unsoundness demotion (#2212) ---
//
// After #2212, each loop sub-check (init, preservation, postcondition,
// variant_nonneg, variant_decrease) takes its own unsoundness snapshot
// inside verify_loop_invariant_inner. These tests validate the per-phase
// demote_if_unsound behavior that replaces the former blanket
// demote_loop_if_unsound.

/// Per-phase demotion isolates a sort fallback to only the affected phase.
#[test]
#[timeout(30000)]
fn per_phase_demotion_isolates_sort_fallback_to_affected_phase() {
    unsoundness::reset();

    let before_init = unsoundness::snapshot();
    let init_result = crate::verify::VerificationResult::Verified(None);
    let init = demote_if_unsound(&before_init, init_result);
    assert!(
        matches!(init, crate::verify::VerificationResult::Verified(_)),
        "clean phase should remain Verified: {init:?}"
    );

    let before_pres = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
    let pres_result = crate::verify::VerificationResult::Verified(None);
    let pres = demote_if_unsound(&before_pres, pres_result);
    assert!(
        matches!(&pres, crate::verify::VerificationResult::Unknown(r) if r.as_str().contains("demoted")),
        "phase with sort fallback should be demoted: {pres:?}"
    );

    let before_post = unsoundness::snapshot();
    let post_result = crate::verify::VerificationResult::Verified(None);
    let post = demote_if_unsound(&before_post, post_result);
    assert!(
        matches!(post, crate::verify::VerificationResult::Verified(_)),
        "subsequent clean phase should remain Verified: {post:?}"
    );

    unsoundness::reset();
}

/// Multiple phases can independently fire unsoundness without cross-contamination.
#[test]
#[timeout(30000)]
fn per_phase_demotion_multiple_phases_independent() {
    unsoundness::reset();

    let before_1 = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
    let r1 = demote_if_unsound(&before_1, crate::verify::VerificationResult::Verified(None));
    assert!(matches!(&r1, crate::verify::VerificationResult::Unknown(_)));

    let before_2 = unsoundness::snapshot();
    let r2 = demote_if_unsound(&before_2, crate::verify::VerificationResult::Verified(None));
    assert!(matches!(r2, crate::verify::VerificationResult::Verified(_)));

    let before_3 = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);
    let r3 = demote_if_unsound(&before_3, crate::verify::VerificationResult::Verified(None));
    assert!(matches!(&r3, crate::verify::VerificationResult::Unknown(_)));

    let before_4 = unsoundness::snapshot();
    let r4 = demote_if_unsound(&before_4, crate::verify::VerificationResult::Verified(None));
    assert!(matches!(r4, crate::verify::VerificationResult::Verified(_)));

    unsoundness::reset();
}

/// Non-Verified results pass through unchanged regardless of unsoundness.
#[test]
#[timeout(30000)]
fn per_phase_demotion_non_verified_passes_through() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);

    let failed = demote_if_unsound(
        &before,
        crate::verify::VerificationResult::Failed(crate::verify::Counterexample::empty()),
    );
    assert!(
        matches!(failed, crate::verify::VerificationResult::Failed(_)),
        "Failed should pass through: {failed:?}"
    );

    let unknown = demote_if_unsound(
        &before,
        crate::verify::VerificationResult::Unknown(UnknownReason::Timeout),
    );
    match &unknown {
        crate::verify::VerificationResult::Unknown(r) => {
            assert!(
                matches!(r, UnknownReason::Timeout),
                "Unknown reason should be preserved: {r}"
            );
        }
        other => panic!("Unknown should pass through unchanged: {other:?}"),
    }

    unsoundness::reset();
}

/// LOW-risk unsoundness does not demote in per-phase checks.
#[test]
#[timeout(30000)]
fn per_phase_demotion_low_risk_does_not_demote() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::UnsupportedConstructSkip);
    unsoundness::increment(UnsoundnessCategory::CatchUnwindFallback);
    let result = demote_if_unsound(&before, crate::verify::VerificationResult::Verified(None));
    assert!(
        matches!(result, crate::verify::VerificationResult::Verified(_)),
        "LOW risk should not demote: {result:?}"
    );
    unsoundness::reset();
}

/// The shared no-driver baseline must not absorb demoting precondition counters.
#[test]
#[timeout(30000)]
fn no_driver_baseline_keeps_precondition_demotions_visible() {
    unsoundness::reset();
    let pre_setup_snapshot = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    let baseline = merge_pre_verification_and_post_bootstrap_snapshots(
        &pre_setup_snapshot,
        &unsoundness::snapshot(),
    );

    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
    let demoted = demote_if_unsound(&baseline, VerificationResult::Verified(None));
    match demoted {
        VerificationResult::Unknown(reason) => {
            let reason = reason.as_str();
            assert!(
                reason.contains("sort_fallback_to_int(1)"),
                "precondition demotion should remain visible: {reason}"
            );
            assert!(
                !reason.contains("sort_fallback_to_int_from_logic_fn"),
                "bootstrap-only logic-fn noise should be absorbed: {reason}"
            );
        }
        other => panic!("precondition demotion should not be absorbed: {other:?}"),
    }
    unsoundness::reset();
}

/// Bootstrap-only logic-fn sort-fallback noise should stay absorbed.
#[test]
#[timeout(30000)]
fn merged_baseline_absorbs_only_bootstrap_logic_fn_noise() {
    unsoundness::reset();
    let pre_setup_snapshot = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    let baseline = merge_pre_verification_and_post_bootstrap_snapshots(
        &pre_setup_snapshot,
        &unsoundness::snapshot(),
    );

    let demoted = demote_if_unsound(&baseline, VerificationResult::Verified(None));
    assert!(
        matches!(demoted, VerificationResult::Verified(_)),
        "bootstrap-only logic-fn noise should be absorbed: {demoted:?}"
    );
    unsoundness::reset();
}

/// Precondition-phase SortFallbackToIntFromLogicFn increments must NOT be
/// absorbed when the post-bootstrap snapshot is taken at the correct point
/// (after bootstrap, before precondition encoding).
///
/// This is the regression test for #2623: previously, the pipeline used a
/// post-setup snapshot (after BOTH bootstrap AND precondition encoding) as
/// the "post_bootstrap" argument, which caused real precondition-phase
/// increments for SortFallbackToIntFromLogicFn to be absorbed into the
/// baseline alongside harmless bootstrap false positives.
#[test]
#[timeout(30000)]
fn precondition_phase_logic_fn_fallback_not_absorbed_by_correct_snapshot() {
    unsoundness::reset();

    // Simulate: pre-verification snapshot (before anything).
    let pre_verification = unsoundness::snapshot();

    // Simulate: bootstrap runs, triggering a false-positive LogicFn increment.
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);

    // Correct: take snapshot HERE (after bootstrap, before precondition encoding).
    let post_bootstrap = unsoundness::snapshot();

    // Simulate: precondition encoding triggers a REAL LogicFn increment.
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);

    // Build baseline using the CORRECT post-bootstrap snapshot.
    let baseline =
        merge_pre_verification_and_post_bootstrap_snapshots(&pre_verification, &post_bootstrap);

    // The baseline should have SortFallbackToIntFromLogicFn = 1 (from bootstrap).
    // Current counter = 2 (1 bootstrap + 1 precondition).
    // Delta = 2 - 1 = 1 → demotion SHOULD fire.
    let result = demote_if_unsound(&baseline, VerificationResult::Verified(None));
    match &result {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason
                    .as_str()
                    .contains("sort_fallback_to_int_from_logic_fn"),
                "precondition-phase LogicFn increment must trigger demotion: {reason}"
            );
        }
        other => panic!(
            "precondition-phase SortFallbackToIntFromLogicFn must NOT be absorbed: {other:?}"
        ),
    }

    unsoundness::reset();
}

/// Contrast with #2623: when using the WRONG (post-setup) snapshot, the
/// precondition-phase increment IS absorbed and demotion does not fire.
/// This documents the pre-fix behavior.
#[test]
#[timeout(30000)]
fn precondition_phase_logic_fn_fallback_absorbed_by_wrong_snapshot() {
    unsoundness::reset();

    let pre_verification = unsoundness::snapshot();

    // Bootstrap false positive.
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);

    // Precondition encoding real increment.
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);

    // WRONG: take snapshot AFTER both bootstrap AND precondition encoding.
    let wrong_post_setup = unsoundness::snapshot();

    // Baseline absorbs ALL SortFallbackToIntFromLogicFn increments (count=2).
    let baseline =
        merge_pre_verification_and_post_bootstrap_snapshots(&pre_verification, &wrong_post_setup);

    // Current counter = 2, baseline = 2, delta = 0 → NO demotion (the bug).
    let result = demote_if_unsound(&baseline, VerificationResult::Verified(None));
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "wrong snapshot absorbs real increments (this is the #2623 bug behavior): {result:?}"
    );

    unsoundness::reset();
}

// --- catch_unwind counter rollback (#2623) ---

/// When `catch_verification_phase_ay_panics` catches an error, unsoundness
/// counters from inside the panicking closure must be rolled back so they
/// do not pollute the demotion baseline for subsequent verifications.
#[test]
#[timeout(30000)]
fn catch_unwind_rollback_restores_counters_on_error() {
    use crate::verify::pipeline::catch_verification_phase_ay_panics;

    unsoundness::reset();
    let before = unsoundness::snapshot();

    // Simulate: a verification phase that increments a counter then returns Err.
    let result = catch_verification_phase_ay_panics(
        "test_phase",
        || -> Result<(), crate::error::EncodingError> {
            unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
            unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);
            Err(crate::error::EncodingError::solver_error(
                "simulated error".to_string(),
            ))
        },
    );

    assert!(result.is_err(), "should propagate the error");

    // After rollback, counters should match the pre-call state.
    let after = unsoundness::snapshot();
    let d = unsoundness::delta(&before, &after);
    assert!(
        d.is_empty(),
        "counters should be rolled back to pre-call state on error, but delta was: {d:?}"
    );

    unsoundness::reset();
}

/// When `catch_verification_phase_ay_panics` succeeds, counters must NOT
/// be rolled back — the increments are real encoding state.
#[test]
#[timeout(30000)]
fn catch_unwind_no_rollback_on_success() {
    use crate::verify::pipeline::catch_verification_phase_ay_panics;

    unsoundness::reset();
    let before = unsoundness::snapshot();

    let result = catch_verification_phase_ay_panics("test_phase", || {
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
        Ok(42)
    });

    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 42);

    let after = unsoundness::snapshot();
    let d = unsoundness::delta(&before, &after);
    assert_eq!(
        d.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&1),
        "successful call should preserve counter increments"
    );

    unsoundness::reset();
}

/// `merge_pre_verification_and_post_bootstrap_snapshots` uses the
/// `has_bootstrap_false_positives()` method to determine which categories
/// to absorb, not a hardcoded category check.
#[test]
#[timeout(30000)]
fn merge_uses_has_bootstrap_false_positives_trait() {
    // Verify that has_bootstrap_false_positives covers exactly the expected
    // categories. If a new category is added to the method, this test must
    // be updated to match.
    let bootstrap_fp_categories: Vec<_> = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.has_bootstrap_false_positives())
        .collect();
    assert_eq!(
        bootstrap_fp_categories,
        vec![&UnsoundnessCategory::SortFallbackToIntFromLogicFn],
        "only SortFallbackToIntFromLogicFn should have bootstrap false positives"
    );

    // Verify the merge function absorbs it.
    let mut driver = unsoundness::Snapshot::new();
    driver.insert(UnsoundnessCategory::SortFallbackToIntFromLogicFn, 2);
    let mut bootstrap = unsoundness::Snapshot::new();
    bootstrap.insert(UnsoundnessCategory::SortFallbackToIntFromLogicFn, 5);
    let merged = merge_pre_verification_and_post_bootstrap_snapshots(&driver, &bootstrap);
    assert_eq!(
        merged.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn),
        Some(&5),
        "bootstrap false positive category should use post-bootstrap value"
    );

    // Verify that a non-bootstrap category is NOT absorbed.
    let mut driver2 = unsoundness::Snapshot::new();
    driver2.insert(UnsoundnessCategory::SortFallbackToInt, 2);
    let mut bootstrap2 = unsoundness::Snapshot::new();
    bootstrap2.insert(UnsoundnessCategory::SortFallbackToInt, 5);
    let merged2 = merge_pre_verification_and_post_bootstrap_snapshots(&driver2, &bootstrap2);
    assert_eq!(
        merged2.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&2),
        "non-bootstrap category should keep driver value"
    );
}

/// Demoting unsoundness increments during precondition encoding must be
/// captured in the delta even when no driver snapshot exists.
///
/// Simulates the full pipeline flow from `run_verification_pipeline`:
/// 1. No driver snapshot -> `pre_setup_snapshot` = current counters
/// 2. Bootstrap runs (may trigger false-positive LogicFn increments)
/// 3. `post_bootstrap_snapshot` taken between bootstrap and precondition encoding
/// 4. Precondition encoding runs (triggers REAL demoting increment)
/// 5. Demotion baseline built via `merge_pre_verification_and_post_bootstrap_snapshots`
/// 6. `demote_if_unsound` computes delta from baseline -> must detect the increment
///
/// Regression test for #2623: without the correct snapshot placement, the
/// precondition-phase increment would be folded into the baseline and
/// become invisible to the demotion check.
#[test]
#[timeout(30000)]
fn precondition_increment_captured_without_driver_snapshot() {
    unsoundness::reset();

    // Step 1: No driver snapshot — pipeline takes snapshot at entry.
    let pre_setup_snapshot = unsoundness::snapshot();

    // Step 2: Bootstrap runs — triggers a false-positive LogicFn increment.
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);

    // Step 3: post_bootstrap_snapshot taken here (after bootstrap, before preconditions).
    let post_bootstrap = unsoundness::snapshot();

    // Step 4: Precondition encoding triggers a REAL demoting increment.
    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);

    // Step 5: Build demotion baseline.
    let baseline =
        merge_pre_verification_and_post_bootstrap_snapshots(&pre_setup_snapshot, &post_bootstrap);

    // Step 6: demote_if_unsound should detect the SortFallbackToInt increment.
    let result = demote_if_unsound(&baseline, VerificationResult::Verified(None));
    match &result {
        VerificationResult::Unknown(reason) => {
            let reason_str = reason.as_str();
            assert!(
                reason_str.contains("sort_fallback_to_int(1)"),
                "precondition SortFallbackToInt must trigger demotion: {reason_str}"
            );
            // Bootstrap false-positive LogicFn noise must NOT appear in demotion.
            assert!(
                !reason_str.contains("sort_fallback_to_int_from_logic_fn"),
                "bootstrap LogicFn noise must be absorbed: {reason_str}"
            );
        }
        other => panic!(
            "precondition-phase SortFallbackToInt must NOT be absorbed into baseline: {other:?}"
        ),
    }

    unsoundness::reset();
}

// --- Direct demotion tests for each demoting category (#2663) ---
//
// Each demoting category needs a direct test that verifies the full
// snapshot → increment → Verified → demote_if_unsound → Unknown pipeline.
// SortFallbackToInt and PanicRecoveryFalse are covered above; these tests
// close the gap for the remaining 6 demoting categories.

/// SpecAxiomDropped (HIGH, demoting) demotes Verified to Unknown.
#[test]
#[timeout(30000)]
fn demote_if_unsound_spec_axiom_dropped_demotes() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SpecAxiomDropped);
    let result = VerificationResult::Verified(None);
    let demoted = demote_if_unsound(&before, result);
    match &demoted {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "should be demoted: {reason}"
            );
            assert!(
                reason.as_str().contains("spec_axiom_dropped"),
                "should cite spec_axiom_dropped: {reason}"
            );
        }
        other => panic!("SpecAxiomDropped (HIGH) should demote Verified to Unknown: {other:?}"),
    }
    unsoundness::reset();
}

/// BitwiseUfApproximation (ELIMINATED #2666, non-demoting) does NOT demote.
///
/// Since BV mode is always-on in production, this category no longer fires.
/// Even if it did (via the legacy UF fallback path in tests), it should not
/// demote because the category is reclassified as ELIMINATED.
#[test]
#[timeout(30000)]
fn demote_if_unsound_bitwise_uf_approximation_does_not_demote() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::BitwiseUfApproximation);
    let result = VerificationResult::Verified(None);
    let demoted = demote_if_unsound(&before, result);
    match &demoted {
        VerificationResult::Verified(_) => {
            // Expected: ELIMINATED category does not demote.
        }
        other => panic!("BitwiseUfApproximation (ELIMINATED #2666) should NOT demote: {other:?}"),
    }
    unsoundness::reset();
}

/// OpaqueCallTrueAssumption (HIGH, demoting) demotes Verified to Unknown.
#[test]
#[timeout(30000)]
fn demote_if_unsound_opaque_call_true_assumption_demotes() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::OpaqueCallTrueAssumption);
    let result = VerificationResult::Verified(None);
    let demoted = demote_if_unsound(&before, result);
    match &demoted {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "should be demoted: {reason}"
            );
            assert!(
                reason.as_str().contains("opaque_call_true_assumption"),
                "should cite opaque_call_true_assumption: {reason}"
            );
        }
        other => {
            panic!("OpaqueCallTrueAssumption (HIGH) should demote Verified to Unknown: {other:?}")
        }
    }
    unsoundness::reset();
}

/// IntegerCastIdentity (HIGH, demoting) demotes Verified to Unknown.
#[test]
#[timeout(30000)]
fn demote_if_unsound_integer_cast_identity_demotes() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::IntegerCastIdentity);
    let result = VerificationResult::Verified(None);
    let demoted = demote_if_unsound(&before, result);
    match &demoted {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "should be demoted: {reason}"
            );
            assert!(
                reason.as_str().contains("integer_cast_identity"),
                "should cite integer_cast_identity: {reason}"
            );
        }
        other => panic!("IntegerCastIdentity (HIGH) should demote Verified to Unknown: {other:?}"),
    }
    unsoundness::reset();
}

/// SortFallbackToIntFromLogicFn (MEDIUM, demoting) demotes Verified to Unknown.
#[test]
#[timeout(30000)]
fn demote_if_unsound_sort_fallback_to_int_from_logic_fn_demotes() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    let result = VerificationResult::Verified(None);
    let demoted = demote_if_unsound(&before, result);
    match &demoted {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "should be demoted: {reason}"
            );
            assert!(
                reason
                    .as_str()
                    .contains("sort_fallback_to_int_from_logic_fn"),
                "should cite sort_fallback_to_int_from_logic_fn: {reason}"
            );
        }
        other => panic!(
            "SortFallbackToIntFromLogicFn (MEDIUM) should demote Verified to Unknown: {other:?}"
        ),
    }
    unsoundness::reset();
}

/// LetAssumeDropped (HIGH, demoting) demotes Verified to Unknown.
/// (Complements the passthrough test at line 98 which only tests
/// non-Verified preservation with LetAssumeDropped.)
#[test]
#[timeout(30000)]
fn demote_if_unsound_let_assume_dropped_demotes() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::LetAssumeDropped);
    let result = VerificationResult::Verified(None);
    let demoted = demote_if_unsound(&before, result);
    match &demoted {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("demoted"),
                "should be demoted: {reason}"
            );
            assert!(
                reason.as_str().contains("let_assume_dropped"),
                "should cite let_assume_dropped: {reason}"
            );
        }
        other => panic!("LetAssumeDropped (HIGH) should demote Verified to Unknown: {other:?}"),
    }
    unsoundness::reset();
}

/// When precondition encoding triggers multiple demoting categories, ALL
/// must appear in the demotion reason -- none should be silently absorbed
/// by the baseline.
#[test]
#[timeout(30000)]
fn multiple_precondition_demoting_categories_all_captured() {
    unsoundness::reset();

    let pre_setup_snapshot = unsoundness::snapshot();

    // Bootstrap false positive (will be absorbed).
    unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    let post_bootstrap = unsoundness::snapshot();

    // Precondition encoding triggers two distinct demoting categories.
    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
    unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);

    let baseline =
        merge_pre_verification_and_post_bootstrap_snapshots(&pre_setup_snapshot, &post_bootstrap);

    let result = demote_if_unsound(&baseline, VerificationResult::Verified(None));
    match &result {
        VerificationResult::Unknown(reason) => {
            let reason_str = reason.as_str();
            assert!(
                reason_str.contains("sort_fallback_to_int"),
                "SortFallbackToInt must be in demotion reason: {reason_str}"
            );
            assert!(
                reason_str.contains("panic_recovery_false"),
                "PanicRecoveryFalse must be in demotion reason: {reason_str}"
            );
        }
        other => panic!("multiple demoting categories must trigger demotion: {other:?}"),
    }

    unsoundness::reset();
}

// --- PremiseNeutralizedEq fail-closed counterexample hygiene ---
// (arc_and_rc sort-plan fix, part c)

/// A Failed(Counterexample) verdict produced while an assumption-position
/// equality was fabricated away must be demoted to Unknown — the model may
/// only exist because a real premise vanished.
#[test]
#[timeout(30000)]
fn premise_neutralized_eq_demotes_failed_to_unknown() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::PremiseNeutralizedEq);

    let failed = crate::verify::VerificationResult::Failed(crate::verify::Counterexample::empty());
    let demoted = demote_if_unsound(&before, failed);
    match &demoted {
        VerificationResult::Unknown(UnknownReason::Demoted(msg)) => {
            assert!(
                msg.contains("premise_neutralized_eq"),
                "demotion message should cite premise_neutralized_eq: {msg}"
            );
            assert!(
                msg.contains("counterexample verdict withheld"),
                "demotion message should explain the fail-closed withholding: {msg}"
            );
        }
        other => {
            panic!("PremiseNeutralizedEq must demote Failed to Unknown(Demoted), got: {other:?}")
        }
    }
    unsoundness::reset();
}

/// PremiseNeutralizedEq weakens the assumption base, which is strictly
/// conservative for proofs — a Verified result must NOT be demoted.
#[test]
#[timeout(30000)]
fn premise_neutralized_eq_does_not_demote_verified() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::PremiseNeutralizedEq);

    let result = demote_if_unsound(&before, VerificationResult::Verified(None));
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "PremiseNeutralizedEq is non-demoting for Verified: {result:?}"
    );
    unsoundness::reset();
}

/// Failed verdicts with only OTHER demoting categories in the delta keep
/// their verdict — the Failed arm is keyed exclusively on
/// PremiseNeutralizedEq so genuine goal-side failures (and the SF lane's
/// expected failures) survive.
#[test]
#[timeout(30000)]
fn failed_without_premise_neutralization_passes_through() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
    unsoundness::increment(UnsoundnessCategory::LetAssumeDropped);

    let failed = crate::verify::VerificationResult::Failed(crate::verify::Counterexample::empty());
    let result = demote_if_unsound(&before, failed);
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Failed without PremiseNeutralizedEq must pass through: {result:?}"
    );
    unsoundness::reset();
}

/// Encoder-level pin: `eq_term` on Bool vs out-of-range Int literal fires
/// PremiseNeutralizedEq ONLY in assumption position. Goal-side fabrications
/// keep the placeholder unprovable (conservative) without poisoning
/// counterexample verdicts.
#[test]
#[timeout(30000)]
fn premise_neutralized_eq_fires_only_in_assumption_position() {
    use ay_dpll::api::Sort;

    let mut encoder = crate::encoder::AYEncoder::new_pure();
    let b = encoder.solver_mut().declare_const("b", Sort::Bool);
    let two = encoder.solver_mut().int_const(2);

    unsoundness::reset();

    // Goal position: neutral placeholder, but NO premise-neutralization mark.
    let before_goal = unsoundness::snapshot();
    let _ = encoder.eq_term(b, two);
    let goal_delta = unsoundness::delta(&before_goal, &unsoundness::snapshot());
    assert!(
        !goal_delta.contains_key(&UnsoundnessCategory::PremiseNeutralizedEq),
        "goal-position fabrication must NOT fire PremiseNeutralizedEq: {goal_delta:?}"
    );
    assert_eq!(
        goal_delta.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&1),
        "the Bool-vs-literal neutralization path itself should have fired"
    );

    // Assumption position: the same shape marks the premise neutralization.
    let before_premise = unsoundness::snapshot();
    encoder.with_assumption_position(|encoder| {
        let _ = encoder.eq_term(b, two);
    });
    let premise_delta = unsoundness::delta(&before_premise, &unsoundness::snapshot());
    assert_eq!(
        premise_delta.get(&UnsoundnessCategory::PremiseNeutralizedEq),
        Some(&1),
        "assumption-position fabrication must fire PremiseNeutralizedEq: {premise_delta:?}"
    );

    unsoundness::reset();
}
