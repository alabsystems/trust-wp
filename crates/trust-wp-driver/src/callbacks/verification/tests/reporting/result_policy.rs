// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_ay::{Counterexample, UnknownReason, VerificationOutcome, VerificationResult};

use crate::callbacks::{
    reporting::{format_verification_summary, VerificationCounters},
    verification::loop_contract::{
        classify_obligation_outcome, classify_obligation_result, record_encoding_error,
        worse_result, ObligationOutcome,
    },
};

#[test]
fn classify_obligation_result_verified_returns_verified_no_counter_delta() {
    let (outcome, delta_failed, delta_errors, delta_demoted) =
        classify_obligation_result(VerificationResult::Verified(None), "test::fn", "test.rs:1");
    assert_eq!(outcome, ObligationOutcome::Verified);
    assert_eq!(delta_failed, 0, "Verified should not increment failed");
    assert_eq!(delta_errors, 0, "Verified should not increment errors");
    assert_eq!(delta_demoted, 0, "Verified should not increment demoted");
}

#[test]
fn classify_obligation_outcome_verified_without_provenance_is_evidence_gap() {
    let (outcome, delta_failed, delta_errors, delta_demoted, delta_evidence_gaps, delta_warnings) =
        classify_obligation_outcome(
            VerificationOutcome::without_provenance(VerificationResult::Verified(None)),
            "test::fn",
            "test.rs:1",
        );
    assert_eq!(outcome, ObligationOutcome::EvidenceGap);
    assert_eq!(delta_failed, 0);
    assert_eq!(delta_errors, 0);
    assert_eq!(delta_demoted, 0);
    assert_eq!(delta_evidence_gaps, 1);
    assert_eq!(delta_warnings, 1);
}

#[test]
fn classify_obligation_result_assumed_returns_assumed_with_reason() {
    let reason = "axiom-only function".to_string();
    let (outcome, delta_failed, delta_errors, delta_demoted) = classify_obligation_result(
        VerificationResult::Assumed(reason.clone()),
        "test::fn",
        "test.rs:1",
    );
    assert_eq!(outcome, ObligationOutcome::Assumed(reason));
    assert_eq!(delta_failed, 0, "Assumed should not increment failed");
    assert_eq!(delta_errors, 0, "Assumed should not increment errors");
    assert_eq!(delta_demoted, 0, "Assumed should not increment demoted");
}

#[test]
fn classify_obligation_result_failed_increments_failed_not_errors() {
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let (outcome, delta_failed, delta_errors, delta_demoted) =
        classify_obligation_result(VerificationResult::Failed(cex), "test::fn", "test.rs:1");
    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(delta_failed, 1, "Failed must increment failed counter");
    assert_eq!(delta_errors, 0, "Failed must NOT increment errors counter");
    assert_eq!(delta_demoted, 0, "Failed should not increment demoted");
}

#[test]
fn classify_obligation_result_unknown_increments_errors_not_failed() {
    let (outcome, delta_failed, delta_errors, delta_demoted) = classify_obligation_result(
        VerificationResult::Unknown(UnknownReason::Unspecified),
        "test::fn",
        "test.rs:1",
    );
    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(delta_failed, 0, "Unknown must NOT increment failed counter");
    assert_eq!(delta_errors, 1, "Unknown must increment errors counter");
    assert_eq!(
        delta_demoted, 0,
        "Unknown(Unspecified) should not be demoted"
    );
}

#[test]
fn classify_obligation_result_unknown_with_reason_increments_errors() {
    let (outcome, delta_failed, delta_errors, delta_demoted) = classify_obligation_result(
        VerificationResult::Unknown(UnknownReason::Timeout),
        "test::fn",
        "test.rs:1",
    );
    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(delta_failed, 0, "Unknown(reason) must NOT increment failed");
    assert_eq!(delta_errors, 1, "Unknown(reason) must increment errors");
    assert_eq!(
        delta_demoted, 0,
        "Non-demotion Unknown should not be demoted"
    );
}

#[test]
fn classify_obligation_result_demoted_unknown_tracks_demotion() {
    let (outcome, delta_failed, delta_errors, delta_demoted) = classify_obligation_result(
        VerificationResult::Unknown(UnknownReason::Demoted(
            "encoding approximations may affect soundness: sort_fallback_to_int(1)".to_string(),
        )),
        "test::fn",
        "test.rs:1",
    );
    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(delta_failed, 0, "Demoted must NOT increment failed");
    assert_eq!(delta_errors, 1, "Demoted must increment errors");
    assert_eq!(delta_demoted, 1, "Demoted must increment demoted (#2106)");
}

#[test]
fn classify_obligation_result_vacuous_solver_message_is_not_verified() {
    let (outcome, delta_failed, delta_errors, delta_demoted) = classify_obligation_result(
        VerificationResult::Unknown(UnknownReason::SolverMessage(
            "vacuous proof: base assertions are UNSAT without the negated postcondition"
                .to_string(),
        )),
        "test::fn",
        "test.rs:1",
    );
    assert_eq!(
        outcome,
        ObligationOutcome::Vacuous,
        "Vacuous loop obligations must not map to Verified"
    );
    assert_ne!(outcome, ObligationOutcome::Verified);
    assert_eq!(delta_failed, 0, "Vacuous does not increment failed");
    assert_eq!(delta_errors, 0, "Vacuous is tracked separately");
    assert_eq!(delta_demoted, 0, "Vacuous is not a demotion");
}

mod report_obligation_result;

// ── worse_result priority tests (#2010) ──────────────────────────────────────
//
// `worse_result` aggregates two VerificationResult values, returning the more
// severe. Priority: Failed > Unknown > Assumed > Verified. This enables
// verify_loop_call_obligations to check BOTH pre-loop and in-loop obligations
// and surface the most actionable result, rather than short-circuiting on the
// first non-Verified outcome.

#[test]
fn worse_result_none_returns_new() {
    let result = worse_result(None, VerificationResult::Verified(None));
    assert!(matches!(result, VerificationResult::Verified(_)));
}

#[test]
fn worse_result_failed_beats_unknown() {
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let result = worse_result(
        Some(VerificationResult::Unknown(UnknownReason::Unspecified)),
        VerificationResult::Failed(cex),
    );
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Failed should beat Unknown"
    );
}

#[test]
fn worse_result_unknown_beats_assumed() {
    let result = worse_result(
        Some(VerificationResult::Assumed("test".into())),
        VerificationResult::Unknown(UnknownReason::Timeout),
    );
    assert!(
        matches!(result, VerificationResult::Unknown(_)),
        "Unknown should beat Assumed"
    );
}

#[test]
fn worse_result_keeps_current_when_more_severe() {
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let result = worse_result(
        Some(VerificationResult::Failed(cex)),
        VerificationResult::Unknown(UnknownReason::Unspecified),
    );
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Failed should be kept over Unknown"
    );
}

#[test]
fn worse_result_assumed_beats_verified() {
    let result = worse_result(
        Some(VerificationResult::Verified(None)),
        VerificationResult::Assumed("axiom-only".into()),
    );
    assert!(
        matches!(result, VerificationResult::Assumed(_)),
        "Assumed should beat Verified"
    );
}

#[test]
fn worse_result_verified_kept_when_new_is_verified() {
    let result = worse_result(
        Some(VerificationResult::Verified(None)),
        VerificationResult::Verified(None),
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Same-severity tie should keep current (Verified)"
    );
}

#[test]
fn worse_result_failed_kept_when_new_is_also_failed() {
    let cex1 = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let cex2 = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let result = worse_result(
        Some(VerificationResult::Failed(cex1)),
        VerificationResult::Failed(cex2),
    );
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Same-severity tie (Failed) should keep current"
    );
}

#[test]
fn worse_result_unknown_kept_when_new_is_assumed() {
    let result = worse_result(
        Some(VerificationResult::Unknown(UnknownReason::Unspecified)),
        VerificationResult::Assumed("axiom-only".into()),
    );
    assert!(
        matches!(result, VerificationResult::Unknown(_)),
        "Unknown (severity 2) should be kept over Assumed (severity 1)"
    );
}

// ── catch_unwind panic isolation tests (#1975) ─────────────────────────

#[test]
fn format_verification_summary_includes_panics_when_nonzero() {
    let c = VerificationCounters {
        verified: 3,
        panics: 2,
        ..VerificationCounters::default()
    };
    assert_eq!(
        format_verification_summary(&c, 0),
        "trust-wp: 3 verified, 0 failed, 0 errors, 2 panicked"
    );
}

#[test]
fn format_verification_summary_omits_panics_when_zero() {
    let c = VerificationCounters {
        verified: 5,
        ..VerificationCounters::default()
    };
    let s = format_verification_summary(&c, 0);
    assert!(
        !s.contains("panicked"),
        "should not include panicked when count is 0, got: {s}"
    );
}

#[test]
fn summary_exit_code_treats_panics_as_errors() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        verified: 3,
        panics: 1,
        ..Default::default()
    };
    assert_eq!(
        summary.exit_code(),
        2,
        "panics should produce exit code 2 (error category)"
    );
}

#[test]
fn summary_exit_code_failures_take_precedence_over_panics() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        verified: 3,
        failed: 1,
        panics: 2,
        ..Default::default()
    };
    assert_eq!(
        summary.exit_code(),
        1,
        "failures should take precedence over panics (exit code 1 > 2)"
    );
}

#[test]
fn summary_from_counters_maps_panics_field() {
    use crate::callbacks::reporting::{ProofAssertCounters, VerificationSummary};

    let counters = VerificationCounters {
        panics: 3,
        ..VerificationCounters::default()
    };
    let pa = ProofAssertCounters::default();
    let summary = VerificationSummary::from_counters(&counters, &pa);
    assert_eq!(
        summary.panics, 3,
        "panics must propagate through from_counters"
    );
}

// ─── unsoundness demotion reporting tests (#2106) ────────────────────────────

#[test]
fn summary_from_counters_maps_demoted_field() {
    use crate::callbacks::reporting::{ProofAssertCounters, VerificationSummary};

    let counters = VerificationCounters {
        demoted: 2,
        errors: 3,
        ..VerificationCounters::default()
    };
    let pa = ProofAssertCounters::default();
    let summary = VerificationSummary::from_counters(&counters, &pa);
    assert_eq!(
        summary.demoted, 2,
        "demoted must propagate through from_counters"
    );
}

#[test]
fn format_verification_summary_includes_demoted_when_nonzero() {
    let c = VerificationCounters {
        verified: 3,
        demoted: 2,
        ..VerificationCounters::default()
    };
    assert_eq!(
        format_verification_summary(&c, 0),
        "trust-wp: 3 verified, 0 failed, 0 errors, 2 demoted"
    );
}

#[test]
fn format_verification_summary_omits_demoted_when_zero() {
    let c = VerificationCounters {
        verified: 5,
        ..VerificationCounters::default()
    };
    let s = format_verification_summary(&c, 0);
    assert!(
        !s.contains("demoted"),
        "should not include demoted when count is 0, got: {s}"
    );
}

// ─── exit code soundness tests (#2120) ──────────────────────────────────────

#[test]
fn summary_exit_code_assumed_only_returns_2() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        assumed: 5,
        ..Default::default()
    };
    assert_eq!(
        summary.exit_code(),
        2,
        "assumed-only should produce exit code 2 to prevent false-accept (#2120)"
    );
}

#[test]
fn summary_exit_code_axiom_deps_only_returns_2() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        verified_with_axiom_deps: 3,
        ..Default::default()
    };
    assert_eq!(
        summary.exit_code(),
        2,
        "axiom-deps-only should produce exit code 2 (#2120)"
    );
}

#[test]
fn summary_exit_code_verified_with_axiom_deps_mixed_returns_2() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        verified: 2,
        verified_with_axiom_deps: 1,
        ..Default::default()
    };
    assert_eq!(
        summary.exit_code(),
        2,
        "mixed verified + axiom-deps must exit 2 so true-100 cannot hide axiom-dependent proofs"
    );
}

#[test]
fn summary_exit_code_unverified_axioms_returns_2() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        verified: 2,
        unverified_axioms: 1,
        ..Default::default()
    };
    assert_eq!(
        summary.exit_code(),
        2,
        "unverified logic postconditions are unproven axioms and must fail strict true-100"
    );
}

#[test]
fn summary_exit_code_mixed_assumed_and_vacuous_return_2() {
    use crate::callbacks::reporting::VerificationSummary;

    let assumed = VerificationSummary {
        verified: 2,
        assumed: 1,
        ..Default::default()
    };
    assert_eq!(
        assumed.exit_code(),
        2,
        "mixed verified + assumed must exit 2"
    );

    let vacuous = VerificationSummary {
        verified: 2,
        vacuous: 1,
        ..Default::default()
    };
    assert_eq!(
        vacuous.exit_code(),
        2,
        "mixed verified + vacuous must exit 2"
    );
}

#[test]
fn summary_exit_code_failures_take_precedence_over_assumed() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        failed: 1,
        assumed: 3,
        ..Default::default()
    };
    assert_eq!(
        summary.exit_code(),
        1,
        "failures should take precedence over assumed-only (exit 1 > 2)"
    );
}

#[test]
fn to_structured_result_preserves_proof_assert_wire_parity() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        verified: 1,
        proof_assert_failed: 2,
        proof_assert_errors: 1,
        ..Default::default()
    };

    let wire = summary.to_structured_result();

    assert_eq!(wire.verified, 1, "verified count must survive on the wire");
    assert_eq!(
        wire.proof_assert_failed, 2,
        "proof_assert failure count must survive on the wire"
    );
    assert_eq!(
        wire.proof_assert_errors, 1,
        "proof_assert error count must survive on the wire"
    );
    assert_eq!(
        wire.base_exit_code, 1,
        "wire exit code must match driver summary precedence when proof_assert fails"
    );
}

#[test]
fn rustc_process_exit_code_defers_proof_assert_failures_to_wire() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        verified: 1,
        proof_assert_failed: 2,
        proof_assert_errors: 1,
        ..Default::default()
    };

    assert_eq!(
        summary.exit_code(),
        1,
        "structured wire summary must still report proof_assert failure"
    );
    assert_eq!(
        summary.rustc_process_exit_code(),
        0,
        "rustc wrapper process should let cargo finish so cargo-trust-wp can aggregate proof_assert counters"
    );
}

#[test]
fn rustc_process_exit_code_keeps_function_failures_fatal() {
    use crate::callbacks::reporting::VerificationSummary;

    let failed = VerificationSummary {
        verified: 1,
        failed: 1,
        proof_assert_failed: 1,
        ..Default::default()
    };
    assert_eq!(failed.rustc_process_exit_code(), 1);

    let errored = VerificationSummary {
        verified: 1,
        errors: 1,
        proof_assert_errors: 1,
        ..Default::default()
    };
    assert_eq!(errored.rustc_process_exit_code(), 2);
}

#[test]
fn rustc_process_exit_code_defers_trusted_skipped_to_wire() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        trusted: 39,
        skipped: 4,
        ..Default::default()
    };

    assert_eq!(
        summary.exit_code(),
        2,
        "structured wire summary must keep trusted/skipped as non-proofs"
    );
    assert_eq!(
        summary.rustc_process_exit_code(),
        0,
        "rustc wrapper process must not abort dependency compilation before target verification runs"
    );
}

/// Comprehensive field-mapping test: every VerificationSummary field that
/// maps to the wire must land on the correct StructuredVerificationResult
/// field. Uses distinct non-zero values so that any swap or misalignment
/// is caught immediately.
#[test]
fn to_structured_result_maps_all_fields_correctly() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        verified: 10,
        failed: 3,
        errors: 2,
        skipped: 7,
        trusted: 5,
        assumed: 4,
        warnings: 6,
        verified_with_axiom_deps: 8,
        unverified_axioms: 16,
        vacuous: 15,
        evidence_gaps: 17,
        proof_assert_verified: 9,
        proof_assert_failed: 11,
        proof_assert_errors: 12,
        panics: 13,
        demoted: 14,
        ..Default::default()
    };

    let wire = summary.to_structured_result();

    // Computed field: failed > 0 → exit code 1
    assert_eq!(wire.base_exit_code, 1, "base_exit_code");

    // Direct mappings (usize → u64)
    assert_eq!(wire.verified, 10, "verified");
    assert_eq!(wire.failed, 3, "failed");
    assert_eq!(wire.errors, 2, "errors");
    assert_eq!(wire.warnings, 6, "warnings");
    assert_eq!(wire.assumed, 4, "assumed");
    assert_eq!(wire.trusted, 5, "trusted");
    assert_eq!(wire.skipped, 7, "skipped");
    assert_eq!(wire.verified_with_axiom_deps, 8, "verified_with_axiom_deps");
    assert_eq!(wire.unverified_axioms, 16, "unverified_axioms");
    assert_eq!(wire.vacuous, 15, "vacuous");
    assert_eq!(wire.evidence_gaps, 17, "evidence_gaps");
    assert_eq!(wire.proof_assert_verified, 9, "proof_assert_verified");
    assert_eq!(wire.proof_assert_failed, 11, "proof_assert_failed");
    assert_eq!(wire.proof_assert_errors, 12, "proof_assert_errors");
    assert_eq!(wire.panics, 13, "panics");
    assert_eq!(wire.demoted, 14, "demoted");

    // Hardcoded zeros — fatal counters are overlaid at emission time,
    // not sourced from VerificationSummary.
    assert_eq!(wire.parse_errors, 0, "parse_errors must be hardcoded zero");
    assert_eq!(
        wire.termination_errors, 0,
        "termination_errors must be hardcoded zero"
    );
    assert_eq!(
        wire.logic_recursion_errors, 0,
        "logic_recursion_errors must be hardcoded zero"
    );
}

#[test]
fn is_axiom_deps_only_true_when_only_axiom_deps() {
    use crate::callbacks::reporting::{ProofAssertCounters, VerificationSummary};

    let counters = VerificationCounters {
        verified_with_axiom_deps: 4,
        ..VerificationCounters::default()
    };
    let pa = ProofAssertCounters::default();
    let summary = VerificationSummary::from_counters(&counters, &pa);
    assert!(
        summary.is_axiom_deps_only(),
        "should be axiom-deps-only when no verified/assumed/failed/errors"
    );
}

#[test]
fn is_axiom_deps_only_false_when_verified_present() {
    use crate::callbacks::reporting::{ProofAssertCounters, VerificationSummary};

    let counters = VerificationCounters {
        verified: 1,
        verified_with_axiom_deps: 2,
        ..VerificationCounters::default()
    };
    let pa = ProofAssertCounters::default();
    let summary = VerificationSummary::from_counters(&counters, &pa);
    assert!(
        !summary.is_axiom_deps_only(),
        "should not be axiom-deps-only when verified > 0"
    );
}

// ─── orphaned invariant/variant error tests (#2122) ──────────────────────────
//
// Orphaned #[invariant] and #[variant] attributes on functions without loops
// must increment `counters.errors` (producing exit code 2), not `counters.skipped`.

#[test]
fn summary_exit_code_orphaned_invariants_produce_errors_not_skipped() {
    use crate::callbacks::reporting::VerificationSummary;

    // Simulate the counters state after orphaned invariants are detected:
    // they are counted as errors (exit code 2), not as skipped.
    let summary = VerificationSummary {
        errors: 1,
        ..Default::default()
    };
    assert_eq!(
        summary.exit_code(),
        2,
        "orphaned invariants must produce exit code 2 (#2122)"
    );
}

#[test]
fn summary_exit_code_skipped_only_returns_2() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        skipped: 1,
        ..Default::default()
    };
    assert_eq!(
        summary.exit_code(),
        2,
        "skipped-only is not a clean proof and must fail strict true-100"
    );
}

#[test]
fn summary_exit_code_definition_registered_only_returns_0() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary::default();
    let wire = summary.to_structured_result();

    assert_eq!(
        summary.exit_code(),
        0,
        "definition-only logic registration should not be modeled as a soundness gap"
    );
    assert_eq!(wire.base_exit_code, 0, "wire base_exit_code");
    assert_eq!(
        wire.skipped, 0,
        "definition-only logic must not increment skipped"
    );
    assert_eq!(
        wire.trusted, 0,
        "definition-only logic must not increment trusted"
    );
    assert_eq!(
        wire.unverified_axioms, 0,
        "bare logic definitions have no unverified postcondition axiom"
    );
}

#[test]
fn summary_exit_code_trusted_only_returns_2() {
    use crate::callbacks::reporting::VerificationSummary;

    let summary = VerificationSummary {
        trusted: 1,
        ..Default::default()
    };
    assert_eq!(
        summary.exit_code(),
        2,
        "trusted-only is not a clean proof and must fail strict true-100"
    );
}

// ---------------------------------------------------------------------------
// Refutation authority: no FAILED without a validated counterexample model.
//
// Both halves must fail if the rule is reverted — the withholding half AND the
// honest half, so the fix can never be "withhold everything".
// ---------------------------------------------------------------------------

/// A SAT snapshot ay validated and accepted: the shape of an honest refutation.
fn validated_sat_provenance() -> trust_wp_ay::VerificationProvenance {
    let mut evidence = trust_wp_ay::SolveEvidenceSnapshot::default();
    evidence.result = "sat".to_string();
    evidence.model_validated = true;
    evidence.accepted_for_consumer = true;
    evidence.verification.sat_model_validated = true;
    evidence.verification_level = trust_wp_ay::SolveVerificationLevelSnapshot::FullyVerified;
    trust_wp_ay::VerificationProvenance::with_solve_time(std::time::Duration::from_millis(11))
        .with_assertion_count(4)
        .with_solve_evidence(Some(evidence))
}

/// `invariant_moves` in one test: a loop call obligation refuted on
/// `ay_result=trust-wp-structural-provenance accepted_for_consumer=false
/// model_validated=false` is NOT a counterexample. It must classify as the
/// error channel (unknown), never the failed channel.
#[test]
fn classify_obligation_outcome_failed_without_validated_model_is_unknown() {
    let (outcome, delta_failed, delta_errors, delta_demoted, delta_evidence_gaps, delta_warnings) =
        classify_obligation_outcome(
            VerificationOutcome::without_provenance(VerificationResult::Failed(
                Counterexample::empty(),
            )),
            "test::fn",
            "test.rs:1",
        );
    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(
        delta_failed, 0,
        "an unvalidated refutation must NOT increment failed"
    );
    assert_eq!(
        delta_errors, 1,
        "it is an inconclusive: count it as an error"
    );
    assert_eq!(delta_demoted, 0);
    assert_eq!(delta_evidence_gaps, 0, "this is not a Verified-side gap");
    assert_eq!(delta_warnings, 0);
}

/// The honest path, pinned: a refutation ay computed AND validated still
/// counts as failed. If this flips, the rule has been over-applied.
#[test]
fn classify_obligation_outcome_failed_with_validated_model_stays_failed() {
    let (outcome, delta_failed, delta_errors, delta_demoted, delta_evidence_gaps, delta_warnings) =
        classify_obligation_outcome(
            VerificationOutcome::new(
                VerificationResult::Failed(Counterexample::empty()),
                Some(validated_sat_provenance()),
            ),
            "test::fn",
            "test.rs:1",
        );
    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(
        delta_failed, 1,
        "a validated counterexample is a real refutation and must stay failed"
    );
    assert_eq!(delta_errors, 0);
    assert_eq!(delta_demoted, 0);
    assert_eq!(delta_evidence_gaps, 0);
    assert_eq!(delta_warnings, 0);
}

/// `unknown` must never be counted as verified — the one guarantee the
/// withheld-refutation policy rests on (D-27).
#[test]
fn a_withheld_refutation_is_never_verified() {
    let (outcome, ..) = classify_obligation_outcome(
        VerificationOutcome::without_provenance(
            VerificationResult::Failed(Counterexample::empty()),
        ),
        "test::fn",
        "test.rs:1",
    );
    assert_ne!(outcome, ObligationOutcome::Verified);
    assert_ne!(outcome, ObligationOutcome::Vacuous);
    assert!(!matches!(outcome, ObligationOutcome::Assumed(_)));
}

// ---------------------------------------------------------------------------
// The mirror-image guard for withheld refutations (D-27).
//
// Withholding moves verdicts OUT of `failed`. Every one of them must land in
// `unknown`, and `unknown` must never be readable as success — not in the
// counters, not in the exit code. These tests fail if it ever becomes one.
// ---------------------------------------------------------------------------

/// A withheld refutation is an `Unknown`, so it takes the `Unknown` arm:
/// errors +1, failed +0, verified untouched.
#[test]
fn a_withheld_refutation_is_counted_as_an_error_never_as_verified() {
    let (outcome, delta_failed, delta_errors, delta_demoted) = classify_obligation_result(
        VerificationResult::Unknown(UnknownReason::SolverMessage(format!(
            "{}: {}",
            trust_wp_ay::REFUTATION_AUTHORITY_MESSAGE,
            trust_wp_ay::INJECTED_FAIL_CLOSED_GOAL_REASON
        ))),
        "test::fn",
        "test.rs:1",
    );
    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_ne!(
        outcome,
        ObligationOutcome::Verified,
        "a withheld refutation must never be credited as a proof"
    );
    assert_eq!(delta_failed, 0);
    assert_eq!(delta_errors, 1);
    assert_eq!(delta_demoted, 0);
}

/// And the crate exit stays nonzero on it. `unknown` is exit 2 — an error or
/// soundness gap — never the exit 0 a clean proof earns.
#[test]
fn a_crate_whose_only_verdict_was_withheld_never_exits_zero() {
    use crate::callbacks::reporting::{ProofAssertCounters, VerificationSummary};

    let withheld_only = VerificationCounters {
        errors: 1,
        refutations_withheld: 1,
        ..VerificationCounters::default()
    };
    assert_eq!(withheld_only.verified, 0);
    assert_eq!(withheld_only.failed, 0);
    let summary =
        VerificationSummary::from_counters(&withheld_only, &ProofAssertCounters::default());
    assert_eq!(
        summary.exit_code(),
        2,
        "an inconclusive crate exits 2, never 0"
    );
    assert_eq!(summary.rustc_process_exit_code(), 2);

    // A crate that proved everything else but withheld one refutation is still
    // not a clean proof.
    let mixed = VerificationCounters {
        verified: 9,
        errors: 1,
        refutations_withheld: 1,
        ..VerificationCounters::default()
    };
    let mixed_summary = VerificationSummary::from_counters(&mixed, &ProofAssertCounters::default());
    assert_eq!(mixed_summary.exit_code(), 2);
    assert_ne!(mixed_summary.exit_code(), 0);
}
