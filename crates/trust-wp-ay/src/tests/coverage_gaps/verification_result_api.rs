// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// `VerificationResult::unknown` constructor creates Unknown with reason.
#[test]
#[timeout(30000)]
fn test_verification_result_unknown_with_reason() {
    let result = VerificationResult::unknown(UnknownReason::Timeout);
    assert!(
        matches!(&result, VerificationResult::Unknown(UnknownReason::Timeout)),
        "unknown(Timeout) should create Unknown(Timeout): got {result:?}"
    );
}

/// `unknown_reason` returns reason for Unknown variant.
#[test]
#[timeout(30000)]
fn test_verification_result_unknown_reason_returns_str() {
    let result = VerificationResult::unknown(UnknownReason::Incomplete);
    assert_eq!(
        result.unknown_reason(),
        Some(&UnknownReason::Incomplete),
        "Unknown(Incomplete) should return reason Incomplete"
    );
}

/// `unknown_reason` returns None for non-Unknown variants.
#[test]
#[timeout(30000)]
fn test_verification_result_unknown_reason_returns_none_for_verified() {
    assert_eq!(
        VerificationResult::Verified(None).unknown_reason(),
        None,
        "Verified variant should have no unknown_reason"
    );
}

/// `unknown_reason` returns None for Failed variant.
#[test]
#[timeout(30000)]
fn test_verification_result_unknown_reason_returns_none_for_failed() {
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let result = VerificationResult::Failed(cex);
    assert_eq!(
        result.unknown_reason(),
        None,
        "Failed variant should have no unknown_reason"
    );
}

/// `overall()` returns Verified when all sub-results are Verified.
#[test]
#[timeout(30000)]
fn test_loop_overall_all_verified() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        matches!(result.overall(), VerificationResult::Verified(_)),
        "all-Verified should produce Verified overall"
    );
}

/// `overall()` returns Failed when initialization fails.
#[test]
#[timeout(30000)]
fn test_loop_overall_init_failed() {
    let cex = Counterexample {
        values: vec![CounterexampleValue {
            name: "i".to_string(),
            value: CounterexampleType::Int(0.into()),
            origin: None,
        }],
        violated_postcondition: None,
    };
    let result = LoopVerificationResult {
        initialization: VerificationResult::Failed(cex),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        matches!(result.overall(), VerificationResult::Failed(_)),
        "Failed init should dominate overall result"
    );
}

/// `overall()` returns Unknown with reason when preservation is Unknown.
#[test]
#[timeout(30000)]
fn test_loop_overall_preservation_unknown_propagates_reason() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Unknown(UnknownReason::SolverPanic(
            "Sort mismatch".to_string(),
        )),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    let overall = result.overall();
    match &overall {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("Sort mismatch"),
                "overall() must propagate the unknown reason from sub-results: got {reason}"
            );
        }
        other => panic!("expected Unknown with reason propagation, got: {other:?}"),
    }
}

/// `overall()` returns Failed when variant_decrease fails (priority over Unknown).
#[test]
#[timeout(30000)]
fn test_loop_overall_variant_decrease_failed() {
    let cex = Counterexample {
        values: vec![CounterexampleValue {
            name: "v".to_string(),
            value: CounterexampleType::Int(5.into()),
            origin: None,
        }],
        violated_postcondition: None,
    };
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: Some(VerificationResult::Failed(cex)),
    };
    assert!(
        matches!(result.overall(), VerificationResult::Failed(_)),
        "Failed variant_decrease should dominate even when base conditions pass"
    );
}

/// `induction_passed()` returns true when init + preservation pass,
/// regardless of postcondition (#2085).
#[test]
#[timeout(30000)]
fn test_loop_induction_passed_ignores_postcondition() {
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Failed(cex),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        result.induction_passed(),
        "induction_passed() should be true when init+preservation pass even if postcondition fails"
    );
    assert!(
        !result.all_passed(),
        "all_passed() should be false when postcondition fails"
    );
}

/// `induction_passed()` returns false when init fails.
#[test]
#[timeout(30000)]
fn test_loop_induction_passed_false_when_init_fails() {
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let result = LoopVerificationResult {
        initialization: VerificationResult::Failed(cex),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        !result.induction_passed(),
        "induction_passed() should be false when init fails"
    );
}

/// `induction_passed()` returns false when preservation fails.
#[test]
#[timeout(30000)]
fn test_loop_induction_passed_false_when_preservation_fails() {
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Failed(cex),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        !result.induction_passed(),
        "induction_passed() should be false when preservation fails"
    );
}

/// `induction_passed()` includes variant checks.
#[test]
#[timeout(30000)]
fn test_loop_induction_passed_includes_variant() {
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: Some(VerificationResult::Failed(cex)),
    };
    assert!(
        !result.induction_passed(),
        "induction_passed() should be false when variant_decrease fails"
    );
}

/// `all_verified()` returns false when variant conditions are inconsistent.
#[test]
#[timeout(30000)]
fn test_loop_all_verified_inconsistent_variants() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: None, // inconsistent: nonneg present but decrease absent
    };
    assert!(
        !result.all_verified(),
        "inconsistent variant conditions (Some, None) should not count as all_verified"
    );
}

// ── Assumed variant tests (#1889) ─────────────────────────────────────

/// `overall()` returns Assumed when all conditions pass but some are Assumed (#1889).
#[test]
#[timeout(30000)]
fn test_loop_overall_propagates_assumed_reason() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("axiom-only function".to_string()),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    let overall = result.overall();
    match &overall {
        VerificationResult::Assumed(reason) => {
            assert!(
                reason.contains("axiom-only"),
                "overall() must propagate Assumed reason from sub-results: got {reason}"
            );
        }
        other => panic!("expected Assumed, got: {other:?}"),
    }
}

/// `overall()` returns first Assumed reason when multiple sub-results are Assumed.
#[test]
#[timeout(30000)]
fn test_loop_overall_first_assumed_wins() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("first reason".to_string()),
        preservation: VerificationResult::Assumed("second reason".to_string()),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    let overall = result.overall();
    match &overall {
        VerificationResult::Assumed(reason) => {
            assert_eq!(
                reason, "first reason",
                "overall() should propagate the FIRST Assumed reason"
            );
        }
        other => panic!("expected Assumed, got: {other:?}"),
    }
}

/// `overall()` returns Failed even when other conditions are Assumed.
/// Failed has highest precedence.
#[test]
#[timeout(30000)]
fn test_loop_overall_failed_beats_assumed() {
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("axiom-only".to_string()),
        preservation: VerificationResult::Failed(cex),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        matches!(result.overall(), VerificationResult::Failed(_)),
        "Failed should take precedence over Assumed"
    );
}

/// `overall()` returns Unknown over Assumed when both present.
/// Unknown has higher precedence than Assumed.
#[test]
#[timeout(30000)]
fn test_loop_overall_unknown_beats_assumed() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("axiom-only".to_string()),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Unknown(UnknownReason::Timeout),
        variant_nonneg: None,
        variant_decrease: None,
    };
    let overall = result.overall();
    assert!(
        matches!(
            &overall,
            VerificationResult::Unknown(UnknownReason::Timeout)
        ),
        "Unknown should take precedence over Assumed: got {overall:?}"
    );
}

/// `all_passed()` returns true when some conditions are Assumed.
#[test]
#[timeout(30000)]
fn test_loop_all_passed_includes_assumed() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("axiom-only".to_string()),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        result.all_passed(),
        "all_passed() should be true when some conditions are Assumed"
    );
    assert!(
        !result.all_verified(),
        "all_verified() should be false when any condition is Assumed"
    );
}

/// `induction_passed()` requires real verified init and preservation phases.
#[test]
#[timeout(30000)]
fn test_loop_induction_passed_rejects_assumed() {
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("axiom-only".to_string()),
        preservation: VerificationResult::Assumed("axiom-only".to_string()),
        postcondition: VerificationResult::Failed(cex),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        !result.induction_passed(),
        "induction_passed() should be false when init+preservation are Assumed"
    );
}

/// `overall()` returns Unknown(Unspecified) when no reason is present.
#[test]
#[timeout(30000)]
fn test_loop_overall_unknown_unspecified_detected() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Unknown(UnknownReason::Unspecified),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    let overall = result.overall();
    assert!(
        matches!(
            overall,
            VerificationResult::Unknown(UnknownReason::Unspecified)
        ),
        "Unknown(Unspecified) should propagate through overall(): got {overall:?}"
    );
}

/// `overall()` returns Assumed from variant_nonneg when base conditions are Verified.
#[test]
#[timeout(30000)]
fn test_loop_overall_assumed_from_variant() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Assumed("variant axiom".to_string())),
        variant_decrease: Some(VerificationResult::Verified(None)),
    };
    let overall = result.overall();
    match &overall {
        VerificationResult::Assumed(reason) => {
            assert!(
                reason.contains("variant axiom"),
                "Assumed from variant_nonneg should propagate: got {reason}"
            );
        }
        other => panic!("expected Assumed from variant, got: {other:?}"),
    }
}

// ── Asymmetric variant state tests (#2306) ────────────────────────────

/// Asymmetric variant state (Some, None) keeps helper APIs and `overall()`
/// fail-closed in sync.
#[test]
#[timeout(30000)]
fn test_loop_overall_asymmetric_variant_nonneg_present_decrease_absent() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: None,
    };
    assert!(
        !result.all_passed(),
        "asymmetric variant state (Some, None) should not count as all_passed"
    );
    assert!(
        !result.all_verified(),
        "asymmetric variant state (Some, None) should not count as all_verified"
    );
    let overall = result.overall();
    match &overall {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("inconsistent loop variant state"),
                "asymmetric variant state should produce Unknown with inconsistency reason: got {reason}"
            );
        }
        other => panic!("expected Unknown for asymmetric variant (Some, None), got: {other:?}"),
    }
}

/// Asymmetric variant state (None, Some) keeps helper APIs and `overall()`
/// fail-closed in sync.
#[test]
#[timeout(30000)]
fn test_loop_overall_asymmetric_variant_nonneg_absent_decrease_present() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: Some(VerificationResult::Verified(None)),
    };
    assert!(
        !result.all_passed(),
        "asymmetric variant state (None, Some) should not count as all_passed"
    );
    assert!(
        !result.all_verified(),
        "asymmetric variant state (None, Some) should not count as all_verified"
    );
    let overall = result.overall();
    match &overall {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("inconsistent loop variant state"),
                "asymmetric variant state should produce Unknown with inconsistency reason: got {reason}"
            );
        }
        other => panic!("expected Unknown for asymmetric variant (None, Some), got: {other:?}"),
    }
}

/// `overall()` returns Failed (not Unknown) when asymmetric variant has a failure.
/// Failed has highest precedence, even over asymmetric detection.
#[test]
#[timeout(30000)]
fn test_loop_overall_asymmetric_variant_with_failure_returns_failed() {
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Failed(cex)),
        variant_decrease: None,
    };
    assert!(
        matches!(result.overall(), VerificationResult::Failed(_)),
        "Failed variant_nonneg should take precedence over asymmetric detection"
    );
}

// --- UnknownReason typed enum tests (#1751) ---

/// `UnknownReason::from_solver_reason` parses known reason strings.
#[test]
#[timeout(30000)]
fn test_unknown_reason_from_solver_reason_known_strings() {
    assert_eq!(
        UnknownReason::from_solver_reason(Some("timeout".to_string())),
        UnknownReason::Timeout
    );
    assert_eq!(
        UnknownReason::from_solver_reason(Some("incomplete".to_string())),
        UnknownReason::Incomplete
    );
    assert_eq!(
        UnknownReason::from_solver_reason(Some("quantifiers".to_string())),
        UnknownReason::Quantifiers
    );
    assert_eq!(
        UnknownReason::from_solver_reason(Some("sat".to_string())),
        UnknownReason::SatModel
    );
    assert_eq!(
        UnknownReason::from_solver_reason(Some("memout".to_string())),
        UnknownReason::MemoryOut
    );
}

/// `UnknownReason::from_solver_reason(None)` returns `Unspecified`.
#[test]
#[timeout(30000)]
fn test_unknown_reason_from_solver_reason_none() {
    assert_eq!(
        UnknownReason::from_solver_reason(None),
        UnknownReason::Unspecified
    );
}

/// Unknown solver strings become `SolverMessage`.
#[test]
#[timeout(30000)]
fn test_unknown_reason_from_solver_reason_unknown_string() {
    match UnknownReason::from_solver_reason(Some("some-new-reason".to_string())) {
        UnknownReason::SolverMessage(msg) => assert_eq!(msg, "some-new-reason"),
        other => panic!("expected SolverMessage, got: {other:?}"),
    }
}

/// `as_str` round-trips known variants.
#[test]
#[timeout(30000)]
fn test_unknown_reason_as_str() {
    assert_eq!(UnknownReason::Timeout.as_str(), "timeout");
    assert_eq!(UnknownReason::Incomplete.as_str(), "incomplete");
    assert_eq!(UnknownReason::Quantifiers.as_str(), "quantifiers");
    assert_eq!(UnknownReason::SatModel.as_str(), "sat");
    assert_eq!(UnknownReason::MemoryOut.as_str(), "memout");
    assert_eq!(UnknownReason::Unspecified.as_str(), "unknown");
    assert_eq!(
        UnknownReason::Demoted("demoted: approx".to_string()).as_str(),
        "demoted: approx"
    );
    assert_eq!(
        UnknownReason::SolverPanic("ay panic".to_string()).as_str(),
        "ay panic"
    );
    assert_eq!(
        UnknownReason::SolverMessage("custom".to_string()).as_str(),
        "custom"
    );
}

/// `to_option_string` produces None for Unspecified, Some for others.
#[test]
#[timeout(30000)]
fn test_unknown_reason_to_option_string() {
    assert_eq!(UnknownReason::Unspecified.to_option_string(), None);
    assert_eq!(
        UnknownReason::Timeout.to_option_string(),
        Some("timeout".to_string())
    );
    assert_eq!(
        UnknownReason::Demoted("detail".to_string()).to_option_string(),
        Some("detail".to_string())
    );
}

/// `Display` implementation matches `as_str`.
#[test]
#[timeout(30000)]
fn test_unknown_reason_display() {
    assert_eq!(format!("{}", UnknownReason::Timeout), "timeout");
    assert_eq!(format!("{}", UnknownReason::Unspecified), "unknown");
    assert_eq!(
        format!("{}", UnknownReason::SolverPanic("crash".to_string())),
        "crash"
    );
}

/// `from_solver_reason_ref` works with borrowed strings.
#[test]
#[timeout(30000)]
fn test_unknown_reason_from_solver_reason_ref() {
    assert_eq!(
        UnknownReason::from_solver_reason_ref(Some("timeout")),
        UnknownReason::Timeout
    );
    assert_eq!(
        UnknownReason::from_solver_reason_ref(None),
        UnknownReason::Unspecified
    );
    match UnknownReason::from_solver_reason_ref(Some("novel")) {
        UnknownReason::SolverMessage(msg) => assert_eq!(msg, "novel"),
        other => panic!("expected SolverMessage, got: {other:?}"),
    }
}

// --- Proof certificate tests (#2629) ---

/// UNSAT result from the solver carries a proof certificate with
/// `strict_verified: true` when proof production is enabled.
///
/// The production encoder keeps proof production off by default for solver
/// throughput, so this test opts in explicitly. Use pure EUF equality
/// transitivity: latest ay may route `Int` equality through arithmetic proof
/// reconstruction and expose that as a diagnostic trust step, while pure EUF
/// remains a strict, trust-free proof artifact.
#[test]
#[timeout(30000)]
fn test_verified_result_carries_proof_certificate() {
    use crate::encoder::AYEncoder;

    let mut encoder = AYEncoder::new();
    encoder.solver_mut().set_produce_proofs(true);
    let proof_sort = ay_dpll::api::Sort::Uninterpreted("ProofWitness".to_string());
    let a = encoder
        .solver_mut()
        .declare_const("proof_a", proof_sort.clone());
    let b = encoder
        .solver_mut()
        .declare_const("proof_b", proof_sort.clone());
    let c = encoder.solver_mut().declare_const("proof_c", proof_sort);
    let a_eq_b = encoder.solver_mut().eq(a, b);
    let b_eq_c = encoder.solver_mut().eq(b, c);
    let a_eq_c = encoder.solver_mut().eq(a, c);
    let not_a_eq_c = encoder.solver_mut().not(a_eq_c);
    encoder.assert_term(a_eq_b);
    encoder.assert_term(b_eq_c);
    encoder.assert_term(not_a_eq_c);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "a=b AND b=c AND NOT(a=c) should be UNSAT: got {result:?}"
    );

    // Extract proof artifact — should be available after UNSAT.
    let artifact = encoder.solver().export_last_unsat_artifact();
    assert!(
        artifact.is_some(),
        "UNSAT result should produce a proof artifact when proof production is enabled"
    );

    let artifact = artifact.unwrap();
    let summary = ProofCertificateSummary {
        strict_verified: matches!(
            artifact.strict_verdict,
            ay_dpll::api::StrictProofVerdict::Verified(_)
        ),
        restricted_rule_subset: artifact.restricted_rule_subset,
        trust_count: artifact.quality.trust_count,
        trust_fallback_count: artifact.quality.trust_fallback_count,
        hole_count: artifact.quality.hole_count,
        theory_lemma_count: artifact.quality.theory_lemma_count,
        resolution_count: artifact.quality.resolution_count,
        farkas_certificate_count: u32::try_from(artifact.farkas_certificates.len())
            .unwrap_or(u32::MAX),
        lrat_present: artifact.lrat_certificate.is_some(),
        alethe_text: Some(artifact.alethe.clone()),
    };
    assert!(
        summary.strict_verified,
        "equality transitivity UNSAT proof should pass strict verification: summary={summary:?}"
    );
    assert_eq!(
        summary.trust_count, 0,
        "equality transitivity UNSAT proof should have zero trust steps"
    );
}

/// `VerificationResult::verified()` convenience constructor creates
/// `Verified(None)`.
#[test]
#[timeout(30000)]
fn test_verified_convenience_constructor_none() {
    let result = VerificationResult::verified();
    assert!(
        matches!(result, VerificationResult::Verified(None)),
        "verified() should create Verified(None): got {result:?}"
    );
}

/// `VerificationResult::verified_with_proof()` constructor wraps summary.
#[test]
#[timeout(30000)]
fn test_verified_with_proof_constructor() {
    let summary = ProofCertificateSummary {
        strict_verified: true,
        restricted_rule_subset: false,
        trust_count: 0,
        trust_fallback_count: 0,
        hole_count: 0,
        theory_lemma_count: 0,
        resolution_count: 42,
        farkas_certificate_count: 0,
        lrat_present: false,
        alethe_text: None,
    };
    let result = VerificationResult::verified_with_proof(summary);
    match &result {
        VerificationResult::Verified(Some(s)) => {
            assert!(s.strict_verified);
            assert!(!s.restricted_rule_subset);
            assert_eq!(s.trust_count, 0);
            assert_eq!(s.resolution_count, 42);
            assert!(s.is_fully_verified());
        }
        other => panic!("expected Verified(Some(...)), got {other:?}"),
    }
}

/// The retired boolean cannot disable proof authority.
#[test]
#[timeout(30000)]
fn test_apply_strict_trust_disabled_still_downgrades_unverified_proof() {
    let summary = ProofCertificateSummary {
        strict_verified: false,
        restricted_rule_subset: false,
        trust_count: 5,
        trust_fallback_count: 2,
        hole_count: 1,
        theory_lemma_count: 3,
        resolution_count: 10,
        farkas_certificate_count: 0,
        lrat_present: false,
        alethe_text: None,
    };
    let before = VerificationResult::verified_with_proof(summary);
    let after = before.apply_strict_trust(false);
    assert!(matches!(
        after,
        VerificationResult::Unknown(UnknownReason::ProofTrusted)
    ));
}

/// `apply_strict_trust(true)` downgrades Verified with trust_count > 0.
#[test]
#[timeout(30000)]
fn test_apply_strict_trust_downgrades_unverified_proof() {
    let summary = ProofCertificateSummary {
        strict_verified: false,
        restricted_rule_subset: false,
        trust_count: 3,
        trust_fallback_count: 0,
        hole_count: 0,
        theory_lemma_count: 0,
        resolution_count: 5,
        farkas_certificate_count: 0,
        lrat_present: false,
        alethe_text: None,
    };
    let before = VerificationResult::verified_with_proof(summary);
    let after = before.apply_strict_trust(true);
    assert!(
        matches!(
            after,
            VerificationResult::Unknown(UnknownReason::ProofTrusted)
        ),
        "expected downgrade to Unknown(ProofTrusted), got {after:?}"
    );
}

/// `apply_strict_trust(true)` leaves fully-verified proofs alone.
#[test]
#[timeout(30000)]
fn test_apply_strict_trust_preserves_fully_verified() {
    let summary = ProofCertificateSummary {
        strict_verified: true,
        restricted_rule_subset: true,
        trust_count: 0,
        trust_fallback_count: 0,
        hole_count: 0,
        theory_lemma_count: 0,
        resolution_count: 5,
        farkas_certificate_count: 1,
        lrat_present: true,
        alethe_text: None,
    };
    let before = VerificationResult::verified_with_proof(summary);
    let after = before.apply_strict_trust(true);
    assert!(matches!(after, VerificationResult::Verified(Some(_))));
}

/// Missing proof evidence cannot confer verified authority.
#[test]
#[timeout(30000)]
fn test_apply_strict_trust_downgrades_verified_without_cert() {
    let before = VerificationResult::verified();
    let after = before.apply_strict_trust(true);
    assert!(matches!(
        after,
        VerificationResult::Unknown(UnknownReason::ProofTrusted)
    ));
}

// --- Alethe proof text capture tests (Phase 1 — soundness, #soundness) ---

/// `with_alethe_text` attaches rendered proof text to a default summary.
#[test]
#[timeout(30000)]
fn test_proof_summary_with_alethe_text_builder_attaches_text() {
    let summary = ProofCertificateSummary {
        strict_verified: true,
        restricted_rule_subset: false,
        trust_count: 0,
        trust_fallback_count: 0,
        hole_count: 0,
        theory_lemma_count: 0,
        resolution_count: 1,
        farkas_certificate_count: 0,
        lrat_present: false,
        alethe_text: None,
    }
    .with_alethe_text("(step t1 (cl) :rule resolution)".to_string());
    assert_eq!(
        summary.alethe_text.as_deref(),
        Some("(step t1 (cl) :rule resolution)"),
        "with_alethe_text should populate the alethe_text field"
    );
}

/// `with_alethe_text` replaces any previously attached text (last write wins).
#[test]
#[timeout(30000)]
fn test_proof_summary_with_alethe_text_overwrites_previous() {
    let summary = ProofCertificateSummary {
        strict_verified: true,
        restricted_rule_subset: false,
        trust_count: 0,
        trust_fallback_count: 0,
        hole_count: 0,
        theory_lemma_count: 0,
        resolution_count: 1,
        farkas_certificate_count: 0,
        lrat_present: false,
        alethe_text: Some("old".to_string()),
    }
    .with_alethe_text("new".to_string());
    assert_eq!(summary.alethe_text.as_deref(), Some("new"));
}

/// Default field state: a struct-literal `ProofCertificateSummary` with
/// `alethe_text: None` reflects "no proof text captured" — the production
/// codepath sets this to `Some(...)` only when the artifact is exported.
#[test]
#[timeout(30000)]
fn test_proof_summary_alethe_text_default_is_none() {
    let summary = ProofCertificateSummary {
        strict_verified: true,
        restricted_rule_subset: false,
        trust_count: 0,
        trust_fallback_count: 0,
        hole_count: 0,
        theory_lemma_count: 0,
        resolution_count: 1,
        farkas_certificate_count: 0,
        lrat_present: false,
        alethe_text: None,
    };
    assert!(summary.alethe_text.is_none());
}

/// `is_fully_verified()` ignores `alethe_text` — verdict depends only on
/// trust/hole/strict fields, not on whether proof text was captured.
#[test]
#[timeout(30000)]
fn test_proof_summary_is_fully_verified_ignores_alethe_text() {
    let without_text = ProofCertificateSummary {
        strict_verified: true,
        restricted_rule_subset: false,
        trust_count: 0,
        trust_fallback_count: 0,
        hole_count: 0,
        theory_lemma_count: 0,
        resolution_count: 2,
        farkas_certificate_count: 0,
        lrat_present: false,
        alethe_text: None,
    };
    let with_text = without_text
        .clone()
        .with_alethe_text("(step t1 (cl) :rule resolution)".to_string());
    let with_empty_text = without_text.clone().with_alethe_text(String::new());

    assert!(
        without_text.is_fully_verified(),
        "fully-verified summary without text should still be fully verified"
    );
    assert_eq!(
        without_text.is_fully_verified(),
        with_text.is_fully_verified(),
        "alethe_text presence must not change is_fully_verified verdict"
    );
    assert_eq!(
        without_text.is_fully_verified(),
        with_empty_text.is_fully_verified(),
        "empty alethe_text must not change is_fully_verified verdict"
    );

    // And the inverse: a trusted proof stays trusted whether or not text is
    // captured.
    let trusted = ProofCertificateSummary {
        strict_verified: false,
        restricted_rule_subset: false,
        trust_count: 4,
        trust_fallback_count: 1,
        hole_count: 0,
        theory_lemma_count: 0,
        resolution_count: 9,
        farkas_certificate_count: 0,
        lrat_present: false,
        alethe_text: None,
    };
    let trusted_with_text = trusted
        .clone()
        .with_alethe_text("trusted proof body".to_string());
    assert!(
        !trusted.is_fully_verified(),
        "trusted proof is not fully verified"
    );
    assert!(
        !trusted_with_text.is_fully_verified(),
        "attaching alethe_text must not upgrade a trusted proof"
    );
}
