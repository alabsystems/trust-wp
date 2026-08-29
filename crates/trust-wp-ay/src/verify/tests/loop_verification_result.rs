// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use crate::UnknownReason;

// --- LoopVerificationResult::overall precedence logic ---
// Coverage gap: 70-line method with precedence rules (Failed > Unknown >
// Assumed > Verified) and 5 optional fields, zero direct unit tests.

#[test]
#[timeout(30000)]
fn loop_result_overall_all_verified() {
    use crate::verify::LoopVerificationResult;

    let result = LoopVerificationResult {
        initialization: crate::verify::VerificationResult::Verified(None),
        preservation: crate::verify::VerificationResult::Verified(None),
        postcondition: crate::verify::VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        matches!(
            result.overall(),
            crate::verify::VerificationResult::Verified(_)
        ),
        "all Verified with no variants should be Verified overall"
    );
}

#[test]
#[timeout(30000)]
fn loop_result_overall_failed_takes_precedence() {
    use crate::verify::{Counterexample, LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Failed(Counterexample::empty()),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        matches!(result.overall(), VerificationResult::Failed(_)),
        "Failed preservation should dominate"
    );
}

#[test]
#[timeout(30000)]
fn loop_result_overall_unknown_over_assumed() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("axiom".to_string()),
        preservation: VerificationResult::Unknown(UnknownReason::Incomplete),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    match result.overall() {
        VerificationResult::Unknown(reason) => {
            assert!(matches!(reason, UnknownReason::Incomplete));
        }
        other => panic!("expected Unknown, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn loop_result_overall_assumed_propagated() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("axiom-only".to_string()),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    match result.overall() {
        VerificationResult::Assumed(reason) => {
            assert_eq!(reason, "axiom-only");
        }
        other => panic!("expected Assumed, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn loop_result_overall_variant_failure_detected() {
    use crate::verify::{Counterexample, LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Failed(Counterexample::empty())),
        variant_decrease: Some(VerificationResult::Verified(None)),
    };
    assert!(
        matches!(result.overall(), VerificationResult::Failed(_)),
        "Failed variant_nonneg should propagate as Failed overall"
    );
}

#[test]
#[timeout(30000)]
fn loop_result_all_passed_with_assumptions() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("axiom".to_string()),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(result.all_passed(), "Assumed counts as passed");
    assert!(!result.all_verified(), "Assumed does NOT count as verified");
}

#[test]
#[timeout(30000)]
fn loop_result_all_verified_with_variants() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: Some(VerificationResult::Verified(None)),
    };
    assert!(result.all_passed(), "all Verified should pass");
    assert!(result.all_verified(), "all Verified should be verified");
}

/// Verify that `overall()` returns Assumed when any loop
/// sub-result is Assumed. This is the property that prevents the
/// loop_contract.rs counter path from counting Assumed results as
/// `counters.verified`. (#2159)
#[test]
#[timeout(30000)]
fn loop_result_overall_returns_assumed_not_verified() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("axiom-only".to_string()),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        result.all_passed(),
        "all_passed should be true (Assumed counts as passed)"
    );
    assert!(
        !result.all_verified(),
        "all_verified should be false when any result is Assumed"
    );
    assert!(
        matches!(result.overall(), VerificationResult::Assumed(_)),
        "overall() must return Assumed: got {:?}",
        result.overall()
    );
}

// --- induction_passed (zero tests before this) ---

/// induction_passed is true when init + preservation + variants all pass.
#[test]
#[timeout(30000)]
fn loop_result_induction_passed_all_verified_no_variants() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Unknown(UnknownReason::Timeout),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        result.induction_passed(),
        "induction_passed ignores postcondition"
    );
}

/// induction_passed is false when preservation fails.
#[test]
#[timeout(30000)]
fn loop_result_induction_passed_false_when_preservation_fails() {
    use crate::verify::{Counterexample, LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Failed(Counterexample::empty()),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        !result.induction_passed(),
        "Failed preservation blocks induction"
    );
}

/// induction_passed is false when initialization is Unknown.
#[test]
#[timeout(30000)]
fn loop_result_induction_passed_false_when_init_unknown() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Unknown(UnknownReason::Incomplete),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        !result.induction_passed(),
        "Unknown initialization blocks induction"
    );
}

/// induction_passed requires real verification, not assumed initialization.
#[test]
#[timeout(30000)]
fn loop_result_induction_passed_false_with_assumed_initialization() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("axiom".to_string()),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Unknown(UnknownReason::Timeout),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        !result.induction_passed(),
        "Assumed initialization must not authorize induction"
    );
}

/// induction_passed requires real verification, not assumed preservation.
#[test]
#[timeout(30000)]
fn loop_result_induction_passed_false_with_assumed_preservation() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Assumed("axiom".to_string()),
        postcondition: VerificationResult::Unknown(UnknownReason::Timeout),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        !result.induction_passed(),
        "Assumed preservation must not authorize induction"
    );
}

/// induction_passed is false when variant_decrease fails.
#[test]
#[timeout(30000)]
fn loop_result_induction_passed_false_when_variant_decrease_fails() {
    use crate::verify::{Counterexample, LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: Some(VerificationResult::Failed(Counterexample::empty())),
    };
    assert!(
        !result.induction_passed(),
        "Failed variant_decrease blocks induction"
    );
}

/// induction_passed requires real verification for variant checks too.
#[test]
#[timeout(30000)]
fn loop_result_induction_passed_false_when_variant_assumed() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: Some(VerificationResult::Assumed("axiom".to_string())),
    };
    assert!(
        !result.induction_passed(),
        "Assumed variant proof must not authorize induction"
    );
}

/// induction_passed returns false for asymmetric variant state (Some/None).
#[test]
#[timeout(30000)]
fn loop_result_induction_passed_false_for_asymmetric_variants() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: None,
    };
    assert!(
        !result.induction_passed(),
        "asymmetric variant state (Some/None) should fail"
    );
}

// --- overall() additional gap tests ---

/// overall() returns Unknown for asymmetric variant state.
#[test]
#[timeout(30000)]
fn loop_result_overall_asymmetric_variant_returns_unknown() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: Some(VerificationResult::Verified(None)),
    };
    match result.overall() {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("inconsistent"),
                "expected inconsistency message, got: {}",
                reason
            );
        }
        other => panic!("expected Unknown for asymmetric variant, got {other:?}"),
    }
}

/// overall() propagates postcondition failure.
#[test]
#[timeout(30000)]
fn loop_result_overall_postcondition_failed() {
    use crate::verify::{Counterexample, LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Failed(Counterexample::empty()),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        matches!(result.overall(), VerificationResult::Failed(_)),
        "Failed postcondition should propagate"
    );
}

/// overall() propagates variant_decrease failure.
#[test]
#[timeout(30000)]
fn loop_result_overall_variant_decrease_failed() {
    use crate::verify::{Counterexample, LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: Some(VerificationResult::Failed(Counterexample::empty())),
    };
    assert!(
        matches!(result.overall(), VerificationResult::Failed(_)),
        "Failed variant_decrease should propagate"
    );
}

#[test]
#[timeout(30000)]
fn loop_outcome_as_result_drops_provenance_but_keeps_phase_results() {
    use crate::verify::{LoopVerificationOutcome, VerificationOutcome, VerificationResult};

    let outcome = LoopVerificationOutcome {
        initialization: VerificationOutcome::without_provenance(VerificationResult::Verified(None)),
        preservation: VerificationOutcome::without_provenance(VerificationResult::Assumed(
            "axiom".to_string(),
        )),
        postcondition: VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::Incomplete,
        )),
        variant_nonneg: Some(VerificationOutcome::without_provenance(
            VerificationResult::Verified(None),
        )),
        variant_decrease: Some(VerificationOutcome::without_provenance(
            VerificationResult::Unknown(UnknownReason::Timeout),
        )),
        entry_may_execute: Some(VerificationOutcome::without_provenance(
            VerificationResult::Failed(crate::verify::Counterexample::empty()),
        )),
    };

    let result = outcome.as_result();
    assert!(matches!(
        result.initialization,
        VerificationResult::Verified(_)
    ));
    assert!(matches!(
        result.preservation,
        VerificationResult::Assumed(_)
    ));
    assert!(matches!(
        result.postcondition,
        VerificationResult::Unknown(UnknownReason::Incomplete)
    ));
    assert!(matches!(
        result.variant_decrease,
        Some(VerificationResult::Unknown(UnknownReason::Timeout))
    ));
    assert!(
        matches!(outcome.overall(), VerificationResult::Unknown(_)),
        "entry reachability probes must not participate in loop verification overall"
    );
}

#[test]
#[timeout(30000)]
fn loop_outcome_all_verified_ignores_entry_probe_result() {
    use crate::verify::{Counterexample, LoopVerificationOutcome, VerificationOutcome};

    let outcome = LoopVerificationOutcome {
        initialization: VerificationOutcome::without_provenance(
            crate::verify::VerificationResult::Verified(None),
        ),
        preservation: VerificationOutcome::without_provenance(
            crate::verify::VerificationResult::Verified(None),
        ),
        postcondition: VerificationOutcome::without_provenance(
            crate::verify::VerificationResult::Verified(None),
        ),
        variant_nonneg: None,
        variant_decrease: None,
        entry_may_execute: Some(VerificationOutcome::without_provenance(
            crate::verify::VerificationResult::Failed(Counterexample::empty()),
        )),
    };

    assert!(outcome.all_verified());
    assert!(matches!(
        outcome.overall(),
        crate::verify::VerificationResult::Verified(_)
    ));
}

// --- all_passed / all_verified negative cases ---

/// all_passed returns false when preservation fails.
#[test]
#[timeout(30000)]
fn loop_result_all_passed_false_when_failed() {
    use crate::verify::{Counterexample, LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Failed(Counterexample::empty()),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(!result.all_passed(), "Failed should not count as passed");
}

/// all_verified returns false when variant is Unknown.
#[test]
#[timeout(30000)]
fn loop_result_all_verified_false_when_variant_unknown() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: Some(VerificationResult::Unknown(UnknownReason::Timeout)),
    };
    assert!(
        !result.all_verified(),
        "Unknown variant should prevent all_verified"
    );
    assert!(
        !result.all_passed(),
        "Unknown variant should prevent all_passed too"
    );
}

// --- LoopVerificationResult::overall certificate propagation ---
// The loop verdict is the CONJUNCTION of its phases. `overall()` used to
// collapse an all-verified loop to `Verified(None)` — an acceptance carrying
// no evidence — which the mandatory proof-authority gate then demoted to
// `Unknown(ProofTrusted)` even when every phase had produced a checked,
// trust-free certificate. These tests pin BOTH directions: the conjunction is
// carried when every phase supplied one, and it still fails closed otherwise.

/// Fully verified per-phase certificate: strict, no trust steps, no holes.
#[cfg(test)]
fn clean_phase_summary(resolution_count: u32) -> crate::verify::ProofCertificateSummary {
    crate::verify::ProofCertificateSummary {
        strict_verified: true,
        restricted_rule_subset: true,
        trust_count: 0,
        trust_fallback_count: 0,
        hole_count: 0,
        theory_lemma_count: 0,
        resolution_count,
        farkas_certificate_count: 0,
        lrat_present: true,
        alethe_text: None,
    }
}

#[test]
#[timeout(30000)]
fn loop_result_overall_carries_conjunction_of_phase_certificates() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(Some(clean_phase_summary(1))),
        preservation: VerificationResult::Verified(Some(clean_phase_summary(2))),
        postcondition: VerificationResult::Verified(Some(clean_phase_summary(4))),
        variant_nonneg: Some(VerificationResult::Verified(Some(clean_phase_summary(8)))),
        variant_decrease: Some(VerificationResult::Verified(Some(clean_phase_summary(16)))),
    };

    let overall = result.overall();
    let VerificationResult::Verified(Some(summary)) = &overall else {
        panic!("all five phases carried a checked certificate; overall must carry their conjunction, got {overall:?}");
    };
    assert!(
        summary.is_fully_verified(),
        "conjunction of fully verified phase certificates must itself be fully verified: {summary:?}"
    );
    assert_eq!(
        summary.resolution_count, 31,
        "conjunction must account for every phase's proof (1+2+4+8+16)"
    );
    assert!(
        matches!(
            overall.clone().apply_strict_trust(true),
            VerificationResult::Verified(_)
        ),
        "a fully certified loop must survive the mandatory proof-authority gate"
    );
}

#[test]
#[timeout(30000)]
fn loop_result_overall_fails_closed_when_a_phase_has_no_certificate() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(Some(clean_phase_summary(1))),
        // Accepted without a proof — nothing certified this phase.
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(Some(clean_phase_summary(4))),
        variant_nonneg: None,
        variant_decrease: None,
    };

    assert!(
        matches!(result.overall(), VerificationResult::Verified(None)),
        "one uncertified phase must leave the conjunction uncertified, got {:?}",
        result.overall()
    );
    assert!(
        matches!(
            result.overall().apply_strict_trust(true),
            VerificationResult::Unknown(UnknownReason::ProofTrusted)
        ),
        "an uncertified loop conjunction must still be demoted by the authority gate"
    );
}

#[test]
#[timeout(30000)]
fn loop_result_overall_fails_closed_on_a_trust_bearing_phase_certificate() {
    use crate::verify::{LoopVerificationResult, VerificationResult};

    let mut trusted = clean_phase_summary(2);
    trusted.trust_count = 1;
    assert!(!trusted.is_fully_verified());

    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(Some(clean_phase_summary(1))),
        preservation: VerificationResult::Verified(Some(trusted)),
        postcondition: VerificationResult::Verified(Some(clean_phase_summary(4))),
        variant_nonneg: None,
        variant_decrease: None,
    };

    assert!(
        matches!(result.overall(), VerificationResult::Verified(None)),
        "a phase proof containing a trust step must not be laundered into the conjunction, got {:?}",
        result.overall()
    );
    assert!(
        matches!(
            result.overall().apply_strict_trust(true),
            VerificationResult::Unknown(UnknownReason::ProofTrusted)
        ),
        "a trust-bearing loop conjunction must be demoted by the authority gate"
    );
}
