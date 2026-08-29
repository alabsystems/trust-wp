// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_ay::{LoopVerificationOutcome, VerificationOutcome};

use super::{
    combine_loop_results, combine_optional_results, loop_verification_evidence_gap_reasons,
    worst_result, Counterexample, LoopVerificationResult, UnknownReason, VerificationResult,
};

fn make_counterexample() -> Counterexample {
    Counterexample {
        values: Vec::new(),
        violated_postcondition: None,
    }
}

fn make_all_verified() -> LoopVerificationResult {
    LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    }
}

#[test]
fn combine_optional_results_both_none_returns_none() {
    assert!(combine_optional_results(None, None).is_none());
}

#[test]
fn loop_outcome_verified_phase_without_provenance_is_evidence_gap() {
    let outcome = LoopVerificationOutcome {
        initialization: VerificationOutcome::without_provenance(VerificationResult::Verified(None)),
        preservation: VerificationOutcome::without_provenance(VerificationResult::Assumed(
            "not under test".to_string(),
        )),
        postcondition: VerificationOutcome::without_provenance(VerificationResult::Assumed(
            "not under test".to_string(),
        )),
        variant_nonneg: None,
        variant_decrease: None,
        entry_may_execute: None,
    };

    let reasons = loop_verification_evidence_gap_reasons(&outcome);

    assert_eq!(reasons, vec!["initialization: missing solver provenance"]);
}

#[test]
fn combine_optional_results_some_with_none_returns_some() {
    let result = combine_optional_results(Some(VerificationResult::Verified(None)), None);
    assert!(matches!(result, Some(VerificationResult::Verified(_))));

    let result = combine_optional_results(
        None,
        Some(VerificationResult::Unknown(UnknownReason::Unspecified)),
    );
    assert!(matches!(
        result,
        Some(VerificationResult::Unknown(UnknownReason::Unspecified))
    ));
}

#[test]
fn combine_optional_results_both_some_takes_worst() {
    let result = combine_optional_results(
        Some(VerificationResult::Verified(None)),
        Some(VerificationResult::Unknown(UnknownReason::Timeout)),
    );
    assert!(
        matches!(result, Some(VerificationResult::Unknown(_))),
        "Unknown should override Verified, got {result:?}"
    );
}

#[test]
fn combine_loop_results_all_verified_stays_verified() {
    // Use asymmetric inputs so the test fails if either argument is ignored.
    // `a` has variant_nonneg = Some(Verified), `b` has variant_decrease = Some(Verified).
    // A correct combine must inspect both arguments to produce the right output.
    let a = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: None,
    };
    let b = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: Some(VerificationResult::Verified(None)),
    };
    let combined = combine_loop_results(a, b);
    assert!(matches!(
        combined.initialization,
        VerificationResult::Verified(_)
    ));
    assert!(matches!(
        combined.preservation,
        VerificationResult::Verified(_)
    ));
    assert!(matches!(
        combined.postcondition,
        VerificationResult::Verified(_)
    ));
    assert!(
        matches!(
            combined.variant_nonneg,
            Some(VerificationResult::Verified(_))
        ),
        "variant_nonneg should be Some(Verified) from a, got {:?}",
        combined.variant_nonneg
    );
    assert!(
        matches!(
            combined.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "variant_decrease should be Some(Verified) from b, got {:?}",
        combined.variant_decrease
    );
}

#[test]
fn combine_loop_results_failed_init_propagates() {
    let a = LoopVerificationResult {
        initialization: VerificationResult::Failed(make_counterexample()),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    let b = make_all_verified();
    let combined = combine_loop_results(a, b);
    assert!(
        matches!(combined.initialization, VerificationResult::Failed(_)),
        "Failed initialization should propagate: {:?}",
        combined.initialization
    );
    assert!(matches!(
        combined.preservation,
        VerificationResult::Verified(_)
    ));
    assert!(matches!(
        combined.postcondition,
        VerificationResult::Verified(_)
    ));
}

#[test]
fn combine_loop_results_worst_across_all_fields() {
    let a = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Unknown(UnknownReason::SatModel),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: None,
    };
    let b = LoopVerificationResult {
        initialization: VerificationResult::Unknown(UnknownReason::Unspecified),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Failed(make_counterexample()),
        variant_nonneg: Some(VerificationResult::Unknown(UnknownReason::Unspecified)),
        variant_decrease: Some(VerificationResult::Verified(None)),
    };
    let combined = combine_loop_results(a, b);
    assert!(
        matches!(combined.initialization, VerificationResult::Unknown(_)),
        "init should be Unknown: {:?}",
        combined.initialization
    );
    assert!(
        matches!(combined.preservation, VerificationResult::Unknown(_)),
        "preservation should be Unknown: {:?}",
        combined.preservation
    );
    assert!(
        matches!(combined.postcondition, VerificationResult::Failed(_)),
        "postcondition should be Failed: {:?}",
        combined.postcondition
    );
    assert!(
        matches!(
            combined.variant_nonneg,
            Some(VerificationResult::Unknown(_))
        ),
        "variant_nonneg should be Some(Unknown): {:?}",
        combined.variant_nonneg
    );
    assert!(
        matches!(
            combined.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "variant_decrease should be Some(Verified): {:?}",
        combined.variant_decrease
    );
}

#[test]
fn worst_result_verified_verified_stays_verified() {
    let result = worst_result(
        VerificationResult::Verified(None),
        VerificationResult::Verified(None),
    );
    assert!(matches!(result, VerificationResult::Verified(_)));
}

#[test]
fn worst_result_failed_trumps_everything() {
    let ce = make_counterexample();
    let result = worst_result(
        VerificationResult::Verified(None),
        VerificationResult::Failed(ce),
    );
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Failed should override Verified: {result:?}"
    );
}

// --- worst_result Assumed soundness tests (#2149) ---

#[test]
fn worst_result_assumed_is_worse_than_verified() {
    let result = worst_result(
        VerificationResult::Verified(None),
        VerificationResult::Assumed("axiom only".to_string()),
    );
    assert!(
        matches!(result, VerificationResult::Assumed(_)),
        "Assumed should override Verified: {result:?}"
    );
}

#[test]
fn worst_result_assumed_loses_to_unknown() {
    let result = worst_result(
        VerificationResult::Assumed("axiom only".to_string()),
        VerificationResult::Unknown(UnknownReason::Timeout),
    );
    assert!(
        matches!(result, VerificationResult::Unknown(_)),
        "Unknown should override Assumed: {result:?}"
    );
}

#[test]
fn worst_result_assumed_loses_to_failed() {
    let ce = make_counterexample();
    let result = worst_result(
        VerificationResult::Assumed("axiom only".to_string()),
        VerificationResult::Failed(ce),
    );
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Failed should override Assumed: {result:?}"
    );
}
