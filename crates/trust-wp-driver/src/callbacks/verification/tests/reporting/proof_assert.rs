// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_ay::{UnknownReason, VerificationOutcome, VerificationResult};

use crate::callbacks::{
    proof_assert_verify::PreparedAssertion,
    reporting::{
        report_proof_assert_outcome_result, report_proof_assert_result, ProofAssertCounters,
    },
};

/// A SAT snapshot ay validated and accepted: the only evidence on which
/// trust-wp may publish a proof_assert as refuted.
fn validated_sat_provenance() -> trust_wp_ay::VerificationProvenance {
    let mut evidence = trust_wp_ay::SolveEvidenceSnapshot::default();
    evidence.result = "sat".to_string();
    evidence.model_validated = true;
    evidence.accepted_for_consumer = true;
    evidence.verification.sat_model_validated = true;
    evidence.verification_level = trust_wp_ay::SolveVerificationLevelSnapshot::FullyVerified;
    trust_wp_ay::VerificationProvenance::with_solve_time(std::time::Duration::from_millis(7))
        .with_assertion_count(3)
        .with_solve_evidence(Some(evidence))
}

/// Verify that proof_assert Assumed results are counted as errors, not verified (#1891).
///
/// A proof_assert that produces Assumed was not actually proven — counting it as
/// verified would inflate the verification count and mask real gaps.
#[test]
fn report_proof_assert_assumed_counts_as_error_not_verified() {
    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: false,
        containing_requires_false: false,
        fn_path: "test::proof_assert_fn".to_string(),
        loc: "test.rs:1:1".to_string(),
        expr_text: "x > 0".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Assumed(
            "axiom-only function".to_string(),
        )),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(
        pa_counters.errors, 1,
        "Assumed proof_assert should count as error"
    );
    assert_eq!(
        pa_counters.verified, 0,
        "Assumed proof_assert should NOT count as verified"
    );
}

/// Verify that proof_assert Verified results without provenance are evidence gaps.
#[test]
fn report_proof_assert_verified_without_evidence_counts_as_gap() {
    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: false,
        containing_requires_false: false,
        fn_path: "test::proof_assert_fn".to_string(),
        loc: "test.rs:1:1".to_string(),
        expr_text: "x > 0".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Verified(None)),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(
        pa_counters.verified, 0,
        "Verified without accepted evidence should not count as verified"
    );
    assert_eq!(
        pa_counters.errors, 1,
        "Verified without accepted evidence should count as error"
    );
    assert_eq!(
        pa_counters.evidence_gaps, 1,
        "Verified without accepted evidence should be tracked as an evidence gap"
    );
}

/// Verify that proof_assert Failed results are counted as failed.
#[test]
fn report_proof_assert_failed_counts_as_failed() {
    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: false,
        containing_requires_false: false,
        fn_path: "test::proof_assert_fn".to_string(),
        loc: "test.rs:1:1".to_string(),
        expr_text: "x > 0".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_outcome_result(
        Ok(VerificationOutcome::new(
            VerificationResult::Failed(trust_wp_ay::Counterexample {
                values: vec![],
                violated_postcondition: None,
            }),
            Some(validated_sat_provenance()),
        )),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(pa_counters.failed, 1, "Failed should count as failed");
    assert_eq!(
        pa_counters.verified, 0,
        "Failed should not count as verified"
    );
    assert_eq!(
        pa_counters.refutations_withheld, 0,
        "a validated refutation is not withheld"
    );
}

/// The same refuted proof_assert WITHOUT a validated model is an inconclusive,
/// not a refutation: it counts as an error and NEVER as verified.
#[test]
fn report_proof_assert_failed_without_validated_model_counts_as_error() {
    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: false,
        containing_requires_false: false,
        fn_path: "test::proof_assert_fn".to_string(),
        loc: "test.rs:1:1".to_string(),
        expr_text: "x > 0".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Failed(trust_wp_ay::Counterexample {
            values: vec![],
            violated_postcondition: None,
        })),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(
        pa_counters.failed, 0,
        "an unvalidated refutation must NOT count as failed"
    );
    assert_eq!(pa_counters.errors, 1, "it is an inconclusive: count it");
    assert_eq!(
        pa_counters.verified, 0,
        "and it must never count as verified"
    );
    assert_eq!(pa_counters.refutations_withheld, 1);
}

/// Verify that proof_assert Unknown results are counted as errors.
#[test]
fn report_proof_assert_unknown_counts_as_error() {
    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: false,
        containing_requires_false: false,
        fn_path: "test::proof_assert_fn".to_string(),
        loc: "test.rs:1:1".to_string(),
        expr_text: "x > 0".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::Timeout)),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(pa_counters.errors, 1, "Unknown should count as error");
    assert_eq!(
        pa_counters.verified, 0,
        "Unknown should not count as verified"
    );
}

#[test]
fn report_proof_assert_contractless_incomplete_not_counted_as_error() {
    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: true,
        containing_requires_false: false,
        fn_path: "test::contractless_incomplete".to_string(),
        loc: "test.rs:2:1".to_string(),
        expr_text: "x > 0".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::Incomplete)),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(
        pa_counters.errors, 0,
        "Contractless incomplete proof_assert should not count as error"
    );
    assert_eq!(
        pa_counters.verified, 0,
        "Contractless incomplete proof_assert should not count as verified"
    );
    assert_eq!(
        pa_counters.inconclusive, 1,
        "Contractless incomplete proof_assert should count as inconclusive"
    );
}

#[test]
fn report_proof_assert_contractless_failed_still_counts_as_failed() {
    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: true,
        containing_requires_false: false,
        fn_path: "test::contractless_failed".to_string(),
        loc: "test.rs:3:1".to_string(),
        expr_text: "x > 0".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_outcome_result(
        Ok(VerificationOutcome::new(
            VerificationResult::Failed(trust_wp_ay::Counterexample {
                values: vec![],
                violated_postcondition: None,
            }),
            Some(validated_sat_provenance()),
        )),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(
        pa_counters.failed, 1,
        "Contractless failed proof_assert should still count as failed"
    );
}

/// Verify that proof_assert Unknown(Demoted(_)) results increment both
/// errors and the demoted sub-counter (#2106).
#[test]
fn report_proof_assert_demoted_increments_demoted_and_errors() {
    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: false,
        containing_requires_false: false,
        fn_path: "test::demoted_proof_assert".to_string(),
        loc: "test.rs:5:1".to_string(),
        expr_text: "v.len() > 0".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::Demoted(
            "sort_fallback_to_int".to_string(),
        ))),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(
        pa_counters.errors, 1,
        "Demoted proof_assert should count as error"
    );
    assert_eq!(
        pa_counters.demoted, 1,
        "Demoted proof_assert should increment demoted sub-counter"
    );
    assert_eq!(
        pa_counters.verified, 0,
        "Demoted proof_assert should not count as verified"
    );
}

/// Verify that vacuous proof_assert results (contradictory premises) are
/// counted as errors, not verified (#2663).
#[test]
fn report_proof_assert_vacuous_counts_as_error_not_verified() {
    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: false,
        containing_requires_false: false,
        fn_path: "test::vacuous_proof_assert".to_string(),
        loc: "test.rs:7:1".to_string(),
        expr_text: "x > 0".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::SolverMessage(
            "vacuous proof detected".to_string(),
        ))),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(
        pa_counters.verified, 0,
        "Vacuous proof_assert should NOT count as verified"
    );
    assert_eq!(
        pa_counters.errors, 1,
        "Vacuous proof_assert should count as error"
    );
}

/// Verify that a vacuous proof_assert inside a function with an explicit
/// user-authored `#[requires(false)]` is CREDITED as verified, not counted as
/// an error. The function is provably uncallable, so the assertion is vacuously
/// discharged by Creusot semantics (specification/erasure.rs regression).
#[test]
fn report_proof_assert_vacuous_with_requires_false_is_verified() {
    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: false,
        containing_requires_false: true,
        fn_path: "test::specs".to_string(),
        loc: "test.rs:8:1".to_string(),
        expr_text: "false".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::SolverMessage(
            "vacuous proof: base assertions are UNSAT without the negated postcondition"
                .to_string(),
        ))),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(
        pa_counters.verified, 1,
        "Vacuous proof_assert under #[requires(false)] should be credited as verified"
    );
    assert_eq!(
        pa_counters.errors, 0,
        "Vacuous proof_assert under #[requires(false)] should NOT count as error"
    );
}

/// Soundness guard: the `containing_requires_false` credit must NOT fire on a
/// NON-vacuous Unknown (e.g., solver incompleteness). Only a genuinely vacuous
/// base — which is exactly what an uncallable `#[requires(false)]` function
/// produces — is discharged; a real solver gap must still surface as an error.
#[test]
fn report_proof_assert_requires_false_does_not_swallow_nonvacuous_unknown() {
    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: false,
        containing_requires_false: true,
        fn_path: "test::specs".to_string(),
        loc: "test.rs:9:1".to_string(),
        expr_text: "x > 0".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::Incomplete)),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(
        pa_counters.verified, 0,
        "Non-vacuous Unknown must not be credited even under #[requires(false)]"
    );
    assert_eq!(
        pa_counters.errors, 1,
        "Non-vacuous Unknown must still count as error"
    );
}

/// Helper to build a minimal PreparedAssertion for report_proof_assert_result tests.
fn make_prepared(is_contractless: bool, fn_path: &str) -> PreparedAssertion {
    PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless,
        containing_requires_false: false,
        fn_path: fn_path.to_string(),
        loc: "test.rs:1:1".to_string(),
        expr_text: "x > 0".to_string(),
    }
}

/// Every quantifier-related UnknownReason variant MUST recover as `inconclusive`
/// (not `errors`) when the function is contractless. Regression guard for #2700:
/// a quantifier variant added later without updating
/// `is_contractless_proof_assert_inconclusive` would silently flip to counting
/// as error, breaking compat-test classification.
#[test]
fn report_proof_assert_contractless_all_quantifier_variants_are_inconclusive() {
    let reasons = [
        UnknownReason::Incomplete,
        UnknownReason::Quantifiers,
        UnknownReason::QuantifierUnhandled,
        UnknownReason::QuantifierRoundLimit,
        UnknownReason::QuantifierDeferred,
        UnknownReason::QuantifierCegqiIncomplete,
        UnknownReason::QuantifierEmatchingExistsIncomplete,
    ];

    for reason in reasons {
        let prepared = make_prepared(true, "test::contractless_quantifier_variant");
        let mut pa = ProofAssertCounters::default();
        report_proof_assert_result(
            Ok(VerificationResult::Unknown(reason.clone())),
            &prepared,
            &mut pa,
        );
        assert_eq!(
            pa.errors, 0,
            "Contractless {reason:?} must NOT count as error"
        );
        assert_eq!(
            pa.inconclusive, 1,
            "Contractless {reason:?} MUST count as inconclusive"
        );
        assert_eq!(
            pa.verified, 0,
            "Contractless {reason:?} must NOT count as verified"
        );
    }
}

/// Guard: Incomplete on a function that HAS contracts (is_contractless=false)
/// must still count as an error. The recovery path is scoped strictly to
/// contractless functions (#2700) — demoting errors in contracted functions
/// would mask real unknown obligations.
#[test]
fn report_proof_assert_with_contracts_incomplete_still_counts_as_error() {
    let prepared = make_prepared(false, "test::contracted_incomplete");
    let mut pa = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::Incomplete)),
        &prepared,
        &mut pa,
    );

    assert_eq!(
        pa.errors, 1,
        "Incomplete with contracts MUST count as error (no silent recovery)"
    );
    assert_eq!(
        pa.inconclusive, 0,
        "Contracted function must not promote Incomplete to inconclusive"
    );
    assert_eq!(pa.verified, 0, "Incomplete must not count as verified");
}

/// Guard: Quantifiers on a contracted function also stays an error.
#[test]
fn report_proof_assert_with_contracts_quantifiers_still_counts_as_error() {
    let prepared = make_prepared(false, "test::contracted_quantifiers");
    let mut pa = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::Quantifiers)),
        &prepared,
        &mut pa,
    );

    assert_eq!(pa.errors, 1);
    assert_eq!(pa.inconclusive, 0);
}

/// Non-quantifier reasons (Timeout, generic SolverMessage) are NOT inconclusive-
/// recoverable even when contractless. A timeout is an actual encoding/solver
/// problem distinct from "quantifier instantiation ran out". This guards
/// against overly-broad recovery.
#[test]
fn report_proof_assert_contractless_timeout_still_counts_as_error() {
    let prepared = make_prepared(true, "test::contractless_timeout");
    let mut pa = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::Timeout)),
        &prepared,
        &mut pa,
    );

    assert_eq!(
        pa.errors, 1,
        "Contractless Timeout must still count as error — not a quantifier inconclusive"
    );
    assert_eq!(
        pa.inconclusive, 0,
        "Timeout is not in the quantifier-recovery allowlist"
    );
}

/// Non-quantifier SolverMessage (that is NOT vacuous) must still count as error.
#[test]
fn report_proof_assert_contractless_non_vacuous_solver_message_counts_as_error() {
    let prepared = make_prepared(true, "test::contractless_other_solver_message");
    let mut pa = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::SolverMessage(
            "some other solver issue".to_string(),
        ))),
        &prepared,
        &mut pa,
    );

    assert_eq!(
        pa.errors, 1,
        "Non-vacuous SolverMessage must count as error even in contractless context"
    );
    assert_eq!(pa.inconclusive, 0);
    assert_eq!(pa.verified, 0);
}

/// Edge case: a vacuous SolverMessage in a contractless function stays on the
/// Unknown error path, not the contractless-inconclusive path. A vacuous result
/// is not a genuine proof, even when there are no function contracts. (#2663)
#[test]
fn report_proof_assert_contractless_vacuous_counts_as_error_not_verified() {
    let prepared = make_prepared(true, "test::contractless_vacuous");
    let mut pa = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::SolverMessage(
            "vacuous proof detected".to_string(),
        ))),
        &prepared,
        &mut pa,
    );

    assert_eq!(pa.verified, 0, "Vacuous must NOT count as verified");
    assert_eq!(
        pa.inconclusive, 0,
        "Vacuous must not count as contractless inconclusive"
    );
    assert_eq!(pa.errors, 1, "Vacuous must count as error");
}

/// Demoted reasons are not in the quantifier-recovery allowlist and must
/// continue to count as errors (and increment the demoted sub-counter)
/// even when contractless. This keeps soundness-demotion observability
/// separate from the inconclusive channel.
#[test]
fn report_proof_assert_contractless_demoted_still_counts_as_error_and_demoted() {
    let prepared = make_prepared(true, "test::contractless_demoted");
    let mut pa = ProofAssertCounters::default();

    report_proof_assert_result(
        Ok(VerificationResult::Unknown(UnknownReason::Demoted(
            "sort_fallback_to_int".to_string(),
        ))),
        &prepared,
        &mut pa,
    );

    assert_eq!(
        pa.errors, 1,
        "Contractless Demoted must still count as error — demotion is a soundness signal"
    );
    assert_eq!(
        pa.demoted, 1,
        "Demoted sub-counter must still increment in contractless context"
    );
    assert_eq!(
        pa.inconclusive, 0,
        "Demoted must not be treated as inconclusive-recoverable"
    );
}

/// Verify that proof_assert Err(EncodingError) results count as errors and
/// record the encoding error breakdown.
#[test]
fn report_proof_assert_encoding_error_counts_and_records() {
    use trust_wp_ay::EncodingError;

    let prepared = PreparedAssertion {
        preconditions: vec![],
        ensures: vec![],
        return_expr: None,
        mode_overrides: None,
        closure_capture_infos: vec![],
        has_mutating_call_effect: false,
        is_contractless: false,
        containing_requires_false: false,
        fn_path: "test::encoding_error_proof_assert".to_string(),
        loc: "test.rs:10:1".to_string(),
        expr_text: "result == 42".to_string(),
    };
    let mut pa_counters = ProofAssertCounters::default();

    report_proof_assert_result(
        Err(EncodingError::Unsupported {
            message: "test unsupported".to_string(),
            span: None,
            contract_text: None,
        }),
        &prepared,
        &mut pa_counters,
    );

    assert_eq!(pa_counters.errors, 1, "EncodingError should count as error");
    assert_eq!(
        pa_counters.verified, 0,
        "EncodingError should not count as verified"
    );
    assert_eq!(
        pa_counters.failed, 0,
        "EncodingError should not count as failed"
    );
    assert!(
        !pa_counters.encoding_errors.is_empty(),
        "EncodingError should be recorded in breakdown"
    );
}
