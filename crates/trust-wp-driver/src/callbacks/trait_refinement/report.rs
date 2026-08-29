// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_ay::{EncodingError, VerificationOutcome, VerificationResult};

use super::RefinementCounts;
use crate::callbacks::{
    encoding_error_breakdown::EncodingErrorBreakdown,
    helpers::report_counterexample,
    reporting::{emit_verification_diagnostic_if_requested, verified_evidence_gap_reason},
};

/// Outcome of a single refinement check (pre- or post-condition direction).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RefinementOutcome {
    Verified,
    /// Solver returned Assumed — refinement not proven, only assumed (#2121).
    Assumed,
    Failed,
    Error,
    /// Unknown result from unsoundness demotion pipeline (#2106).
    /// Counted as an error with separate demotion tracking.
    Demoted,
    /// Verified-shaped result without accepted solver proof evidence.
    EvidenceGap,
}

#[cfg(test)]
pub(super) fn report_refinement_result(
    result: Result<VerificationResult, EncodingError>,
    def_path: &str,
    trait_method_path: &str,
    check_description: &str,
    loc: &str,
) -> RefinementOutcome {
    report_refinement_outcome_result(
        result.map(VerificationOutcome::without_provenance),
        def_path,
        trait_method_path,
        check_description,
        loc,
    )
}

pub(super) fn report_refinement_outcome_result(
    result: Result<VerificationOutcome, EncodingError>,
    def_path: &str,
    trait_method_path: &str,
    check_description: &str,
    loc: &str,
) -> RefinementOutcome {
    match result {
        Ok(outcome) => {
            let diagnostic_path = format!("{def_path}::{check_description}");
            emit_verification_diagnostic_if_requested(
                &diagnostic_path,
                "trait_refinement",
                &outcome,
            );
            if let Some(reason) = verified_evidence_gap_reason(&outcome) {
                eprintln!("trust-wp: {def_path} trait refinement evidence gap ({reason})");
                eprintln!("  trait method: {trait_method_path}");
                eprintln!("  check: {check_description}");
                eprintln!("  at {loc}");
                return RefinementOutcome::EvidenceGap;
            }
            report_refinement_verification_result(
                outcome.result,
                def_path,
                trait_method_path,
                check_description,
                loc,
            )
        }
        Err(error) => {
            eprintln!("trust-wp: {def_path} trait refinement error: {error}");
            eprintln!("  trait method: {trait_method_path}");
            eprintln!("  check: {check_description}");
            eprintln!("  at {loc}");
            RefinementOutcome::Error
        }
    }
}

fn report_refinement_verification_result(
    result: VerificationResult,
    def_path: &str,
    trait_method_path: &str,
    check_description: &str,
    loc: &str,
) -> RefinementOutcome {
    match result {
        VerificationResult::Verified(_) => RefinementOutcome::Verified,
        VerificationResult::Assumed(_) => {
            eprintln!("trust-wp: {def_path} trait refinement ASSUMED (not proven) (#2121)");
            eprintln!("  trait method: {trait_method_path}");
            eprintln!("  check: {check_description}");
            eprintln!("  at {loc}");
            RefinementOutcome::Assumed
        }
        VerificationResult::Failed(counterexample) => {
            eprintln!("trust-wp: {def_path} trait refinement FAILED \u{2717}");
            eprintln!("  trait method: {trait_method_path}");
            eprintln!("  check: {check_description}");
            eprintln!("  at {loc}");
            report_counterexample(&counterexample);
            RefinementOutcome::Failed
        }
        VerificationResult::Unknown(ref reason) => {
            // Unknown results, including vacuous proofs, are not successful
            // refinements. Track demotions from the unsoundness demotion
            // pipeline separately (#2106).
            let is_demoted = matches!(reason, trust_wp_ay::UnknownReason::Demoted(_));
            eprintln!("trust-wp: {def_path} trait refinement unknown ({reason})");
            eprintln!("  trait method: {trait_method_path}");
            eprintln!("  check: {check_description}");
            eprintln!("  at {loc}");
            if is_demoted {
                RefinementOutcome::Demoted
            } else {
                RefinementOutcome::Error
            }
        }
        // VerificationResult is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => RefinementOutcome::Error,
    }
}

pub(super) fn aggregate_refinement_counts(
    pre_outcome: RefinementOutcome,
    post_outcome: RefinementOutcome,
    verbose: bool,
    def_path: &str,
    encoding_errors: EncodingErrorBreakdown,
) -> RefinementCounts {
    let assumed_delta = usize::from(matches!(pre_outcome, RefinementOutcome::Assumed))
        + usize::from(matches!(post_outcome, RefinementOutcome::Assumed));
    let failed_delta = usize::from(matches!(pre_outcome, RefinementOutcome::Failed))
        + usize::from(matches!(post_outcome, RefinementOutcome::Failed));
    // Demoted counts as an error for overall accounting (#2106).
    let demoted_delta = usize::from(matches!(pre_outcome, RefinementOutcome::Demoted))
        + usize::from(matches!(post_outcome, RefinementOutcome::Demoted));
    let evidence_gap_delta = usize::from(matches!(pre_outcome, RefinementOutcome::EvidenceGap))
        + usize::from(matches!(post_outcome, RefinementOutcome::EvidenceGap));
    let warning_delta = evidence_gap_delta;
    let error_delta = usize::from(matches!(
        pre_outcome,
        RefinementOutcome::Error | RefinementOutcome::Demoted
    )) + usize::from(matches!(
        post_outcome,
        RefinementOutcome::Error | RefinementOutcome::Demoted
    ));

    if failed_delta > 0 || error_delta > 0 || evidence_gap_delta > 0 {
        RefinementCounts {
            verified_delta: -1,
            assumed_delta,
            failed_delta,
            error_delta,
            demoted_delta,
            evidence_gap_delta,
            warning_delta,
            encoding_errors,
        }
    } else if assumed_delta > 0 {
        // Assumed refinement is not a hard failure but is NOT verified (#2121).
        // Don't decrement verified count (no false negative), but don't
        // increment it either (no false positive).
        RefinementCounts {
            verified_delta: 0,
            assumed_delta,
            failed_delta: 0,
            error_delta: 0,
            demoted_delta: 0,
            evidence_gap_delta: 0,
            warning_delta: 0,
            encoding_errors,
        }
    } else {
        if verbose {
            eprintln!("trust-wp: {def_path} refinement verified \u{2713}");
        }
        RefinementCounts {
            verified_delta: 0,
            assumed_delta: 0,
            failed_delta: 0,
            error_delta: 0,
            demoted_delta: 0,
            evidence_gap_delta: 0,
            warning_delta: 0,
            encoding_errors,
        }
    }
}
