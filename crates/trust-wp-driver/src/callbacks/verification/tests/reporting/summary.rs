// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::callbacks::{
    encoding_error_breakdown::EncodingErrorBreakdown,
    reporting::{
        dropped_obligation_hint, format_proof_assert_summary, format_verification_summary,
        handle_recursive_variant_mir_unavailable, ProofAssertCounters, VerificationCounters,
        VerificationSummary,
    },
};

fn make_counters(
    verified: usize,
    failed: usize,
    errors: usize,
    skipped: usize,
    warnings: usize,
) -> VerificationCounters {
    VerificationCounters {
        verified,
        failed,
        errors,
        skipped,
        warnings,
        ..VerificationCounters::default()
    }
}

fn make_counters_with_assumed(
    verified: usize,
    failed: usize,
    errors: usize,
    skipped: usize,
    warnings: usize,
    assumed: usize,
) -> VerificationCounters {
    VerificationCounters {
        verified,
        failed,
        errors,
        skipped,
        assumed,
        warnings,
        ..VerificationCounters::default()
    }
}

#[test]
fn recursive_variant_mir_unavailable_counts_error() {
    let mut counters = VerificationCounters::default();
    handle_recursive_variant_mir_unavailable("crate::f", "src/lib.rs:1:1", &mut counters);
    assert_eq!(
        counters.errors, 1,
        "expected missing MIR to count as one error"
    );
}

#[test]
fn format_verification_summary_omits_skipped_when_zero() {
    let c = make_counters(2, 1, 0, 0, 0);
    assert_eq!(
        format_verification_summary(&c, 0),
        "trust-wp: 2 verified, 1 failed, 0 errors"
    );
}

#[test]
fn format_verification_summary_includes_skipped_when_nonzero() {
    let c = make_counters(2, 1, 0, 3, 0);
    assert_eq!(
        format_verification_summary(&c, 0),
        "trust-wp: 2 verified, 1 failed, 0 errors, 3 skipped"
    );
}

#[test]
fn format_verification_summary_includes_warnings_when_nonzero() {
    let c = make_counters(5, 0, 0, 0, 3);
    assert_eq!(
        format_verification_summary(&c, 0),
        "trust-wp: 5 verified, 0 failed, 0 errors, 3 warnings"
    );
}

#[test]
fn format_verification_summary_includes_both_skipped_and_warnings() {
    let c = make_counters(2, 1, 0, 1, 4);
    assert_eq!(
        format_verification_summary(&c, 0),
        "trust-wp: 2 verified, 1 failed, 0 errors, 1 skipped, 4 warnings"
    );
}

#[test]
fn format_verification_summary_includes_unverified_axioms() {
    let c = make_counters(3, 0, 0, 0, 0);
    assert_eq!(
        format_verification_summary(&c, 2),
        "trust-wp: 3 verified, 0 failed, 0 errors, 2 unverified axiom(s)"
    );
}

#[test]
fn format_verification_summary_includes_unverified_axioms_and_warnings() {
    let c = make_counters(3, 1, 0, 0, 2);
    assert_eq!(
        format_verification_summary(&c, 1),
        "trust-wp: 3 verified, 1 failed, 0 errors, 1 unverified axiom(s), 2 warnings"
    );
}

#[test]
fn format_verification_summary_includes_assumed_when_nonzero() {
    let c = make_counters_with_assumed(3, 0, 0, 0, 0, 2);
    assert_eq!(
        format_verification_summary(&c, 0),
        "trust-wp: 3 verified, 0 failed, 0 errors, 2 assumed"
    );
}

#[test]
fn format_verification_summary_includes_trusted_when_nonzero() {
    let c = VerificationCounters {
        verified: 3,
        trusted: 2,
        ..VerificationCounters::default()
    };
    assert_eq!(
        format_verification_summary(&c, 0),
        "trust-wp: 3 verified, 0 failed, 0 errors, 2 trusted"
    );
}

#[test]
fn format_verification_summary_all_counters() {
    let c = VerificationCounters {
        verified: 5,
        failed: 2,
        errors: 1,
        skipped: 3,
        assumed: 1,
        trusted: 2,
        demoted: 1,
        panics: 1,
        warnings: 4,
        ..VerificationCounters::default()
    };
    assert_eq!(
        format_verification_summary(&c, 2),
        "trust-wp: 5 verified, 2 failed, 1 errors, 1 assumed, 2 trusted, 3 skipped, 2 unverified axiom(s), 1 demoted, 1 panicked, 4 warnings"
    );
}

#[test]
fn format_verification_summary_includes_verified_with_axiom_deps() {
    let c = VerificationCounters {
        verified: 3,
        verified_with_axiom_deps: 2,
        ..VerificationCounters::default()
    };
    assert_eq!(
        format_verification_summary(&c, 1),
        "trust-wp: 3 verified, 0 failed, 0 errors, 2 verified* (unproven axiom deps), 1 unverified axiom(s)"
    );
}

#[test]
fn format_verification_summary_includes_evidence_gaps() {
    let c = VerificationCounters {
        verified: 3,
        evidence_gaps: 2,
        ..VerificationCounters::default()
    };
    assert_eq!(
        format_verification_summary(&c, 0),
        "trust-wp: 3 verified, 0 failed, 0 errors, 2 evidence gaps"
    );
}

#[test]
fn summary_from_counters_maps_assumed_field() {
    let counters = VerificationCounters {
        verified: 3,
        assumed: 2,
        trusted: 1,
        ..VerificationCounters::default()
    };
    let pa = ProofAssertCounters::default();
    let summary = VerificationSummary::from_counters(&counters, &pa);
    assert_eq!(summary.assumed, 2, "assumed should map from counters");
    assert_eq!(summary.trusted, 1, "trusted should remain separate");
    assert_eq!(summary.verified, 3);
}

#[test]
fn summary_from_counters_maps_function_and_proof_assert_evidence_gaps() {
    let counters = VerificationCounters {
        evidence_gaps: 2,
        ..VerificationCounters::default()
    };
    let pa = ProofAssertCounters {
        evidence_gaps: 3,
        ..ProofAssertCounters::default()
    };
    let summary = VerificationSummary::from_counters(&counters, &pa);
    assert_eq!(summary.evidence_gaps, 5);
    assert_eq!(summary.exit_code(), 2);
}

#[test]
fn is_assumed_only_true_when_only_assumed() {
    let counters = VerificationCounters {
        assumed: 3,
        ..VerificationCounters::default()
    };
    let pa = ProofAssertCounters::default();
    let summary = VerificationSummary::from_counters(&counters, &pa);
    assert!(
        summary.is_assumed_only(),
        "should be assumed-only when no verified/failed/errors"
    );
}

#[test]
fn is_assumed_only_false_when_verified_present() {
    let counters = VerificationCounters {
        verified: 1,
        assumed: 2,
        ..VerificationCounters::default()
    };
    let pa = ProofAssertCounters::default();
    let summary = VerificationSummary::from_counters(&counters, &pa);
    assert!(
        !summary.is_assumed_only(),
        "should not be assumed-only when verified > 0"
    );
}

#[test]
fn is_assumed_only_false_when_no_assumed() {
    let counters = VerificationCounters {
        verified: 5,
        ..VerificationCounters::default()
    };
    let pa = ProofAssertCounters::default();
    let summary = VerificationSummary::from_counters(&counters, &pa);
    assert!(
        !summary.is_assumed_only(),
        "should not be assumed-only when assumed == 0"
    );
}

#[test]
fn is_assumed_only_false_when_panics_present() {
    let counters = VerificationCounters {
        assumed: 3,
        panics: 1,
        ..VerificationCounters::default()
    };
    let pa = ProofAssertCounters::default();
    let summary = VerificationSummary::from_counters(&counters, &pa);
    assert!(
        !summary.is_assumed_only(),
        "should not be assumed-only when panics > 0 (#1975)"
    );
}

#[test]
fn dropped_obligation_hint_shown_when_drops_present_and_not_verbose() {
    assert_eq!(
        dropped_obligation_hint(1, false),
        Some("trust-wp: hint: run with -v for additional warning context")
    );
}

#[test]
fn dropped_obligation_hint_hidden_when_verbose_or_no_drops() {
    assert_eq!(dropped_obligation_hint(0, false), None);
    assert_eq!(dropped_obligation_hint(3, true), None);
}

// ── encoding-error breakdown tests (#2015) ──

#[test]
fn format_verification_summary_includes_encoding_errors_when_nonzero() {
    let c = VerificationCounters {
        verified: 5,
        failed: 2,
        errors: 8,
        encoding_errors: EncodingErrorBreakdown {
            unsupported: 3,
            sort_inference: 4,
            solver: 1,
        },
        ..VerificationCounters::default()
    };
    assert_eq!(
        format_verification_summary(&c, 0),
        "trust-wp: 5 verified, 2 failed, 8 errors, encoding-errors unsupported=3 sort-inference=4 solver=1"
    );
}

#[test]
fn format_verification_summary_omits_encoding_errors_when_empty() {
    let c = make_counters(3, 0, 2, 0, 0);
    let summary = format_verification_summary(&c, 0);
    assert!(
        !summary.contains("encoding-errors"),
        "encoding-errors suffix should be omitted when breakdown is empty"
    );
}

#[test]
fn format_proof_assert_summary_basic() {
    let pa = ProofAssertCounters {
        verified: 3,
        failed: 0,
        errors: 2,
        ..ProofAssertCounters::default()
    };
    assert_eq!(
        format_proof_assert_summary(&pa),
        "trust-wp: proof_assert: 3 verified, 0 failed, 2 errors"
    );
}

/// When `inconclusive > 0`, the summary line MUST include the count so that
/// the compat harness classifier and downstream telemetry can observe
/// contractless proof_assert recoveries (#2700). If this count were silently
/// dropped from the summary, the harness would be unable to distinguish
/// "recovered from Incomplete" from "true verified".
#[test]
fn format_proof_assert_summary_includes_inconclusive_when_nonzero() {
    let pa = ProofAssertCounters {
        verified: 1,
        failed: 0,
        errors: 0,
        inconclusive: 2,
        ..ProofAssertCounters::default()
    };
    assert_eq!(
        format_proof_assert_summary(&pa),
        "trust-wp: proof_assert: 1 verified, 0 failed, 0 errors, 2 inconclusive"
    );
}

#[test]
fn format_proof_assert_summary_includes_evidence_gaps_when_nonzero() {
    let pa = ProofAssertCounters {
        verified: 1,
        failed: 0,
        errors: 1,
        evidence_gaps: 1,
        ..ProofAssertCounters::default()
    };
    assert_eq!(
        format_proof_assert_summary(&pa),
        "trust-wp: proof_assert: 1 verified, 0 failed, 1 errors, 1 evidence gaps"
    );
}

/// Zero inconclusive count MUST NOT add a trailing ", 0 inconclusive" —
/// the field is observability-only and only meaningful when non-zero.
#[test]
fn format_proof_assert_summary_omits_inconclusive_when_zero() {
    let pa = ProofAssertCounters {
        verified: 1,
        failed: 0,
        errors: 0,
        inconclusive: 0,
        ..ProofAssertCounters::default()
    };
    assert_eq!(
        format_proof_assert_summary(&pa),
        "trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"
    );
}

#[test]
fn format_proof_assert_summary_with_encoding_errors() {
    let pa = ProofAssertCounters {
        verified: 3,
        failed: 0,
        errors: 2,
        encoding_errors: EncodingErrorBreakdown {
            unsupported: 2,
            sort_inference: 0,
            solver: 0,
        },
        ..ProofAssertCounters::default()
    };
    assert_eq!(
        format_proof_assert_summary(&pa),
        "trust-wp: proof_assert: 3 verified, 0 failed, 2 errors, encoding-errors unsupported=2 sort-inference=0 solver=0"
    );
}

#[test]
fn summary_from_counters_maps_encoding_errors() {
    let counters = VerificationCounters {
        errors: 5,
        encoding_errors: EncodingErrorBreakdown {
            unsupported: 2,
            sort_inference: 1,
            solver: 2,
        },
        ..VerificationCounters::default()
    };
    let pa = ProofAssertCounters {
        errors: 3,
        encoding_errors: EncodingErrorBreakdown {
            unsupported: 1,
            sort_inference: 0,
            solver: 2,
        },
        ..ProofAssertCounters::default()
    };
    let summary = VerificationSummary::from_counters(&counters, &pa);
    assert_eq!(summary.encoding_errors.unsupported, 2);
    assert_eq!(summary.encoding_errors.sort_inference, 1);
    assert_eq!(summary.encoding_errors.solver, 2);
    assert_eq!(summary.proof_assert_encoding_errors.unsupported, 1);
    assert_eq!(summary.proof_assert_encoding_errors.solver, 2);
}
