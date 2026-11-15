// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verification-run summary reporting.

use std::collections::HashSet;

use crate::callbacks::reporting::{
    dropped_obligation_hint, format_proof_assert_summary, format_verification_summary,
    ProofAssertCounters, VerificationCounters, VerificationSummary,
};

/// Print verification summary (#1526 Phase 5).
pub(super) fn print_verification_summary(
    counters: &VerificationCounters,
    pa_counters: &ProofAssertCounters,
    unverified_axioms: &HashSet<String>,
    verbose: bool,
) -> VerificationSummary {
    eprintln!();
    if !unverified_axioms.is_empty() {
        eprintln!(
            "trust-wp: {} logic function postcondition(s) unverified — callers may depend on unproven axioms",
            unverified_axioms.len()
        );
    }
    if counters.panics > 0 {
        eprintln!(
            "trust-wp: warning: {} function(s) panicked during verification (#1975)",
            counters.panics
        );
    }
    if counters.trusted > 0 {
        eprintln!("trust-wp: ({} trusted, skipped)", counters.trusted);
    }
    eprintln!(
        "{}",
        format_verification_summary(counters, unverified_axioms.len())
    );
    if let Some(hint) = dropped_obligation_hint(counters.warnings, verbose) {
        eprintln!("{hint}");
    }
    // Every assertion adjudicated is counted on the line, whatever the word:
    // an inconclusive assertion in a contract-free body, or one whose proof
    // lacked evidence, is unproved, and a run holding only such assertions
    // printed no proof_assert line at all.
    let logic_asserted = counters.logic_assertions_verified;
    if pa_counters.verified + logic_asserted > 0
        || pa_counters.failed > 0
        || pa_counters.errors > 0
        || pa_counters.inconclusive > 0
        || pa_counters.evidence_gaps > 0
    {
        eprintln!(
            "{}",
            format_proof_assert_summary(pa_counters, logic_asserted)
        );
    }
    let mut summary = VerificationSummary::from_counters(counters, pa_counters);
    summary.unverified_axioms = unverified_axioms.len();
    if summary.is_assumed_only() {
        eprintln!(
            "trust-wp: warning: all {} function(s) assumed without SMT proof — no contracts were verified",
            summary.assumed
        );
    }
    if summary.is_axiom_deps_only() {
        eprintln!(
            "trust-wp: warning: all {} function(s) depend on unproven axioms — no contracts were independently verified",
            summary.verified_with_axiom_deps
        );
    }
    summary
}
