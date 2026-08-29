// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop verification result reporting and combination.
//!
//! Handles combining multi-loop results (worst-case wins) and user-facing
//! failure output for loop invariant verification.

use trust_wp_ay::{
    LoopVerificationOutcome, LoopVerificationResult, VerificationOutcome, VerificationResult,
};

use super::super::{super::contracts::FunctionContract, helpers::report_counterexample};
use crate::callbacks::reporting::verified_evidence_gap_reason;

/// Emit per-phase loop diagnostics for result-protocol consumers.
pub(in crate::callbacks) fn emit_loop_verification_diagnostics(
    def_path: &str,
    outcome: &LoopVerificationOutcome,
) {
    crate::callbacks::reporting::emit_verification_diagnostic_if_requested(
        def_path,
        "loop_initialization",
        &outcome.initialization,
    );
    if let Some(entry_may_execute) = &outcome.entry_may_execute {
        // `loop_entry_may_execute` is a SAT *probe*, not a verification
        // obligation: a `Failed` (SAT) result means "the loop entry condition
        // is satisfiable, so the loop body may execute" — the normal case that
        // simply schedules body verification. It is NOT a proof failure (the
        // function still verifies). Emitting a `status=failed reason=counterexample`
        // diagnostic for it pollutes the output with a spurious "counterexample"
        // marker that downstream consumers (e.g. the Creusot-compat harness)
        // misread as a real failure. Only surface genuine gaps (`Unknown`:
        // timeout/solver-panic) that actually affect whether the body is
        // verified; suppress the benign `Failed`/may-execute outcome.
        if !matches!(entry_may_execute.result, VerificationResult::Failed(_)) {
            crate::callbacks::reporting::emit_verification_diagnostic_if_requested(
                def_path,
                "loop_entry_may_execute",
                entry_may_execute,
            );
        }
    }
    crate::callbacks::reporting::emit_verification_diagnostic_if_requested(
        def_path,
        "loop_preservation",
        &outcome.preservation,
    );
    crate::callbacks::reporting::emit_verification_diagnostic_if_requested(
        def_path,
        "loop_postcondition",
        &outcome.postcondition,
    );
    if let Some(variant_nonneg) = &outcome.variant_nonneg {
        crate::callbacks::reporting::emit_verification_diagnostic_if_requested(
            def_path,
            "loop_variant_nonneg",
            variant_nonneg,
        );
    }
    if let Some(variant_decrease) = &outcome.variant_decrease {
        crate::callbacks::reporting::emit_verification_diagnostic_if_requested(
            def_path,
            "loop_variant_decrease",
            variant_decrease,
        );
    }
}

pub(in crate::callbacks) fn loop_verification_evidence_gap_reasons(
    outcome: &LoopVerificationOutcome,
) -> Vec<String> {
    let mut reasons = Vec::new();
    push_phase_evidence_gap(&mut reasons, "initialization", &outcome.initialization);
    push_phase_evidence_gap(&mut reasons, "preservation", &outcome.preservation);
    push_phase_evidence_gap(&mut reasons, "postcondition", &outcome.postcondition);
    if let Some(variant_nonneg) = &outcome.variant_nonneg {
        push_phase_evidence_gap(&mut reasons, "variant_nonneg", variant_nonneg);
    }
    if let Some(variant_decrease) = &outcome.variant_decrease {
        push_phase_evidence_gap(&mut reasons, "variant_decrease", variant_decrease);
    }
    reasons
}

fn push_phase_evidence_gap(reasons: &mut Vec<String>, phase: &str, outcome: &VerificationOutcome) {
    if let Some(reason) = verified_evidence_gap_reason(outcome) {
        reasons.push(format!("{phase}: {reason}"));
    }
}

/// Combine two loop verification results, taking the worst outcome for each check.
///
/// Priority: Failed > Unknown > Verified
pub(in crate::callbacks) fn combine_loop_results(
    a: LoopVerificationResult,
    b: LoopVerificationResult,
) -> LoopVerificationResult {
    LoopVerificationResult {
        initialization: worst_result(a.initialization, b.initialization),
        preservation: worst_result(a.preservation, b.preservation),
        postcondition: worst_result(a.postcondition, b.postcondition),
        variant_nonneg: combine_optional_results(a.variant_nonneg, b.variant_nonneg),
        variant_decrease: combine_optional_results(a.variant_decrease, b.variant_decrease),
    }
}

/// Combine optional verification results, taking the worst outcome.
pub(in crate::callbacks) fn combine_optional_results(
    a: Option<VerificationResult>,
    b: Option<VerificationResult>,
) -> Option<VerificationResult> {
    match (a, b) {
        (None, None) => None,
        (Some(r), None) | (None, Some(r)) => Some(r),
        (Some(r1), Some(r2)) => Some(worst_result(r1, r2)),
    }
}

/// Return the worse of two verification results.
///
/// Priority order: Failed (worst) > Unknown > Assumed > Verified (best)
pub(in crate::callbacks) fn worst_result(
    r1: VerificationResult,
    r2: VerificationResult,
) -> VerificationResult {
    match (r1, r2) {
        (VerificationResult::Failed(counterexample), _)
        | (_, VerificationResult::Failed(counterexample)) => {
            VerificationResult::Failed(counterexample)
        }
        (VerificationResult::Unknown(reason1), VerificationResult::Unknown(reason2)) => {
            // Prefer the more specific reason (non-Unspecified wins)
            let reason = if matches!(reason1, trust_wp_ay::UnknownReason::Unspecified) {
                reason2
            } else {
                reason1
            };
            VerificationResult::Unknown(reason)
        }
        (VerificationResult::Unknown(reason), _) | (_, VerificationResult::Unknown(reason)) => {
            VerificationResult::Unknown(reason)
        }
        (VerificationResult::Assumed(reason), _) | (_, VerificationResult::Assumed(reason)) => {
            VerificationResult::Assumed(reason)
        }
        _ => VerificationResult::Verified(None),
    }
}

/// Report a loop verification failure with detailed information
pub(in crate::callbacks) fn report_loop_verification_failure(
    def_path: &str,
    loc: &str,
    contract: &FunctionContract,
    result: &LoopVerificationResult,
) {
    eprintln!("trust-wp: {def_path} FAILED ✗ (loop invariant)");
    eprintln!("  at {loc}");

    // Report which verification condition failed.
    // Assumed results emit a note (#2149) rather than silent acceptance,
    // so users know the check was not fully proven.
    match &result.initialization {
        VerificationResult::Failed(ce) => {
            eprintln!("  initialization check failed: precondition does not imply invariant");
            report_counterexample(ce);
        }
        VerificationResult::Unknown(reason) => {
            eprintln!("  initialization check: unknown ({reason})");
        }
        VerificationResult::Assumed(reason) => {
            eprintln!("  initialization check: assumed (not proven) — {reason}");
        }
        VerificationResult::Verified(_) => {}
        _ => {}
    }

    match &result.preservation {
        VerificationResult::Failed(ce) => {
            eprintln!("  preservation check failed: invariant not maintained by loop body");
            report_counterexample(ce);
        }
        VerificationResult::Unknown(reason) => {
            eprintln!("  preservation check: unknown ({reason})");
        }
        VerificationResult::Assumed(reason) => {
            eprintln!("  preservation check: assumed (not proven) — {reason}");
        }
        VerificationResult::Verified(_) => {}
        _ => {}
    }

    match &result.postcondition {
        VerificationResult::Failed(ce) => {
            eprintln!(
                "  postcondition check failed: invariant ∧ ¬condition does not imply ensures"
            );
            if !contract.ensures.is_empty() {
                eprintln!("  postcondition(s):");
                for ens in &contract.ensures {
                    eprintln!("    ensures: {ens}");
                }
            }
            report_counterexample(ce);
        }
        VerificationResult::Unknown(reason) => {
            eprintln!("  postcondition check: unknown ({reason})");
        }
        VerificationResult::Assumed(reason) => {
            eprintln!("  postcondition check: assumed (not proven) — {reason}");
        }
        VerificationResult::Verified(_) => {}
        _ => {}
    }

    // Report variant verification failures (termination proofs)
    if let Some(ref variant_result) = result.variant_nonneg {
        match variant_result {
            VerificationResult::Failed(ce) => {
                eprintln!("  variant non-negativity check failed: variant may be negative");
                report_counterexample(ce);
            }
            VerificationResult::Unknown(reason) => {
                eprintln!("  variant non-negativity check: unknown ({reason})");
            }
            VerificationResult::Assumed(reason) => {
                eprintln!("  variant non-negativity check: assumed (not proven) — {reason}");
            }
            VerificationResult::Verified(_) => {}
            _ => {}
        }
    }

    if let Some(ref variant_result) = result.variant_decrease {
        match variant_result {
            VerificationResult::Failed(ce) => {
                eprintln!("  variant decrease check failed: variant may not strictly decrease");
                report_counterexample(ce);
            }
            VerificationResult::Unknown(reason) => {
                eprintln!("  variant decrease check: unknown ({reason})");
            }
            VerificationResult::Assumed(reason) => {
                eprintln!("  variant decrease check: assumed (not proven) — {reason}");
            }
            VerificationResult::Verified(_) => {}
            _ => {}
        }
    }

    // Show invariants for context
    if !contract.invariants.is_empty() {
        eprintln!("  invariant(s):");
        for inv in &contract.invariants {
            eprintln!("    invariant: {inv}");
        }
    }
}
