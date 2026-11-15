// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop-with-invariant verification dispatch and trait refinement checks.
//!
//! Contains [`LoopPathOutcome`] and [`verify_contract_loop_path`]; trait
//! refinement runs in the standalone refinement pass. The 4 `ContinueWithAssumptions` return sites
//! are deduplicated via [`make_continue_outcome`]. (#2321)

use std::collections::HashMap;

use trust_wp_ay::{EncodingError, LoopVerificationResult, VerificationOutcome, VerificationResult};
use trust_wp_core::formula::PureExpr;

use super::{
    super::{
        super::{
            super::contracts::FunctionContract,
            function_credit::{grant_function_credit, CreditKind, FunctionCredit},
            ghost_context::rustc_span_to_source_span,
            loop_verify::{
                report_loop_verification_failure, verify_loop_with_invariant,
                LoopWithInvariantRequest,
            },
            parsing::ParsedContract,
            reporting::{
                emit_verification_diagnostic_if_requested, LoopCaveats, VerificationCounters,
            },
            type_invariants::build_type_invariant_clauses,
            verification_context::VerificationContext,
        },
        contract_transform::TransformedContract,
    },
    exit_assumptions::{build_loop_exit_assumptions, should_continue_with_loop_exit_assumptions},
    obligation::{
        report_obligation_result, verify_loop_call_obligations_outcome, LoopCallObligationContext,
        ObligationOutcome,
    },
};

/// Read-only loop continuation state built once and passed to both
/// `handle_all_verified` and `handle_partial_result`, keeping their
/// signatures under clippy's `too_many_arguments` threshold. (#2657)
struct LoopContinuationState<'a> {
    loop_frame_constraints: &'a [PureExpr],
    loop_continuation_assumptions: &'a [PureExpr],
    loop_return_expr: &'a Option<PureExpr>,
    loop_post_final_values: &'a HashMap<String, PureExpr>,
    /// The single loop's condition, whose negation joins the exit facts, when
    /// every return passes through the loop (D-224); `None` otherwise.
    exit_condition: Option<&'a PureExpr>,
    /// Why that condition reads a value no premise states, if it does.
    exit_condition_unstated: Option<&'a str>,
}

/// Outcome of loop path dispatch (#2085).
///
/// The three-variant design enables compositional verification: loop
/// invariant induction handles the loop body, and the normal function-level
/// path handles post-loop sequential reasoning with loop-exit state
/// injected as additional preconditions.
pub(crate) enum LoopPathOutcome {
    /// Loop verification handled everything; caller should skip function-level path.
    ///
    /// The caller must STILL verify the function's in-function `proof_assert!`s
    /// (D-38): a caller that skips them on this arm credits
    /// `#[invariant(..)] while .. {} proof_assert!(false)` — a loop lane with no
    /// postcondition to defer — `verified ✓` with the assertion never examined
    /// (`s53_pa_false_after_loop_lane.rs`). `loop_exit_assumptions` carries the same
    /// `invariants ∧ ¬condition ∧ frame_constraints` the
    /// `ContinueWithAssumptions` lane injects, and is EMPTY unless the loop's
    /// inductive proof actually succeeded.
    Handled {
        loop_exit_assumptions: Vec<PureExpr>,
    },
    /// No loops detected or no invariants specified; fall through to normal path.
    NotApplicable,
    /// Loop invariant verified, but function has postconditions that depend on
    /// post-loop code. The caller should inject these loop-exit assumptions
    /// (loop-exit continuation facts ∧ ¬condition ∧ frame_constraints) into
    /// effective_requires and continue with the normal function-level
    /// verification path.
    ///
    /// The optional `PureExpr` is the post-loop return expression extracted from
    /// MIR blocks after the loop exit. When present, it should be set as
    /// `parsed.result_expr` so the function-level verifier can bind `result` (#2085).
    ContinueWithAssumptions {
        assumptions: Vec<PureExpr>,
        return_expr: Option<PureExpr>,
        /// Final values for `&mut` parameters written through deref after loop exit (#2085).
        post_loop_final_values: std::collections::HashMap<String, PureExpr>,
        /// What the function-level verdict must not claim about this run.
        caveats: LoopCaveats,
    },
}

/// Build a `ContinueWithAssumptions` outcome, deduplicating the 4 return sites
/// in `verify_contract_loop_path`. (#2321)
///
/// When `include_exit_assumptions` is true, builds
/// `continuation_facts ∧ ¬condition ∧ frame_constraints`.
/// When false, returns empty assumptions (used when invariant proof is incomplete).
#[allow(clippy::ref_option)] // &Option<PureExpr> matches the call-site ownership pattern
fn make_continue_outcome(
    exit_base_assumptions: &[PureExpr],
    condition: Option<&PureExpr>,
    frame_constraints: &[PureExpr],
    return_expr: &Option<PureExpr>,
    post_loop_final_values: &HashMap<String, PureExpr>,
    include_exit_assumptions: bool,
    unstated_exit_premise: Option<&str>,
) -> LoopPathOutcome {
    let assumptions = if include_exit_assumptions {
        let mut assumptions = build_loop_exit_assumptions(exit_base_assumptions, condition);
        assumptions.extend(frame_constraints.iter().cloned());
        assumptions
    } else {
        vec![]
    };
    LoopPathOutcome::ContinueWithAssumptions {
        assumptions,
        return_expr: return_expr.clone(),
        post_loop_final_values: post_loop_final_values.clone(),
        caveats: LoopCaveats {
            incomplete_loop: None,
            result_unbound: None,
            unstated_exit_premise: unstated_exit_premise
                .filter(|_| include_exit_assumptions)
                .map(|what| {
                    format!("the loop condition reads a value the loop VC does not state: {what}")
                }),
        },
    }
}

/// Build the outcome for a loop whose phases were all incomplete: the
/// function-level path runs with NO loop-exit assumptions, and records why so
/// a function-level counterexample is reported as unknown, never FAILED.
#[allow(clippy::ref_option)]
fn make_incomplete_loop_outcome(
    reason: String,
    return_expr: &Option<PureExpr>,
    post_loop_final_values: &HashMap<String, PureExpr>,
) -> LoopPathOutcome {
    let mut outcome = make_continue_outcome(
        &[],
        None,
        &[],
        return_expr,
        post_loop_final_values,
        false,
        None,
    );
    if let LoopPathOutcome::ContinueWithAssumptions { caveats, .. } = &mut outcome {
        caveats.incomplete_loop = Some(reason);
    }
    outcome
}

/// Handle the loop-with-invariant verification path for a single contract.
///
/// Returns [`LoopPathOutcome`]:
/// - `Handled`: loop verification complete, caller should skip function-level path
/// - `NotApplicable`: no loops/invariants, fall through to normal verification
/// - `ContinueWithAssumptions(assumptions)`: loop invariant verified, but
///   function postconditions need post-loop sequential reasoning. Caller should
///   inject `assumptions` into effective_requires and continue to function-level
///   verification. The assumptions include synthesized structural/completion
///   facts in addition to user-written invariants. (#2085, #2116)
pub(crate) fn verify_contract_loop_path(
    vctx: &VerificationContext<'_, '_>,
    parsed: &ParsedContract,
    tc: &TransformedContract,
    counters: &mut VerificationCounters,
) -> LoopPathOutcome {
    if parsed.loop_fields.invariants.is_empty() && parsed.loop_fields.variants.is_empty() {
        return LoopPathOutcome::NotApplicable;
    }

    let def_path = vctx.def_path;
    let loc = vctx.loc;
    let contract = vctx.contract;

    if let Some(ref loop_analysis) = parsed.loop_fields.loop_analysis {
        if loop_analysis.has_loops {
            let mut loop_base_requires = tc.base_requires.clone();
            if let Some(type_invariant_defs) = vctx.type_invariants_opt {
                for require in build_type_invariant_clauses(
                    vctx.tcx,
                    contract.def_id,
                    &parsed.arg_names,
                    type_invariant_defs,
                )
                .0
                {
                    if !loop_base_requires.contains(&require) {
                        loop_base_requires.push(require);
                    }
                }
            }
            let base_requires = loop_base_requires.as_slice();
            let base_ensures = tc.base_ensures.as_slice();
            let pre_loop_call_obligation_ensures = tc.pre_loop_call_obligation_ensures.as_slice();
            let post_loop_call_obligation_ensures = tc.post_loop_call_obligation_ensures.as_slice();
            let loop_req = LoopWithInvariantRequest {
                def_path,
                loc,
                contract,
                parsed,
                requires: base_requires,
                transformed_ensures: base_ensures,
                loop_analysis,
                type_invariants: vctx.type_invariants_opt,
                logic_fns: vctx.logic_fns_opt,
                mode_overrides: vctx.mode_overrides_opt,
                type_constants: vctx.type_constants,
                track: Some(vctx.track_level),
                verbose: vctx.verbose,
                timeout: vctx.timeout,
                user_specs: vctx.user_specs,
                trait_specs: vctx.trait_specs,
                extern_specs: vctx.extern_specs,
                adt_decls: vctx.adt_decls_opt,
                adt_field_ranges: vctx.adt_field_ranges_opt,
            };
            let loop_output = verify_loop_with_invariant(vctx.tcx, &loop_req);
            let (
                loop_result,
                loop_frame_constraints,
                loop_continuation_assumptions,
                loop_return_expr,
                loop_post_final_values,
                loop_effective_invariants,
                loop_evidence_gap_reasons,
                exit_condition_holds_at_return,
            ) = match loop_output {
                Ok(output) => (
                    Ok(output.result),
                    output.frame_constraints,
                    output.continuation_assumptions,
                    output.return_expr,
                    output.post_loop_final_values,
                    output.per_loop_effective_invariants,
                    output.evidence_gap_reasons,
                    output.exit_condition_holds_at_return,
                ),
                Err(e) => (
                    Err(e),
                    Vec::new(),
                    Vec::new(),
                    None,
                    std::collections::HashMap::new(),
                    Vec::new(),
                    Vec::new(),
                    false,
                ),
            };
            let loop_has_evidence_gap = !loop_evidence_gap_reasons.is_empty();
            record_loop_evidence_gaps(def_path, loc, &loop_evidence_gap_reasons, counters);

            // Use the full effective invariants (including auto-synthesized
            // structural, frame, type-invariant, and unsigned non-negative
            // invariants) for call obligation checking: the user-written
            // invariants alone leave call obligations that need synthesized
            // facts like `i >= 0` or `v.len() > 0` unprovable. (#1709)
            let obligation_ctx = LoopCallObligationContext {
                base_requires,
                pre_loop_assumptions: &parsed.pre_loop_call_assumptions,
                per_loop_invariants: &loop_effective_invariants,
                pre_loop_obligations: pre_loop_call_obligation_ensures,
                loop_obligation_groups: &parsed.loop_fields.loop_obligation_groups,
                logic_fns_opt: vctx.logic_fns_opt,
                mode_overrides_opt: vctx.mode_overrides_opt,
                type_invariants_opt: vctx.type_invariants_opt,
                type_constants_opt: vctx.type_constants,
                adt_decls_opt: vctx.adt_decls_opt,
                adt_field_ranges_opt: vctx.adt_field_ranges_opt,
                track_level: vctx.track_level,
                timeout: vctx.timeout,
            };

            let mut incomplete_loop_reason: Option<String> = None;
            let exit_condition = parsed
                .loop_fields
                .single_loop_condition()
                .filter(|_| exit_condition_holds_at_return);
            let loop_cont = LoopContinuationState {
                loop_frame_constraints: &loop_frame_constraints,
                loop_continuation_assumptions: &loop_continuation_assumptions,
                loop_return_expr: &loop_return_expr,
                loop_post_final_values: &loop_post_final_values,
                exit_condition,
                exit_condition_unstated: parsed
                    .loop_fields
                    .single_loop_condition_unstated()
                    .filter(|_| exit_condition.is_some()),
            };

            // Whether the loop's inductive proof succeeded: gates the loop-exit
            // premise offered to the in-function assertion lane (D-38).
            let mut loop_all_verified = false;
            match loop_result {
                Ok(ref result) if result.all_verified() => {
                    loop_all_verified = true;
                    if let Some(outcome) = handle_all_verified(
                        result,
                        vctx,
                        parsed,
                        tc,
                        base_ensures,
                        pre_loop_call_obligation_ensures,
                        post_loop_call_obligation_ensures,
                        &obligation_ctx,
                        &loop_cont,
                        loop_has_evidence_gap,
                        counters,
                    ) {
                        return outcome;
                    }
                }
                Ok(ref result) => {
                    let has_obligations = !pre_loop_call_obligation_ensures.is_empty()
                        || parsed
                            .loop_fields
                            .loop_obligation_groups
                            .iter()
                            .any(|g| !g.obligations.is_empty());
                    let obligation_failed = if has_obligations {
                        matches!(
                            report_obligation_result(
                                verify_loop_call_obligations_with_diagnostics(
                                    &obligation_ctx,
                                    vctx,
                                ),
                                vctx,
                                counters,
                            ),
                            ObligationOutcome::ErrorRecorded
                                | ObligationOutcome::Vacuous
                                | ObligationOutcome::EvidenceGap
                                | ObligationOutcome::Assumed(_)
                        )
                    } else {
                        false
                    };
                    if loop_has_evidence_gap
                        && !matches!(result.overall(), VerificationResult::Failed(_))
                    {
                        // An evidence gap means the invariant is NOT established
                        // evidence: the assertions are checked with no loop-exit
                        // premise at all.
                        return LoopPathOutcome::Handled {
                            loop_exit_assumptions: Vec::new(),
                        };
                    }
                    if !obligation_failed {
                        if let Some(outcome) = handle_partial_result(
                            result,
                            def_path,
                            loc,
                            contract,
                            parsed,
                            base_ensures,
                            post_loop_call_obligation_ensures,
                            &loop_cont,
                            counters,
                            &mut incomplete_loop_reason,
                        ) {
                            return outcome;
                        }
                    }
                }
                Err(e) => {
                    counters.encoding_errors.record(&e);
                    let e = match rustc_span_to_source_span(
                        vctx.tcx.sess.source_map(),
                        vctx.tcx.def_span(contract.def_id),
                    ) {
                        Some(src_span) => e.with_span(src_span),
                        None => e,
                    };
                    counters.errors += 1;
                    eprintln!("trust-wp: {def_path} error: {e}");
                    eprintln!("  at {loc}");
                }
            }
            if let Some(reason) = incomplete_loop_reason {
                return make_incomplete_loop_outcome(
                    reason,
                    &loop_return_expr,
                    &loop_post_final_values,
                );
            }
            // The in-function `proof_assert!`s still have to be checked by the
            // caller (D-38). The loop-exit premise is offered only when the
            // inductive proof succeeded and left no evidence gap — exactly the
            // condition the `ContinueWithAssumptions` lane already requires.
            let loop_invariant_proven = loop_all_verified && !loop_has_evidence_gap;
            return LoopPathOutcome::Handled {
                loop_exit_assumptions: if loop_invariant_proven {
                    let mut assumptions = build_loop_exit_assumptions(
                        loop_cont.loop_continuation_assumptions,
                        loop_cont.exit_condition,
                    );
                    assumptions.extend(loop_cont.loop_frame_constraints.iter().cloned());
                    assumptions
                } else {
                    Vec::new()
                },
            };
        }
        report_orphaned_loop_attributes(def_path, parsed, vctx, counters);
    } else {
        report_orphaned_loop_attributes(def_path, parsed, vctx, counters);
    }
    LoopPathOutcome::NotApplicable
}

/// Credit a function contract verified by the loop lane (`LoopPathOutcome::
/// Handled`), unless function-body context extraction gave up before every
/// obligation site was walked (`ParsedContract::extraction_fail_closed_reason`).
///
/// The loop lane's pre-/post-loop obligation walkers are separate from context
/// extraction, but nothing guarantees they revisit every block that extraction
/// skipped past a real (non-cycle) gap. The function-level path demotes such a
/// `Verified` verdict in `per_contract.rs`; this is the same fail-closed rule
/// for verdicts that return early through `Handled` and never reach it.
fn report_loop_lane_verified(
    parsed: &ParsedContract,
    def_path: &str,
    loc: &str,
    suffix: &str,
    counters: &mut VerificationCounters,
) {
    if let Some(gap) = parsed.extraction_fail_closed_reason.as_deref() {
        counters.errors += 1;
        counters.demoted += 1;
        eprintln!(
            "trust-wp: {def_path} unknown (loop invariant{suffix}: demoted: body extraction incomplete ({gap}); obligations past the gap were not walked)"
        );
        eprintln!("  at {loc}");
        return;
    }
    grant_function_credit(
        counters,
        FunctionCredit::new(
            CreditKind::Verified { native_only: false },
            format!("trust-wp: {def_path} verified ✓ (loop invariant{suffix})"),
        ),
    );
}

/// Handle the `all_verified` branch of loop result dispatch.
///
/// Returns `Some(LoopPathOutcome)` if the caller should return early
/// (compositional post-loop verification), or `None` to fall through.
fn handle_all_verified(
    _result: &LoopVerificationResult,
    vctx: &VerificationContext<'_, '_>,
    parsed: &ParsedContract,
    _tc: &TransformedContract,
    base_ensures: &[PureExpr],
    pre_loop_call_obligation_ensures: &[PureExpr],
    post_loop_call_obligation_ensures: &[PureExpr],
    obligation_ctx: &LoopCallObligationContext<'_>,
    loop_cont: &LoopContinuationState<'_>,
    loop_has_evidence_gap: bool,
    counters: &mut VerificationCounters,
) -> Option<LoopPathOutcome> {
    let def_path = vctx.def_path;

    let has_any_obligations = !pre_loop_call_obligation_ensures.is_empty()
        || parsed
            .loop_fields
            .loop_obligation_groups
            .iter()
            .any(|g| !g.obligations.is_empty());
    let suffix = if has_any_obligations {
        " + call obligations"
    } else {
        ""
    };
    let loop_body_verified = if has_any_obligations {
        match report_obligation_result(
            verify_loop_call_obligations_with_diagnostics(obligation_ctx, vctx),
            vctx,
            counters,
        ) {
            ObligationOutcome::ErrorRecorded => false,
            ObligationOutcome::Vacuous => false,
            ObligationOutcome::EvidenceGap => false,
            ObligationOutcome::Verified => true,
            ObligationOutcome::Assumed(_) => false,
        }
    } else {
        true
    };

    if loop_has_evidence_gap {
        // No loop-exit premise: an evidence gap is not a proof of the invariant.
        return Some(LoopPathOutcome::Handled {
            loop_exit_assumptions: Vec::new(),
        });
    }

    // Compositional post-loop verification (#2085).
    if loop_body_verified
        && (!base_ensures.is_empty() || !post_loop_call_obligation_ensures.is_empty())
    {
        eprintln!(
            "trust-wp: {def_path} loop invariant{suffix} verified ✓ — continuing to post-loop verification"
        );
        return Some(make_continue_outcome(
            loop_cont.loop_continuation_assumptions,
            loop_cont.exit_condition,
            loop_cont.loop_frame_constraints,
            loop_cont.loop_return_expr,
            loop_cont.loop_post_final_values,
            true,
            loop_cont.exit_condition_unstated,
        ));
    }

    if loop_body_verified {
        report_loop_lane_verified(parsed, def_path, vctx.loc, &suffix, counters);
    }

    None
}

fn record_loop_evidence_gaps(
    def_path: &str,
    loc: &str,
    reasons: &[String],
    counters: &mut VerificationCounters,
) {
    for reason in reasons {
        counters.evidence_gaps += 1;
        counters.warnings += 1;
        eprintln!("trust-wp: {def_path} evidence gap (loop invariant: {reason})");
        eprintln!("  at {loc}");
    }
}

fn verify_loop_call_obligations_with_diagnostics(
    obligation_ctx: &LoopCallObligationContext<'_>,
    vctx: &VerificationContext<'_, '_>,
) -> Result<VerificationOutcome, EncodingError> {
    let outcome = verify_loop_call_obligations_outcome(obligation_ctx)?;
    emit_verification_diagnostic_if_requested(vctx.def_path, "loop_call_obligation", &outcome);
    Ok(outcome)
}

/// Handle partial loop verification results (not all_verified).
///
/// Returns `Some(LoopPathOutcome)` for compositional continuation, `None`
/// for normal processing. Sets `incomplete_loop_reason` when the function-level
/// path should run without loop-exit assumptions (#2321); the reason makes a
/// function-level counterexample report as unknown, not FAILED.
fn handle_partial_result(
    result: &LoopVerificationResult,
    def_path: &str,
    loc: &str,
    contract: &FunctionContract,
    parsed: &ParsedContract,
    base_ensures: &[PureExpr],
    post_loop_call_obligation_ensures: &[PureExpr],
    loop_cont: &LoopContinuationState<'_>,
    counters: &mut VerificationCounters,
    incomplete_loop_reason: &mut Option<String>,
) -> Option<LoopPathOutcome> {
    match result.overall() {
        VerificationResult::Failed(_) => {
            if should_continue_with_loop_exit_assumptions(result)
                && (!base_ensures.is_empty() || !post_loop_call_obligation_ensures.is_empty())
            {
                eprintln!(
                    "trust-wp: {def_path} loop induction verified ✓, postcondition deferred to function-level path"
                );
                eprintln!("  at {loc}");
                return Some(make_continue_outcome(
                    loop_cont.loop_continuation_assumptions,
                    loop_cont.exit_condition,
                    loop_cont.loop_frame_constraints,
                    loop_cont.loop_return_expr,
                    loop_cont.loop_post_final_values,
                    true,
                    loop_cont.exit_condition_unstated,
                ));
            }

            counters.failed += 1;
            report_loop_verification_failure(def_path, loc, contract, result);
        }
        VerificationResult::Unknown(ref reason) => {
            // Vacuous proofs indicate contradictory premises — do NOT
            // count as verified (#2663). Loop invariant verification
            // continues (the invariant is assumed for subsequent checks)
            // but the result is not counted as proven.
            let is_vacuous = matches!(
                reason,
                trust_wp_ay::UnknownReason::SolverMessage(msg) if msg.contains("vacuous proof")
            );
            if is_vacuous {
                // A loop inside a function with an explicit user-authored
                // `#[requires(false)]` is unreachable: the function is provably
                // uncallable, so the vacuous loop-invariant obligation is
                // vacuously discharged by Creusot semantics and must be
                // credited, not flagged as a soundness gap. Keyed to the
                // PRECONDITION position only (does NOT credit `#[ensures(false)]`).
                if crate::callbacks::reporting::user_authored_requires_false(contract) {
                    grant_function_credit(
                        counters,
                        FunctionCredit::new(
                            CreditKind::Verified { native_only: false },
                            format!(
                                "trust-wp: {def_path} verified ✓ (loop invariant vacuous: explicit #[requires(false)])"
                            ),
                        )
                        .with_line(format!("  at {loc}")),
                    );
                    return Some(make_continue_outcome(
                        loop_cont.loop_continuation_assumptions,
                        loop_cont.exit_condition,
                        loop_cont.loop_frame_constraints,
                        loop_cont.loop_return_expr,
                        loop_cont.loop_post_final_values,
                        true,
                        loop_cont.exit_condition_unstated,
                    ));
                }
                counters.vacuous += 1;
                counters.warnings += 1;
                eprintln!("trust-wp: {def_path} vacuous (loop invariant, contradictory premises)");
                eprintln!("  at {loc}");
                return Some(make_continue_outcome(
                    loop_cont.loop_continuation_assumptions,
                    loop_cont.exit_condition,
                    loop_cont.loop_frame_constraints,
                    loop_cont.loop_return_expr,
                    loop_cont.loop_post_final_values,
                    true,
                    loop_cont.exit_condition_unstated,
                ));
            }
            let is_demoted = matches!(reason, trust_wp_ay::UnknownReason::Demoted(_));
            if base_ensures.is_empty() && post_loop_call_obligation_ensures.is_empty() {
                counters.errors += 1;
                if is_demoted {
                    counters.demoted += 1;
                }
                eprintln!("trust-wp: {def_path} unknown (loop invariant: {reason})");
                eprintln!("  at {loc}");
            } else {
                let reason_str = reason.as_str();
                if should_continue_with_loop_exit_assumptions(result) {
                    eprintln!(
                        "trust-wp: {def_path} loop induction verified ✓, \
                         postcondition incomplete ({reason_str}) — deferring \
                         to function-level path"
                    );
                    eprintln!("  at {loc}");
                    return Some(make_continue_outcome(
                        loop_cont.loop_continuation_assumptions,
                        loop_cont.exit_condition,
                        loop_cont.loop_frame_constraints,
                        loop_cont.loop_return_expr,
                        loop_cont.loop_post_final_values,
                        true,
                        loop_cont.exit_condition_unstated,
                    ));
                }

                eprintln!(
                    "trust-wp: {def_path} loop invariant incomplete ({reason_str}) — continuing to postcondition verification"
                );
                eprintln!("  at {loc}");
                *incomplete_loop_reason = Some(format!("loop invariant {reason_str}"));
            }
        }
        VerificationResult::Verified(_) => {
            report_loop_lane_verified(parsed, def_path, loc, "", counters);
        }
        VerificationResult::Assumed(ref reason) => {
            counters.assumed += 1;
            eprintln!("trust-wp: {def_path} assumed (loop invariant: {reason})");
            eprintln!("  at {loc}");
        }
        #[allow(unreachable_patterns)]
        _ => {
            counters.errors += 1;
            eprintln!("  at {loc}");
        }
    }
    None
}

/// Report orphaned loop attributes (#2122) when loops are specified but
/// no actual loops are found.
fn report_orphaned_loop_attributes(
    def_path: &str,
    parsed: &ParsedContract,
    vctx: &VerificationContext<'_, '_>,
    counters: &mut VerificationCounters,
) {
    if !parsed.loop_fields.invariants.is_empty() {
        counters.errors += 1;
        eprintln!(
            "trust-wp: error: {} has {} invariant(s) but no loops detected (invariants not checked)",
            def_path,
            parsed.loop_fields.invariants.len()
        );
    }
    if !parsed.loop_fields.variants.is_empty()
        && !vctx.recursive_fns.contains(&vctx.contract.def_id)
    {
        counters.errors += 1;
        eprintln!(
            "trust-wp: error: {} has {} variant(s) but no loops detected (variants not checked)",
            def_path,
            parsed.loop_fields.variants.len()
        );
    }
}

#[cfg(test)]
mod incomplete_loop_outcome_tests {
    use std::collections::HashMap;

    use super::{make_continue_outcome, make_incomplete_loop_outcome, LoopPathOutcome};

    #[test]
    fn incomplete_loop_outcome_carries_reason_and_no_loop_assumptions() {
        let outcome = make_incomplete_loop_outcome(
            "loop invariant timeout".to_string(),
            &None,
            &HashMap::new(),
        );
        match outcome {
            LoopPathOutcome::ContinueWithAssumptions {
                assumptions,
                caveats,
                ..
            } => {
                assert!(
                    assumptions.is_empty(),
                    "an unproven invariant must not be assumed"
                );
                assert_eq!(
                    caveats.incomplete_loop.as_deref(),
                    Some("loop invariant timeout")
                );
            }
            _ => panic!("expected ContinueWithAssumptions"),
        }
    }

    #[test]
    fn proven_loop_continuation_is_not_marked_incomplete() {
        let outcome = make_continue_outcome(&[], None, &[], &None, &HashMap::new(), true, None);
        match outcome {
            LoopPathOutcome::ContinueWithAssumptions { caveats, .. } => {
                assert!(caveats.incomplete_loop.is_none());
            }
            _ => panic!("expected ContinueWithAssumptions"),
        }
    }
}
