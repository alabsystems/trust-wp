// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop-with-invariant verification dispatch and trait refinement checks.
//!
//! Contains [`LoopPathOutcome`], [`verify_contract_loop_path`], and
//! [`check_trait_refinement`]. The 4 `ContinueWithAssumptions` return sites
//! are deduplicated via [`make_continue_outcome`]. (#2321)

use std::collections::HashMap;

use trust_wp_ay::{EncodingError, LoopVerificationResult, VerificationOutcome, VerificationResult};
use trust_wp_core::formula::PureExpr;

use super::{
    super::{
        super::{
            super::contracts::{FunctionContract, TraitMethodContract},
            ghost_context::rustc_span_to_source_span,
            loop_verify::{
                report_loop_verification_failure, verify_loop_with_invariant,
                LoopWithInvariantRequest,
            },
            parsing::ParsedContract,
            reporting::{emit_verification_diagnostic_if_requested, VerificationCounters},
            trait_refinement::{verify_trait_refinement, TraitRefinementRequest},
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
}

/// Outcome of loop path dispatch (#2085).
///
/// Replaces the previous `bool` return from `verify_contract_loop_path`.
/// The three-variant design enables compositional verification: loop
/// invariant induction handles the loop body, and the normal function-level
/// path handles post-loop sequential reasoning with loop-exit state
/// injected as additional preconditions.
pub(crate) enum LoopPathOutcome {
    /// Loop verification handled everything; caller should skip function-level path.
    Handled,
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
    }
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
            ) = match loop_output {
                Ok(output) => (
                    Ok(output.result),
                    output.frame_constraints,
                    output.continuation_assumptions,
                    output.return_expr,
                    output.post_loop_final_values,
                    output.effective_invariants,
                    output.evidence_gap_reasons,
                ),
                Err(e) => (
                    Err(e),
                    Vec::new(),
                    Vec::new(),
                    None,
                    std::collections::HashMap::new(),
                    Vec::new(),
                    Vec::new(),
                ),
            };
            let loop_has_evidence_gap = !loop_evidence_gap_reasons.is_empty();
            record_loop_evidence_gaps(def_path, loc, &loop_evidence_gap_reasons, counters);

            // Use the full effective invariants (including auto-synthesized
            // structural, frame, type-invariant, and unsigned non-negative
            // invariants) for call obligation checking. Previously only
            // user-written invariants were used, causing call obligation
            // failures when auto-synthesized facts like `i >= 0` or
            // `v.len() > 0` were needed. (#1709)
            let obligation_ctx = LoopCallObligationContext {
                base_requires,
                pre_loop_assumptions: &parsed.pre_loop_call_assumptions,
                invariants: &loop_effective_invariants,
                pre_loop_obligations: pre_loop_call_obligation_ensures,
                loop_obligation_groups: &parsed.loop_fields.loop_obligation_groups,
                logic_fns_opt: vctx.logic_fns_opt,
                mode_overrides_opt: vctx.mode_overrides_opt,
                type_invariants_opt: vctx.type_invariants_opt,
                type_constants_opt: vctx.type_constants,
                adt_decls_opt: vctx.adt_decls_opt,
                track_level: vctx.track_level,
                timeout: vctx.timeout,
            };

            let mut continue_to_fn_path = false;
            let loop_cont = LoopContinuationState {
                loop_frame_constraints: &loop_frame_constraints,
                loop_continuation_assumptions: &loop_continuation_assumptions,
                loop_return_expr: &loop_return_expr,
                loop_post_final_values: &loop_post_final_values,
            };

            match loop_result {
                Ok(ref result) if result.all_verified() => {
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
                        return LoopPathOutcome::Handled;
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
                            &mut continue_to_fn_path,
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
            if continue_to_fn_path {
                return make_continue_outcome(
                    &[],
                    None,
                    &[],
                    &loop_return_expr,
                    &loop_post_final_values,
                    false,
                );
            }
            return LoopPathOutcome::Handled;
        }
        report_orphaned_loop_attributes(def_path, parsed, vctx, counters);
    } else {
        report_orphaned_loop_attributes(def_path, parsed, vctx, counters);
    }
    LoopPathOutcome::NotApplicable
}

/// Handle the `all_verified` branch of loop result dispatch.
///
/// Returns `Some(LoopPathOutcome)` if the caller should return early
/// (compositional post-loop verification), or `None` to fall through.
fn handle_all_verified(
    _result: &LoopVerificationResult,
    vctx: &VerificationContext<'_, '_>,
    parsed: &ParsedContract,
    tc: &TransformedContract,
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
        return Some(LoopPathOutcome::Handled);
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
            parsed.loop_fields.single_loop_condition(),
            loop_cont.loop_frame_constraints,
            loop_cont.loop_return_expr,
            loop_cont.loop_post_final_values,
            true,
        ));
    }

    if loop_body_verified {
        counters.verified += 1;
        eprintln!("trust-wp: {def_path} verified ✓ (loop invariant{suffix})");
        check_trait_refinement(vctx, parsed, &tc.base_requires, &tc.base_ensures, counters);
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
/// for normal processing. Sets `continue_to_fn_path` when the function-level
/// path should run without loop-exit assumptions. (#2321)
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
    continue_to_fn_path: &mut bool,
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
                    parsed.loop_fields.single_loop_condition(),
                    loop_cont.loop_frame_constraints,
                    loop_cont.loop_return_expr,
                    loop_cont.loop_post_final_values,
                    true,
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
                    counters.verified += 1;
                    eprintln!(
                        "trust-wp: {def_path} verified ✓ (loop invariant vacuous: explicit #[requires(false)])"
                    );
                    eprintln!("  at {loc}");
                    return Some(make_continue_outcome(
                        loop_cont.loop_continuation_assumptions,
                        parsed.loop_fields.single_loop_condition(),
                        loop_cont.loop_frame_constraints,
                        loop_cont.loop_return_expr,
                        loop_cont.loop_post_final_values,
                        true,
                    ));
                }
                counters.vacuous += 1;
                counters.warnings += 1;
                eprintln!("trust-wp: {def_path} vacuous (loop invariant, contradictory premises)");
                eprintln!("  at {loc}");
                return Some(make_continue_outcome(
                    loop_cont.loop_continuation_assumptions,
                    parsed.loop_fields.single_loop_condition(),
                    loop_cont.loop_frame_constraints,
                    loop_cont.loop_return_expr,
                    loop_cont.loop_post_final_values,
                    true,
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
                        parsed.loop_fields.single_loop_condition(),
                        loop_cont.loop_frame_constraints,
                        loop_cont.loop_return_expr,
                        loop_cont.loop_post_final_values,
                        true,
                    ));
                }

                eprintln!(
                    "trust-wp: {def_path} loop invariant incomplete ({reason_str}) — continuing to postcondition verification"
                );
                eprintln!("  at {loc}");
                *continue_to_fn_path = true;
            }
        }
        VerificationResult::Verified(_) => {
            counters.verified += 1;
            eprintln!("trust-wp: {def_path} verified ✓ (loop invariant)");
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

/// Check trait refinement for a verified function and adjust counters (#1986).
pub(crate) fn check_trait_refinement(
    vctx: &VerificationContext<'_, '_>,
    parsed: &ParsedContract,
    base_requires: &[PureExpr],
    base_ensures: &[PureExpr],
    counters: &mut VerificationCounters,
) {
    if !vctx
        .trait_refinement_overrides
        .contains(&vctx.contract.def_id)
    {
        return;
    }
    let Some(origin) = vctx.contract.trait_origin.as_ref() else {
        return;
    };
    let Some(trait_contract) = vctx.trait_contract_map.get(&origin.trait_def_id).and_then(
        |methods: &HashMap<String, &TraitMethodContract>| methods.get(&origin.trait_method_name),
    ) else {
        return;
    };
    let refinement_req = TraitRefinementRequest {
        impl_def_id: vctx.contract.def_id,
        impl_arg_names: &parsed.arg_names,
        trait_contract,
        base_requires,
        base_ensures,
        type_invariant_defs: vctx.type_invariants_opt.unwrap_or(&[]),
        logic_fns_opt: vctx.logic_fns_opt,
        mode_overrides_opt: vctx.mode_overrides_opt,
        adt_decls: vctx.adt_decls_opt,
        track_level: vctx.track_level,
        def_path: vctx.def_path,
        loc: vctx.loc,
        verbose: vctx.verbose,
    };
    let counts = verify_trait_refinement(vctx.tcx, &refinement_req);
    if counts.verified_delta < 0 {
        counters.verified = counters
            .verified
            .saturating_sub(counts.verified_delta.unsigned_abs() as usize);
    }
    counters.assumed += counts.assumed_delta;
    counters.failed += counts.failed_delta;
    counters.errors += counts.error_delta;
    counters.demoted += counts.demoted_delta;
    counters.evidence_gaps += counts.evidence_gap_delta;
    counters.warnings += counts.warning_delta;
    counters.encoding_errors.merge_from(&counts.encoding_errors);
}
