// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop invariant verification.
//!
//! Implements inductive loop verification: initialization, preservation,
//! and postcondition checks for functions with loop invariants.
//!
//! # Logging policy (#1689)
//!
//! - **User-facing failure reports** (`report_loop_verification_failure`) remain
//!   as `eprintln!` until #1690 structured result path lands.
//! - **Progress/diagnostic output** (verbose-gated) uses tracing macros
//!   (`debug!`/`trace!`) controlled by `TRUST_WP_LOG` env filter.

mod encoder_config;
mod expr_utils;
mod for_loop_facts;
pub(in crate::callbacks) mod ghost_rewrite;
mod inference;
mod old_rewrite;
mod reporting;
mod single_loop;
mod span_matching;
mod transition_facts;
mod types;

use encoder_config::encoder_config_from_req;
use for_loop_facts::{
    build_for_loop_range_element_bounds, build_group_guarded_for_loop_produced_len_bound,
    build_group_guarded_for_loop_range_element_facts,
    build_group_guarded_for_loop_seq_element_facts,
    build_group_guarded_seq_for_loop_yielded_element_facts,
};
use ghost_rewrite::function_returns_ghost;
use inference::{infer_unsigned_nonneg_invariants, infer_unsigned_nonneg_requires};
// Re-export pub(super) items for the parent callbacks module.
pub(super) use reporting::report_loop_verification_failure;
use reporting::{
    combine_loop_results, emit_loop_verification_diagnostics,
    loop_verification_evidence_gap_reasons,
};
use rustc_middle::ty::TyCtxt;
use single_loop::{verify_single_loop, LoopOrchestrationData};
use span_matching::find_loop_invariants;
use tracing::{debug, debug_span};
use trust_wp_ay::{
    verify_loop_invariant_outcome, BodyEffects, EncodingError, LoopVerificationContext,
    LoopVerificationResult, VerificationResult,
};
use trust_wp_core::formula::PureExpr;
pub(super) use types::{LoopVerificationOutput, LoopWithInvariantRequest};
use types::{PerLoopConditions, PreExtractedLoopBodies};

use super::{
    super::mir_analysis::{extract_loop_body, get_mir_body, CallSpecContext},
    try_get_body_with_context, MIR_BODIES,
};

/// Verify a function with loop invariants using inductive proof.
///
/// This performs three checks for EACH loop in the function:
/// 1. Initialization: precondition => invariant
/// 2. Preservation: invariant ∧ condition => invariant' (post-iteration)
/// 3. Postcondition: invariant ∧ ¬condition => postcondition
///
/// When multiple loops exist, each is verified independently with the same
/// invariants. All loops must satisfy all three checks for verification to pass.
pub(super) fn verify_loop_with_invariant(
    tcx: TyCtxt<'_>,
    req: &LoopWithInvariantRequest<'_>,
) -> Result<LoopVerificationOutput, EncodingError> {
    let def_path = req.def_path;
    let verbose = req.verbose;
    let parsed = req.parsed;
    let contract = req.contract;
    let loop_analysis = req.loop_analysis;

    let _span = debug_span!(
        "trust_wp::verify_loop_invariant",
        def_path = %def_path,
        loc = %req.loc,
        loops = loop_analysis.loops.len(),
    )
    .entered();

    if verbose {
        debug!(
            def_path = %def_path,
            loc = %req.loc,
            loops = loop_analysis.loops.len(),
            "running loop invariant verification"
        );
    }

    // Handle empty loops case
    if loop_analysis.loops.is_empty() {
        let empty_effect_map = std::collections::HashMap::new();
        let empty_pre_loop = std::collections::HashMap::new();
        let config = encoder_config_from_req(req);
        let ctx = LoopVerificationContext::new(
            req.requires,
            req.transformed_ensures,
            &parsed.loop_fields.invariants,
            &[],
            BodyEffects::new(&empty_effect_map, &empty_effect_map, &empty_effect_map),
            &empty_pre_loop,
        )
        .with_config(config);
        let outcome = verify_loop_invariant_outcome(&ctx)?;
        emit_loop_verification_diagnostics(def_path, &outcome);
        let evidence_gap_reasons = loop_verification_evidence_gap_reasons(&outcome);
        return Ok(LoopVerificationOutput {
            result: outcome.as_result(),
            frame_constraints: Vec::new(),
            continuation_assumptions: Vec::new(),
            return_expr: None,
            post_loop_final_values: std::collections::HashMap::new(),
            effective_invariants: parsed.loop_fields.invariants.clone(),
            evidence_gap_reasons,
        });
    }

    let inferred_unsigned_invariants = MIR_BODIES.with(|state| {
        let map = state.borrow();
        map.get(&contract.local_def_id)
            .map(|body_with_facts| {
                infer_unsigned_nonneg_invariants(get_mir_body(body_with_facts), &parsed.arg_names)
            })
            .unwrap_or_default()
    });
    let inferred_unsigned_requires = MIR_BODIES.with(|state| {
        let map = state.borrow();
        map.get(&contract.local_def_id)
            .map(|body_with_facts| {
                infer_unsigned_nonneg_requires(get_mir_body(body_with_facts), &parsed.arg_names)
            })
            .unwrap_or_default()
    });
    let returns_ghost = function_returns_ghost(tcx, contract.def_id);

    // Pre-compute per-loop invariants so nested loops can inherit outer
    // loop invariants as additional assumptions. (#1295)
    let per_loop_effective_invariants: Vec<Vec<PureExpr>> = loop_analysis
        .loops
        .iter()
        .map(|li| {
            let header_byte_pos = MIR_BODIES.with(|state| {
                let map = state.borrow();
                map.get(&contract.local_def_id).map(|body_with_facts| {
                    let mir_body = get_mir_body(body_with_facts);
                    mir_body.basic_blocks[li.header]
                        .terminator()
                        .source_info
                        .span
                        .lo()
                        .0
                })
            });
            let mut invs = if let (false, Some(pos)) = (
                parsed.loop_fields.per_loop_invariants.is_empty(),
                header_byte_pos,
            ) {
                find_loop_invariants(
                    &parsed.loop_fields.per_loop_invariants,
                    &parsed.loop_fields.all_loop_spans,
                    pos,
                )
            } else {
                parsed.loop_fields.invariants.clone()
            };
            for inv in &inferred_unsigned_invariants {
                if !invs.contains(inv) {
                    invs.push(inv.clone());
                }
            }
            invs
        })
        .collect();
    // Pre-extract ALL loop bodies once with full call_spec_ctx, eliminating the
    // redundant second extraction inside the per-loop for-loop. (#2278 F7)
    // Previously, conditions were extracted in a separate pass (with None call_spec_ctx)
    // and then full bodies were re-extracted per-loop (with Some(call_spec_ctx)).
    let call_spec_ctx = CallSpecContext {
        tcx,
        user_specs: req.user_specs,
        trait_specs: req.trait_specs,
        extern_specs: req.extern_specs,
    };
    let loop_count = loop_analysis.loops.len();
    let (mut pre_extracted_bodies, per_loop_conditions): (
        PreExtractedLoopBodies,
        PerLoopConditions,
    ) = if let Some(body_with_facts) = try_get_body_with_context(contract.local_def_id) {
        let mir_body = get_mir_body(body_with_facts);
        loop_analysis
            .loops
            .iter()
            .map(|li| {
                let body_expr = extract_loop_body(
                    mir_body,
                    &parsed.arg_names,
                    li,
                    Some(&loop_analysis.loops),
                    Some(&call_spec_ctx),
                    returns_ghost,
                );
                let header_byte_pos = mir_body.basic_blocks[li.header]
                    .terminator()
                    .source_info
                    .span
                    .lo()
                    .0;
                let condition = body_expr.condition.clone();
                (Some((body_expr, header_byte_pos)), condition)
            })
            .unzip()
    } else {
        (
            (0..loop_count).map(|_| None).collect(),
            (0..loop_count).map(|_| None).collect(),
        )
    };

    let per_loop_call_obligation_facts: Vec<Vec<PureExpr>> = pre_extracted_bodies
        .iter()
        .enumerate()
        .map(|(loop_idx, body_opt)| {
            let Some((body_expr, _)) = body_opt.as_ref() else {
                return Vec::new();
            };
            let Some(state) = body_expr.for_loop_state.as_ref() else {
                return Vec::new();
            };
            let group_condition = parsed
                .loop_fields
                .loop_obligation_groups
                .get(loop_idx)
                .and_then(|group| group.condition.as_ref());
            let mut facts = build_group_guarded_for_loop_range_element_facts(
                state,
                body_expr.condition.as_ref(),
                group_condition,
            );
            facts.extend(build_group_guarded_for_loop_produced_len_bound(
                state,
                body_expr.condition.as_ref(),
                group_condition,
            ));
            facts.extend(build_group_guarded_for_loop_seq_element_facts(
                state,
                body_expr.condition.as_ref(),
                group_condition,
            ));
            facts.extend(build_group_guarded_seq_for_loop_yielded_element_facts(
                state,
                &body_expr.pre_loop_init_facts,
                body_expr.condition.as_ref(),
                group_condition,
            ));
            facts
        })
        .collect();
    let per_loop_nested_active_facts: Vec<Vec<PureExpr>> = pre_extracted_bodies
        .iter()
        .map(|body_opt| {
            body_opt
                .as_ref()
                .and_then(|(body_expr, _)| body_expr.for_loop_state.as_ref())
                .map_or_else(Vec::new, build_for_loop_range_element_bounds)
        })
        .collect();

    // Verify ALL loops, collect results (#2337: orchestrator fold).
    let mut combined_result: Option<LoopVerificationResult> = None;
    let mut frame_constraint_map: std::collections::HashMap<String, PureExpr> =
        std::collections::HashMap::new();
    let mut continuation_assumptions: Vec<PureExpr> = Vec::new();
    let mut all_modified_vars: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut last_return_expr: Option<PureExpr> = None;
    let mut accumulated_post_loop_final_values: std::collections::HashMap<String, PureExpr> =
        std::collections::HashMap::new();
    let mut accumulated_effective_invariants: Vec<PureExpr> = Vec::new();
    let mut evidence_gap_reasons = Vec::new();

    let orch = LoopOrchestrationData {
        per_loop_effective_invariants: &per_loop_effective_invariants,
        per_loop_conditions: &per_loop_conditions,
        per_loop_nested_active_facts: &per_loop_nested_active_facts,
        inferred_unsigned_invariants: &inferred_unsigned_invariants,
        inferred_unsigned_requires: &inferred_unsigned_requires,
        returns_ghost,
    };
    #[allow(clippy::needless_range_loop)]
    // loop_idx used by verify_single_loop + pre_extracted_bodies
    for loop_idx in 0..loop_analysis.loops.len() {
        let single = verify_single_loop(
            tcx,
            req,
            loop_idx,
            pre_extracted_bodies[loop_idx].take(),
            &orch,
            &mut all_modified_vars,
        )?;
        for reason in single.evidence_gap_reasons {
            evidence_gap_reasons.push(format!("loop[{loop_idx}] {reason}"));
        }

        for (name, expr) in single.frame_contributions {
            frame_constraint_map.insert(name, expr);
        }
        for assumption in single.continuation_assumptions {
            if !continuation_assumptions.contains(&assumption) {
                continuation_assumptions.push(assumption);
            }
        }
        // Accumulate effective invariants from each loop, deduplicating.
        // The call obligation checker needs the union of invariants from all
        // loops to prove call-site preconditions. (#1709)
        for inv in single.effective_invariants {
            if !accumulated_effective_invariants.contains(&inv) {
                accumulated_effective_invariants.push(inv);
            }
        }
        // Range loop elements are only bounded on active loop iterations.
        // Thread condition-guarded bounds to the output used by loop call
        // obligation checking without strengthening raw loop invariants.
        for fact in &per_loop_call_obligation_facts[loop_idx] {
            if !accumulated_effective_invariants.contains(fact) {
                accumulated_effective_invariants.push(fact.clone());
            }
        }
        last_return_expr = single.return_expr.or(last_return_expr);
        accumulated_post_loop_final_values.extend(single.post_loop_final_values);
        combined_result = Some(match combined_result {
            None => single.result,
            Some(prev) => combine_loop_results(prev, single.result),
        });
    }

    Ok(LoopVerificationOutput {
        result: combined_result.unwrap_or(LoopVerificationResult {
            initialization: VerificationResult::Verified(None),
            preservation: VerificationResult::Verified(None),
            postcondition: VerificationResult::Verified(None),
            variant_nonneg: None,
            variant_decrease: None,
        }),
        // After processing all loops, finalize frame constraints by removing
        // any entries whose variable was modified by a later loop (the
        // `all_modified_vars` filter in the loop body handles this, but a final
        // pass ensures soundness if insertion order created a stale entry).
        frame_constraints: frame_constraint_map
            .into_iter()
            .filter(|(name, _)| !all_modified_vars.contains(name))
            .map(|(_, expr)| expr)
            .collect(),
        continuation_assumptions,
        return_expr: last_return_expr,
        post_loop_final_values: accumulated_post_loop_final_values,
        effective_invariants: accumulated_effective_invariants,
        evidence_gap_reasons,
    })
}

#[cfg(test)]
mod tests;
