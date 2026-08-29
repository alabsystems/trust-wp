// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Clause-enrichment phase of `verify_single_contract`, moved verbatim from
//! `per_contract.rs` (LOC budget, #82dcbf0 precedent): closure-capture
//! synthesis (#2151 Phase 3), clause enrichment (#1526, #2151), post-loop
//! current-invariant filtering (#2361), reborrow-prophecy premises, and the
//! `Ghost<T>` function-level ensures rewrite (#2671).

use std::collections::HashMap;

use tracing::trace;
use trust_wp_core::{closure::ClosureCaptureInfo, formula::PureExpr};

use super::{
    super::{
        super::{
            super::contracts::FunctionContract,
            closure_enrichment::{
                collect_closure_capture_infos, synthesized_ensures_from_capture_infos,
            },
            loop_verify::ghost_rewrite::{
                filter_post_loop_current_invariant_clauses, function_returns_ghost,
                rewrite_loop_ensures_for_ghost_return,
            },
            parsing::ParsedContract,
        },
        clause_enrichment::{enrich_effective_clauses, EnrichmentData},
    },
    reborrow_prophecy::build_reborrow_prophecy_premises,
    state::SharedVerificationState,
};

/// Runs the clause-enrichment phase in place. Behavior-identical to the code
/// previously inline in `verify_single_contract`.
pub(super) fn apply_clause_enrichment_phase(
    shared: &SharedVerificationState<'_, '_>,
    contract: &FunctionContract,
    parsed: &mut ParsedContract,
    effective_requires: &mut Vec<PureExpr>,
    effective_ensures: &mut Vec<PureExpr>,
    post_loop_final_values: Option<&HashMap<String, PureExpr>>,
) -> Vec<ClosureCaptureInfo> {
    let user_specs = &shared.prep.user_specs;

    // Collect closure capture infos early so synthesized ensures from
    // body effect analysis (#2151 Phase 3) are available for enrichment.
    let closure_capture_infos = collect_closure_capture_infos(
        shared.tcx,
        contract.local_def_id,
        user_specs,
        shared.config.trait_specs,
        shared.config.extern_specs,
    );
    let synth_ensures = synthesized_ensures_from_capture_infos(&closure_capture_infos);
    if !synth_ensures.is_empty() {
        trace!(
            count = synth_ensures.len(),
            "synthesized closure ensures for contract enrichment",
        );
    }

    // Apply all clause enrichment passes (#1526, #2151).
    let enrichment_data = EnrichmentData {
        type_invariant_defs: shared.config.type_invariant_defs,
        synthesized_closure_ensures: &synth_ensures,
        closure_capture_infos: &closure_capture_infos,
    };
    enrich_effective_clauses(
        shared.tcx,
        contract,
        parsed,
        effective_requires,
        effective_ensures,
        shared.prep,
        &enrichment_data,
    );
    if let Some(loop_final_values) = post_loop_final_values {
        filter_post_loop_current_invariant_clauses(effective_requires, loop_final_values);
    }

    // Synthesize the prophecy-pinning premise for a recognized recursive
    // `&mut self` match-reborrow function (rusthorn take_some). Sound: see
    // `build_reborrow_prophecy_premises`.
    if let (Some(info), Some(result_expr)) = (
        parsed.reborrow_prophecy.as_ref(),
        parsed.result_expr.as_ref(),
    ) {
        let premises = build_reborrow_prophecy_premises(result_expr, info);
        if !premises.is_empty() {
            trace!(
                count = premises.len(),
                "synthesized reborrow-prophecy premises"
            );
            effective_requires.extend(premises);
        }
    }

    // Rewrite function-level ensures for Ghost<T> return types (#2671).
    //
    // When a function returns `Ghost<T>`, postcondition clauses like `*result == x`
    // dereference the Ghost wrapper. Since Ghost<T> is transparent in the logic
    // (`*Ghost<T>` == `T`), `*result` should refer to the inner value. The loop
    // path already applies this rewrite to loop-level ensures via
    // `rewrite_loop_ensures_for_ghost_return` in single_loop.rs. This applies the
    // same rewrite to the function-level ensures so that `*result` is replaced with
    // the actual return expression (e.g., the loop body's computed value).
    if function_returns_ghost(shared.tcx, contract.def_id) {
        *effective_ensures = rewrite_loop_ensures_for_ghost_return(
            effective_ensures,
            true,
            parsed.result_expr.as_ref(),
        );
        trace!("rewrote function-level ensures for Ghost<T> return type (#2671)",);
    }

    closure_capture_infos
}
