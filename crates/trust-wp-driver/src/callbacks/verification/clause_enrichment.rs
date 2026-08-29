// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pre-solver clause enrichment pipeline for verification (#1526 Phase 5).
//!
//! Applies all enrichment passes (const substitution, trusted assumptions,
//! forall grounding, trivial closure rewriting, type invariants, closure
//! ensures enrichment) before SMT dispatch.

use rustc_middle::ty::TyCtxt;
use tracing::trace;
use trust_wp_core::{closure::ClosureCaptureInfo, formula::PureExpr, logic::TypeInvariantDef};

use super::{
    super::{
        super::contracts::FunctionContract,
        closure_enrichment::{
            collect_trivial_closure_receivers, enrich_existentials_with_closure_ensures,
            enrich_forall_goals_with_closure_ensures, instantiate_forall_precondition_rules,
            normalize_current_closure_capture_postconditions,
            rewrite_trivial_closure_precondition_goal,
            trivialize_closure_env_resolves_in_assumptions, ClosureEnsuresEntry,
        },
        contract_rewrite::annotate_exprs_with_param_sorts,
        type_invariants::{
            build_closure_capture_invariant_requires,
            build_current_closure_self_invariant_requires, build_type_invariant_clauses,
        },
    },
    PreparedVerification,
};

/// Closure and type-invariant data for clause enrichment (#2657).
///
/// Bundles the pre-collected closure capture infos, synthesized ensures,
/// and type invariant definitions that feed into the enrichment pipeline,
/// keeping `enrich_effective_clauses` under clippy's `too_many_arguments`
/// threshold.
pub(super) struct EnrichmentData<'a> {
    pub(super) type_invariant_defs: &'a [TypeInvariantDef],
    pub(super) synthesized_closure_ensures: &'a [ClosureEnsuresEntry],
    pub(super) closure_capture_infos: &'a [ClosureCaptureInfo],
}

/// Apply clause enrichments to effective requires/ensures (#1526).
///
/// This composite function applies all pre-solver enrichment passes in order:
/// 1. Const item substitutions (named const values, tuple beta-reduction)
/// 2. Trusted proof_assert assumptions
/// 3. Forall precondition rule instantiation (grounding)
/// 4. Trivial closure receiver precondition rewriting
/// 5. Type invariant clause injection (pre + postconditions)
/// 6. Existential enrichment with concrete closure ensures
/// 7. Forall goal enrichment with concrete closure ensures
///
/// All passes mutate `effective_requires` and/or `effective_ensures` in place.
/// The function also rewrites `parsed.loop_fields.loop_call_obligations` for trivial closures.
pub(super) fn enrich_effective_clauses(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    parsed: &mut super::super::parsing::ParsedContract,
    effective_requires: &mut Vec<PureExpr>,
    effective_ensures: &mut Vec<PureExpr>,
    prep: &PreparedVerification<'_>,
    enrichment: &EnrichmentData<'_>,
) {
    let type_invariant_defs = enrichment.type_invariant_defs;
    let synthesized_closure_ensures = enrichment.synthesized_closure_ensures;
    let closure_capture_infos = enrichment.closure_capture_infos;
    // (1) Substitute named const items in contract expressions (#1588).
    // Replaces `Var("TUP", _)` with `__trust_wp_tuple2(42, 24)` etc.
    // Also performs tuple beta-reduction.
    apply_const_item_substitutions(
        parsed,
        effective_requires,
        effective_ensures,
        &prep.const_item_substitutions,
    );

    // (2) Trusted proof_assert assumptions.
    if let Some(assumptions) = prep
        .trusted_proof_assert_assumptions
        .get(&contract.local_def_id)
    {
        let assumptions =
            annotate_exprs_with_param_sorts(tcx, contract.def_id, &parsed.arg_names, assumptions);
        trace!(
            count = assumptions.len(),
            "trusted proof_assert assumption(s) injected"
        );
        effective_requires.extend(assumptions);
    }

    // (3) Ground forall precondition rules into concrete assumptions.
    let grounded_forall_preconditions = instantiate_forall_precondition_rules(effective_requires);
    if grounded_forall_preconditions > 0 {
        trace!(
            count = grounded_forall_preconditions,
            "grounded precondition assumption(s) from forall rules"
        );
    }

    // (4) Rewrite trivial closure precondition goals.
    // Concrete closures without explicit requires have vacuous preconditions.
    let trivial_closure_receivers = collect_trivial_closure_receivers(
        contract.local_def_id,
        &parsed.arg_names,
        &prep.user_specs,
    );
    trace!("trivial closure receivers: {trivial_closure_receivers:?}");
    if !trivial_closure_receivers.is_empty() {
        let mut rewritten = 0usize;
        for goal in effective_ensures.iter_mut() {
            if rewrite_trivial_closure_precondition_goal(goal, &trivial_closure_receivers) {
                rewritten += 1;
            }
        }
        for group in &mut parsed.loop_fields.loop_obligation_groups {
            for goal in &mut group.obligations {
                if rewrite_trivial_closure_precondition_goal(goal, &trivial_closure_receivers) {
                    rewritten += 1;
                }
            }
        }
        if rewritten > 0 {
            trace!(
                rewritten,
                "trivial closure precondition obligation(s) discharged"
            );
        }
    }

    // (5) Inject type invariant pre/postconditions for non-primitive types (#359).
    let (inv_requires, inv_ensures) =
        build_type_invariant_clauses(tcx, contract.def_id, &parsed.arg_names, type_invariant_defs);
    if !inv_requires.is_empty() || !inv_ensures.is_empty() {
        trace!(
            preconditions = inv_requires.len(),
            postconditions = inv_ensures.len(),
            "type invariant clauses injected",
        );
        effective_requires.extend(inv_requires);
        effective_ensures.extend(inv_ensures);
    }

    // (5b) Inject closure capture type invariant preconditions (#2257).
    // Closure captures with typed ExprSort annotations get invariant
    // assumptions as regular requires, replacing the ay-side bootstrap
    // injection that happened too late in the pipeline.
    let capture_inv_requires =
        build_closure_capture_invariant_requires(closure_capture_infos, type_invariant_defs);
    if !capture_inv_requires.is_empty() {
        trace!(
            count = capture_inv_requires.len(),
            "closure capture type invariant requires injected",
        );
        effective_requires.extend(capture_inv_requires);
    }
    let current_closure_self_inv_requires =
        build_current_closure_self_invariant_requires(closure_capture_infos, type_invariant_defs);
    if !current_closure_self_inv_requires.is_empty() {
        trace!(
            count = current_closure_self_inv_requires.len(),
            "current closure self-field type invariant requires injected",
        );
        effective_requires.extend(current_closure_self_inv_requires);
    }

    let normalized_closure_postconditions =
        normalize_current_closure_capture_postconditions(closure_capture_infos, effective_ensures);
    if normalized_closure_postconditions > 0 {
        trace!(
            normalized_closure_postconditions,
            "current closure capture postcondition(s) normalized"
        );
    }

    // (6) Enrich existential call-site assumptions with concrete closure ensures (#970).
    // ay performs only one round of E-matching (ay#1018), so quantified axioms
    // cannot chain with tuple destructor axioms.
    let enrichment_count = enrich_existentials_with_closure_ensures(
        tcx,
        contract.local_def_id,
        &prep.user_specs,
        effective_requires,
        synthesized_closure_ensures,
    );
    if enrichment_count > 0 {
        trace!(
            enrichment_count,
            "closure postcondition_mut enrichment(s) applied"
        );
    }

    // Trivialize spurious `resolve(<concrete closure env>)` conjuncts left in the
    // FnMut-adapter existential assumptions: re-resolving an already-final
    // closure env is a no-op, but ay's resolve encoding distributes an extra
    // prophecy layer over it, collapsing consecutive call layers into
    // contradictory (vacuous) premises (closures/07 test_fnmut2).
    let resolves_trivialized = trivialize_closure_env_resolves_in_assumptions(effective_requires);
    if resolves_trivialized > 0 {
        trace!(
            resolves_trivialized,
            "spurious closure-env resolve conjunct(s) trivialized"
        );
    }

    // (7) Enrich Forall postcondition goals with concrete closure ensures (#970).
    let forall_enrichment_count = enrich_forall_goals_with_closure_ensures(
        tcx,
        contract.local_def_id,
        &prep.user_specs,
        effective_ensures,
    );
    if forall_enrichment_count > 0 {
        trace!(forall_enrichment_count, "Forall goal enrichment(s) applied");
    }
}

pub(super) fn discharge_ensures_already_required(
    _requires: &[PureExpr],
    ensures: &mut Vec<PureExpr>,
) {
    ensures.retain(|ensure| !matches!(ensure, PureExpr::Bool(true)));
}

pub(super) fn apply_const_item_substitutions(
    parsed: &mut super::super::parsing::ParsedContract,
    effective_requires: &mut [PureExpr],
    effective_ensures: &mut [PureExpr],
    substitutions: &std::collections::HashMap<String, PureExpr>,
) {
    if substitutions.is_empty() {
        return;
    }

    for expr in effective_requires {
        *expr = expr.substitute(substitutions);
    }
    for expr in effective_ensures {
        *expr = expr.substitute(substitutions);
    }
    apply_const_item_substitutions_to_loop_invariants(parsed, substitutions);
}

pub(super) fn apply_const_item_substitutions_to_loop_invariants(
    parsed: &mut super::super::parsing::ParsedContract,
    substitutions: &std::collections::HashMap<String, PureExpr>,
) {
    if substitutions.is_empty() {
        return;
    }

    for expr in &mut parsed.loop_fields.invariants {
        *expr = expr.substitute(substitutions);
    }
    for (_, _, invariants) in &mut parsed.loop_fields.per_loop_invariants {
        for expr in invariants {
            *expr = expr.substitute(substitutions);
        }
    }
}
