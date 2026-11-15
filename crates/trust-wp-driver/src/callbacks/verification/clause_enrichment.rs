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
            collect_contract_free_closure_receivers, enrich_existentials_with_closure_ensures,
            enrich_forall_goals_with_closure_ensures, instantiate_forall_precondition_rules,
            normalize_current_closure_capture_postconditions,
            rewrite_contract_free_closure_precondition_goal,
            trivialize_closure_env_resolves_in_assumptions, ClosureEnsuresEntry,
            ClosurePreconditions,
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
    /// Trait and extern contracts, needed to compute a contract-free closure's
    /// body precondition over the SAME callee specs the body's own
    /// verification would see.
    pub(super) trait_specs:
        &'a std::collections::HashMap<rustc_hir::def_id::DefId, trust_wp_driver::StdSpec>,
    pub(super) extern_specs: &'a std::collections::HashMap<String, trust_wp_driver::StdSpec>,
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

    // (4) Resolve contract-free closure preconditions to their body WP.
    // A closure without `#[requires]` is transparent, not vacuous.
    let contract_free_receivers = collect_contract_free_closure_receivers(
        tcx,
        contract.local_def_id,
        &parsed.arg_names,
        &prep.user_specs,
    );
    trace!("contract-free closure receivers: {contract_free_receivers:?}");
    if !contract_free_receivers.is_empty() {
        // GOALS ONLY. `effective_requires` are ASSUMPTIONS when this contract
        // is verified, and the receiver table is keyed on the source name of a
        // closure aggregate in the BODY, while a `requires` clause can only
        // name a PARAMETER — so every hit in premise position is a name
        // collision, and rewriting there replaces the parameter's
        // uninterpreted `precondition` with a DIFFERENT closure's body WP.
        // The caller then discharges a clause about the closure it passed
        // while the callee assumed one about a local: grant and obligation in
        // different environments, which is D-54's defect one lane over.
        let closure_preconditions = ClosurePreconditions::new(
            tcx,
            &prep.user_specs,
            enrichment.trait_specs,
            enrichment.extern_specs,
        );
        let mut rewritten = 0usize;
        for goal in effective_ensures.iter_mut() {
            if rewrite_contract_free_closure_precondition_goal(
                goal,
                &contract_free_receivers,
                &closure_preconditions,
            ) {
                rewritten += 1;
            }
        }
        for group in &mut parsed.loop_fields.loop_obligation_groups {
            for goal in &mut group.obligations {
                if rewrite_contract_free_closure_precondition_goal(
                    goal,
                    &contract_free_receivers,
                    &closure_preconditions,
                ) {
                    rewritten += 1;
                }
            }
        }
        if rewritten > 0 {
            trace!(
                rewritten,
                "contract-free closure precondition(s) resolved to their body WP"
            );
        }
    }

    // (5) Inject type invariant pre/postconditions for non-primitive types (#359).
    //
    // The PRECONDITIONS are read from the callee-keyed spec table, not rebuilt
    // here. They are a premise in this body and an obligation at every call
    // site of this function; two independent computations of the same clause
    // set is precisely how a body ends up enjoying a premise no caller pays
    // for. The builder is still called for the POSTCONDITIONS, which have no
    // call-site counterpart — its precondition half is discarded unused.
    let inv_requires = prep
        .user_specs
        .get(&contract.def_id)
        .map(|spec| spec.inv_requires.clone())
        .unwrap_or_default();
    let (_discarded_requires, inv_ensures) =
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
    //
    // As with (5), the clauses are READ from the closure's spec-table entry
    // (carried on the capture info) rather than rebuilt here: they are a
    // premise in the closure's body and an obligation where the closure is
    // CONSTRUCTED, and a capture the two sides disagreed about is a premise
    // nobody pays for (D-66).
    let capture_inv_requires = build_closure_capture_invariant_requires(closure_capture_infos);
    if !capture_inv_requires.is_empty() {
        trace!(
            count = capture_inv_requires.len(),
            "closure capture type invariant requires injected",
        );
        effective_requires.extend(capture_inv_requires);
    }
    let current_closure_self_inv_requires =
        build_current_closure_self_invariant_requires(closure_capture_infos);
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
