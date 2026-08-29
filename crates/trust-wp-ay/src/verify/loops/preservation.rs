// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preservation verification for loops.
//!
//! Implements the inductive step: invariant /\ condition => invariant'
//! (after one loop iteration, the invariant still holds).

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::{
    formula::{BinOp, ExprSort, PureExpr},
    logic::{LogicFnDef, LogicMode},
};

use super::{
    super::{
        assert_eager_negated_existential_instantiations, assert_standard_axioms, demote_if_unsound,
        encode_and_assert_negated_postconditions, obligation_slices, try_axiom_free_solve,
        Counterexample, VerificationOutcome, VerificationResult,
    },
    encoder_setup::{
        assert_loop_current_chain_alias_constraints, collect_loop_sort_plan,
        encode_and_assert_condition, setup_loop_encoder, solve_scoped_loop_obligation_outcome,
        OutcomeContinuation,
    },
    expr_helpers::{collect_expr_var_names, expr_references_any_var},
    invariant_transforms::{
        inject_forall_triggers, normalize_fmap_get_biconditional, relax_single_var_multitriggers,
    },
    prime_substitutions::{
        assert_deref_prophecy_bridge, build_prime_substitutions, is_cons_tail_self_reborrow,
    },
    recursive_unfolding::assert_recursive_fn_unfoldings,
    BodyEffects, LoopEncoderConfig, LoopVcBase,
};
use crate::{
    encoder::{sort_context::DerivedKind, unsoundness, AYEncoder},
    error::EncodingError,
    expr::{expr_has_closure_spec_method, expr_has_datatype_spec_method},
};

/// Positional-parameter entry point for preservation verification (test-only).
///
/// Wraps [`verify_preservation_with_config`] with default body-break mode
/// (header condition) and empty deref/double-deref effect maps.
///
/// # Errors
///
/// Returns `EncodingError` if expression encoding fails.
#[cfg(test)]
pub(crate) fn verify_preservation(
    invariants: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    modified_vars: &[&str],
    body_effect: &HashMap<String, PureExpr>,
    config: &LoopEncoderConfig<'_>,
) -> Result<VerificationResult, EncodingError> {
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();
    let base = LoopVcBase {
        invariants,
        loop_condition,
        condition_is_body_break: false, // header condition (test helper default)
        modified_vars,
        effects: BodyEffects::new(body_effect, &empty_deref, &empty_double_deref),
        config,
    };
    verify_preservation_with_config(&base)
}

/// Verify loop preservation: invariant /\ condition => invariant'.
///
/// # Contracts
///
/// ```text
/// REQUIRES: All expressions in invariants are well-formed.
/// REQUIRES: body_effect correctly represents loop body's effect on modified_vars.
/// REQUIRES: loop_condition (if Some) represents the loop continuation test.
///
/// ENSURES (Soundness): If Ok(Verified), then:
///     invariants /\ loop_condition => invariants[modified_vars := body_effect]
///     is valid. The loop body preserves the invariant.
///
/// ENSURES (Completeness): If Ok(Failed(ce)), ce witnesses a preservation violation.
///
/// ENSURES (Unknown): If Ok(Unknown), the solver could not determine validity.
///     No soundness guarantee in this case.
///
/// ENSURES (Error): Result is Err only if encoding fails (expression not supported).
/// ```
///
/// The invariant' uses primed variables to represent post-iteration state.
/// We substitute `body_effect[var]` for `var'` in the primed invariant.
///
/// # Errors
///
/// Returns `EncodingError` if expression encoding fails.
#[allow(clippy::too_many_lines)] // Loop preservation VC with vacuity guard, primed substitution, and obligation slicing
pub(in crate::verify::loops) fn verify_preservation_with_config(
    base: &LoopVcBase<'_>,
) -> Result<VerificationResult, EncodingError> {
    Ok(verify_preservation_with_config_outcome(base)?.result)
}

pub(in crate::verify::loops) fn verify_preservation_with_config_outcome(
    base: &LoopVcBase<'_>,
) -> Result<VerificationOutcome, EncodingError> {
    let invariants = base.invariants;
    let loop_condition = base.loop_condition;
    let condition_is_body_break = base.condition_is_body_break;
    let modified_vars = base.modified_vars;
    let effects = base.effects;
    let config = base.config;
    let base_snapshot = unsoundness::snapshot();
    if invariants.is_empty() {
        return super::encoder_setup::prove_empty_preservation_outcome(config)
            .map(|outcome| demote_outcome_if_unsound(&base_snapshot, outcome));
    }

    // Early vacuity guard (#2440, #2628): check if invariants + effective
    // condition + effect constraints are contradictory. For body-break loops,
    // use the primed condition and include effect equalities so primed names
    // are constrained in the bootstrap encoder.
    {
        let mut base_exprs: Vec<PureExpr> = invariants.to_vec();
        let mut condition_free_base_exprs: Vec<PureExpr> = invariants.to_vec();
        if let Some(cond) = loop_condition {
            if condition_is_body_break {
                // PureExpr-level name substitution for body-break priming.
                // Unlike variant.rs, we cannot use build_prime_substitutions
                // here because the encoder is not yet created (it's per-slice).
                let modified_set: HashSet<&str> = modified_vars.iter().copied().collect();
                let prime_name_map: HashMap<String, PureExpr> = modified_vars
                    .iter()
                    .map(|v| {
                        (
                            v.to_string(),
                            PureExpr::Var(DerivedKind::Prime.format_name(v), None),
                        )
                    })
                    .collect();
                base_exprs.push(cond.substitute_filtered(&modified_set, &prime_name_map));
                // Include effect equalities so primed names are constrained (#2621 lesson).
                for (var, effect_expr) in effects.direct {
                    let prime_name = DerivedKind::Prime.format_name(var);
                    let effect_equality = PureExpr::BinOp(
                        Arc::new(PureExpr::Var(prime_name, None)),
                        BinOp::Eq,
                        Arc::new(effect_expr.clone()),
                    );
                    condition_free_base_exprs.push(effect_equality.clone());
                    base_exprs.push(effect_equality);
                }
            } else {
                base_exprs.push(cond.clone());
            }
        }
        base_exprs.extend(config.transition_facts.iter().cloned());
        base_exprs.extend(config.bridge_facts.iter().cloned());
        condition_free_base_exprs.extend(config.transition_facts.iter().cloned());
        condition_free_base_exprs.extend(config.bridge_facts.iter().cloned());
        if super::encoder_setup::is_base_vacuous(&base_exprs) {
            let result = if condition_is_body_break
                || super::encoder_setup::is_base_vacuous(&condition_free_base_exprs)
            {
                VerificationResult::Unknown(crate::verify::UnknownReason::SolverMessage(
                    crate::verify::solver_tail::VACUOUS_PROOF_MESSAGE.to_string(),
                ))
            } else {
                VerificationResult::Verified(None)
            };
            if matches!(result, VerificationResult::Verified(_)) {
                return super::encoder_setup::prove_structural_loop_goal_outcome(
                    config,
                    "__trust_wp_loop_preservation_vacuous_condition_structural",
                )
                .map(|outcome| demote_outcome_if_unsound(&base_snapshot, outcome));
            }
            return Ok(VerificationOutcome::without_provenance(demote_if_unsound(
                &base_snapshot,
                result,
            )));
        }
    }

    // Normalize doubly-quantified FMap get/Some biconditionals to
    // singly-quantified form. This eliminates the inner value quantifier
    // variable that has no trigger coverage for E-matching. (#2116)
    let normalized_invariants: Vec<PureExpr> = invariants
        .iter()
        .map(normalize_fmap_get_biconditional)
        .collect();

    // Pre-synthesize triggers for triggerless forall/exists in invariants at
    // the PureExpr level. This ensures ay-dpll's E-matching receives explicit
    // triggers rather than relying on encoding-time synthesis which is
    // non-deterministic for nested quantifier proofs. (#2116)
    let triggered_invariants: Vec<PureExpr> = normalized_invariants
        .iter()
        .map(inject_forall_triggers)
        .collect();

    // Demote recursive Open-mode logic functions to Default (opaque) for the
    // preservation encoder. The quantified defining axiom `forall n: f(n) = body`
    // floods ay-dpll's E-matching with recursive functions, causing timeouts on
    // preservation VCs that are provable from ground unfoldings alone. The
    // one-step unfoldings from `assert_recursive_fn_unfoldings` (step 5b below)
    // provide the needed semantic content without the E-matching overhead. (#994)
    //
    // Non-recursive Open functions keep their mode — their defining axioms are
    // well-behaved under E-matching and may be needed by the solver.
    let recursive_demoted_modes: Option<Vec<LogicMode>> = config.logic_fns.and_then(|fns| {
        #[allow(clippy::redundant_closure_for_method_calls)] // complex type paths hurt readability
        let modes = config.mode_overrides.map_or_else(
            || fns.iter().map(|f| f.mode()).collect::<Vec<_>>(),
            |m| m.to_vec(),
        );
        let has_recursive_open = fns
            .iter()
            .zip(modes.iter())
            .any(|(f, m)| f.is_recursive() && matches!(m, LogicMode::Open | LogicMode::OpenSelf));
        if has_recursive_open {
            Some(
                fns.iter()
                    .zip(modes)
                    .map(|(f, m)| {
                        if f.is_recursive() && matches!(m, LogicMode::Open | LogicMode::OpenSelf) {
                            LogicMode::Default
                        } else {
                            m
                        }
                    })
                    .collect(),
            )
        } else {
            None
        }
    });
    let preservation_config = if let Some(ref demoted) = recursive_demoted_modes {
        LoopEncoderConfig {
            type_invariants: config.type_invariants,
            logic_fns: config.logic_fns,
            mode_overrides: Some(demoted),
            type_constants: config.type_constants,
            track: config.track,
            timeout: config.timeout,
            transition_facts: config.transition_facts.clone(),
            bridge_facts: config.bridge_facts.clone(),
            adt_decls: config.adt_decls,
            adt_field_ranges: config.adt_field_ranges,
            loop_element_borrow_vars: config.loop_element_borrow_vars.clone(),
        }
    } else {
        LoopEncoderConfig {
            type_invariants: config.type_invariants,
            logic_fns: config.logic_fns,
            mode_overrides: config.mode_overrides,
            type_constants: config.type_constants,
            track: config.track,
            timeout: config.timeout,
            transition_facts: config.transition_facts.clone(),
            bridge_facts: config.bridge_facts.clone(),
            adt_decls: config.adt_decls,
            adt_field_ranges: config.adt_field_ranges,
            loop_element_borrow_vars: config.loop_element_borrow_vars.clone(),
        }
    };

    let current_slices = obligation_slices::split_ensures(&normalized_invariants);
    let triggered_slices = obligation_slices::split_ensures(&triggered_invariants);
    let split_invariant_exprs: Vec<&PureExpr> = triggered_slices
        .iter()
        .map(|slice| slice.ensure.as_ref())
        .collect();
    let ground_hashmap_list_universals =
        hashmap_list_loop_forall_grounding_enabled(config, &normalized_invariants);
    let invariant_exprs_have_source_axiom_demand = normalized_invariants
        .iter()
        .any(expr_has_source_axiom_demand);
    let loop_condition_has_source_axiom_demand = loop_condition
        .map(expr_has_source_axiom_demand)
        .unwrap_or(false);
    let mut slice_results: Vec<obligation_slices::SliceOutcome> =
        Vec::with_capacity(current_slices.len());

    for (current_slice, triggered_slice) in current_slices.iter().zip(triggered_slices.iter()) {
        let mut reachable_names: HashSet<String> = HashSet::new();
        let mut slice_names = HashSet::new();
        collect_expr_var_names(current_slice.ensure.as_ref(), &mut slice_names);
        reachable_names.extend(slice_names.into_iter().map(str::to_string));
        if condition_is_body_break {
            if let Some(cond) = loop_condition {
                let mut cond_names = HashSet::new();
                collect_expr_var_names(cond, &mut cond_names);
                reachable_names.extend(cond_names.into_iter().map(str::to_string));
            }
        }

        let mut relevant_modified_names: HashSet<String> = modified_vars
            .iter()
            .copied()
            .filter(|var_name| reachable_names.contains(*var_name))
            .map(str::to_string)
            .collect();
        let mut slice_bridge_facts = Vec::new();
        let mut remaining_bridge_facts: Vec<&PureExpr> = config.bridge_facts.iter().collect();

        loop {
            let reachable_name_refs: HashSet<&str> =
                reachable_names.iter().map(String::as_str).collect();
            let mut still_remaining = Vec::new();
            // Batch discovered names to avoid conflicting borrows on reachable_names.
            let mut discovered_names: Vec<String> = Vec::new();

            for fact in remaining_bridge_facts {
                if expr_references_any_var(fact, &reachable_name_refs) {
                    slice_bridge_facts.push(fact.clone());
                    let mut fact_names = HashSet::new();
                    collect_expr_var_names(fact, &mut fact_names);
                    discovered_names.extend(fact_names.into_iter().map(str::to_string));
                } else {
                    still_remaining.push(fact);
                }
            }

            let mut changed = false;
            for name in discovered_names {
                if modified_vars.contains(&name.as_str())
                    && relevant_modified_names.insert(name.clone())
                {
                    changed = true;
                }
                if reachable_names.insert(name) {
                    changed = true;
                }
            }

            if !changed {
                break;
            }
            remaining_bridge_facts = still_remaining;
        }

        let relevant_modified_vars: Vec<&str> = modified_vars
            .iter()
            .copied()
            .filter(|var_name| relevant_modified_names.contains(*var_name))
            .collect();
        let mut relevant_modified_vars = relevant_modified_vars;
        for var_name in effects
            .deref
            .keys()
            .chain(effects.double_deref.keys())
            .map(String::as_str)
        {
            if (reachable_names.contains(var_name)
                || expr_mentions_var_syntactically(current_slice.ensure.as_ref(), var_name))
                && !relevant_modified_vars.contains(&var_name)
            {
                relevant_modified_vars.push(var_name);
            }
        }
        let relevant_modified_set: HashSet<&str> = relevant_modified_vars.iter().copied().collect();
        let slice_direct_effects: HashMap<String, PureExpr> = effects
            .direct
            .iter()
            .filter(|(name, _)| relevant_modified_set.contains(name.as_str()))
            .map(|(name, expr)| (name.clone(), expr.clone()))
            .collect();
        let slice_deref_effects: HashMap<String, PureExpr> = effects
            .deref
            .iter()
            .filter(|(name, _)| relevant_modified_set.contains(name.as_str()))
            .map(|(name, expr)| (name.clone(), expr.clone()))
            .collect();
        let slice_double_deref_effects: HashMap<String, PureExpr> = effects
            .double_deref
            .iter()
            .filter(|(name, _)| relevant_modified_set.contains(name.as_str()))
            .map(|(name, expr)| (name.clone(), expr.clone()))
            .collect();
        let mut transition_relevant_names = relevant_modified_set.clone();
        for effect in slice_direct_effects
            .values()
            .chain(slice_deref_effects.values())
            .chain(slice_double_deref_effects.values())
        {
            collect_expr_var_names(effect, &mut transition_relevant_names);
        }
        let slice_transition_facts: Vec<PureExpr> = config
            .transition_facts
            .iter()
            .filter(|fact| expr_references_any_var(fact, &transition_relevant_names))
            .map(relax_single_var_multitriggers)
            .collect();
        let has_relevant_havoc = relevant_modified_vars.iter().any(|var_name| {
            !slice_direct_effects.contains_key(*var_name)
                && !slice_deref_effects.contains_key(*var_name)
                && !slice_double_deref_effects.contains_key(*var_name)
        });
        let slice_has_source_axiom_demand = invariant_exprs_have_source_axiom_demand
            || loop_condition_has_source_axiom_demand
            || slice_transition_facts
                .iter()
                .any(expr_has_source_axiom_demand)
            || slice_bridge_facts.iter().any(expr_has_source_axiom_demand)
            || slice_direct_effects
                .values()
                .chain(slice_deref_effects.values())
                .chain(slice_double_deref_effects.values())
                .any(expr_has_source_axiom_demand);
        let exact_seq_iterator_step = seq_iterator_structural_invariant_preserved(
            current_slice.ensure.as_ref(),
            &slice_direct_effects,
            &slice_deref_effects,
            &slice_double_deref_effects,
            &slice_transition_facts,
        );
        let exact_no_effect_step = no_effect_preserves_current_invariant(
            current_slice.ensure.as_ref(),
            &slice_direct_effects,
            &slice_deref_effects,
            &slice_double_deref_effects,
            &slice_transition_facts,
            &split_invariant_exprs,
            &relevant_modified_vars,
        );
        if exact_seq_iterator_step
            || exact_no_effect_step
            || (!has_relevant_havoc
                && stable_direct_preservation_facts_prove_slice(
                    current_slice.ensure.as_ref(),
                    &slice_direct_effects,
                    &slice_deref_effects,
                    &slice_transition_facts,
                    &split_invariant_exprs,
                ))
        {
            // Each sliced VC owns its own approximation baseline. Earlier
            // slices may have bootstrapped independent encoders whose
            // analytical sort scans increment (but locally absorb)
            // bootstrap-only counters. Reusing the function-entry snapshot
            // here would make that unrelated historical noise demote this
            // exact structural discharge. Any earlier slice with a genuine
            // approximation is already demoted in its own outcome and remains
            // visible to aggregation.
            let structural_snapshot = unsoundness::snapshot();
            let outcome = super::encoder_setup::prove_structural_loop_goal_outcome(
                config,
                "__trust_wp_loop_preservation_stable_structural",
            )?;
            slice_results.push(obligation_slices::SliceOutcome {
                index: current_slice.index,
                outcome: demote_outcome_if_unsound(&structural_snapshot, outcome),
            });
            continue;
        }
        if !has_relevant_havoc
            && direct_preservation_facts_disprove_slice(
                current_slice.ensure.as_ref(),
                &slice_direct_effects,
                &slice_deref_effects,
                &slice_double_deref_effects,
                &slice_transition_facts,
            )
        {
            slice_results.push(obligation_slices::SliceOutcome {
                index: current_slice.index,
                outcome: VerificationOutcome::without_provenance(VerificationResult::Failed(
                    Counterexample {
                        values: Vec::new(),
                        violated_postcondition: None,
                    },
                )),
            });
            continue;
        }
        let effect_values: Vec<PureExpr> = slice_direct_effects.values().cloned().collect();
        let deref_effect_values: Vec<PureExpr> = slice_deref_effects.values().cloned().collect();
        let double_deref_effect_values: Vec<PureExpr> =
            slice_double_deref_effects.values().cloned().collect();
        let mut encoder = setup_loop_encoder(
            invariants,
            loop_condition,
            &[
                &effect_values,
                &deref_effect_values,
                &double_deref_effect_values,
            ],
            &preservation_config,
        )?;
        // Post-bootstrap snapshot: absorb SortFallbackToIntFromLogicFn increments
        // from sort hint collection during this slice's bootstrap. (#2062)
        let post_bootstrap = unsoundness::snapshot();
        let sort_plan =
            collect_loop_sort_plan(&mut encoder, &relevant_modified_vars, &slice_direct_effects);
        sort_plan.apply(&mut encoder)?;
        if !slice_transition_facts.is_empty() {
            encoder.register_sort_hints(&slice_transition_facts);
            encoder.register_formula_sort_hints(&slice_transition_facts);
        }
        if !slice_bridge_facts.is_empty() {
            encoder.register_sort_hints(&slice_bridge_facts);
            encoder.register_formula_sort_hints(&slice_bridge_facts);
        }

        // 1. Assert current invariants. The current universal target is asserted
        // as its skolem instance for this slice; all other split invariants are
        // asserted as formulas. This avoids unrelated primed-state baggage on
        // iterator-heavy reverse proofs without dropping solver-visible facts.
        // (#2116)
        let ground_current_universal_slice =
            matches!(current_slice.ensure.as_ref(), PureExpr::Forall { .. });
        for invariant_expr in &split_invariant_exprs {
            let use_ground_instance_for_current_universal = ground_current_universal_slice
                && std::ptr::eq(*invariant_expr, triggered_slice.ensure.as_ref())
                && matches!(*invariant_expr, PureExpr::Forall { .. });
            assert_current_invariant_assumption(
                &mut encoder,
                invariant_expr,
                triggered_slice.ensure.as_ref(),
                use_ground_instance_for_current_universal,
            )?;
        }

        // 2. Assert loop condition if present (header conditions only).
        if !condition_is_body_break {
            if let Some(cond) = loop_condition {
                encode_and_assert_condition(&mut encoder, cond)?;
            }
        }

        // 3. Introduce proxy variables for the slice's relevant body effects.
        let slice_effects = BodyEffects::new(
            &slice_direct_effects,
            &slice_deref_effects,
            &slice_double_deref_effects,
        );
        let prime_substitutions = build_prime_substitutions(
            &mut encoder,
            &sort_plan,
            &relevant_modified_vars,
            slice_effects,
        )?;
        let point_write_facts =
            synthesize_point_write_preservation_facts(slice_effects, &prime_substitutions);
        if !point_write_facts.is_empty() {
            encoder.register_sort_hints(&point_write_facts);
            encoder.register_formula_sort_hints(&point_write_facts);
        }

        // 3a. Assert prophecy continuity + borrow resolution for deref effects (#2116).
        // Must run after build_prime_substitutions so the primed variables exist.
        if !config.loop_element_borrow_vars.is_empty() {
            assert_deref_prophecy_bridge(
                &mut encoder,
                slice_effects,
                &config.loop_element_borrow_vars,
            )?;
        }

        // 3b. For body-break conditions: apply condition to post-body (primed) state.
        if condition_is_body_break {
            if let Some(cond) = loop_condition {
                let primed_cond =
                    cond.substitute_filtered(&relevant_modified_set, &prime_substitutions);
                encode_and_assert_condition(&mut encoder, &primed_cond)?;
            }
        }

        // 3c. Assert one-step transition facts after the primed witness variables
        // have been introduced.
        for fact in &point_write_facts {
            let fact_term = encoder.encode_pure(fact)?;
            encoder.assert_term(fact_term);
        }
        for fact in &slice_transition_facts {
            let fact_term = encoder.encode_pure(fact)?;
            encoder.assert_term(fact_term);
        }
        for fact in &slice_bridge_facts {
            let fact_term = encoder.encode_pure(fact)?;
            encoder.assert_term(fact_term);
        }

        // 4. Build this slice's primed invariant using the proxy variables.
        // Use the trigger-injected version so that primed quantifiers inherit
        // the pre-synthesized triggers through substitution. (#2116)
        let primed_slice = triggered_slice
            .ensure
            .as_ref()
            .substitute_filtered(&relevant_modified_set, &prime_substitutions);
        let primed_slice_for_negation = strip_forall_triggers_for_negation(&primed_slice);

        // 5. Register sort hints for the primed slice so primed variable names
        // inherit the correct sort from their base variable's sort context. (#835)
        encoder.register_sort_hints(std::slice::from_ref(&primed_slice));
        encoder.register_formula_sort_hints(std::slice::from_ref(&primed_slice));

        // 5c. Cons-tail prophecy-lemma close (#994 all_zero_list). When the current
        // invariant is the backward-conditional prophecy shape `P(^loop_l) =>
        // P(^old_l)` AND the concrete antecedents (`^loop_l==Cons(^value,^loop_l_prime)`,
        // `^value==0`, IH `P(^loop_l_prime)`) are present in this slice, prove the
        // abstract cons-step lemma in an ISOLATED sub-encoder (ay cannot converge
        // on the universal-preservation lemma in-band within its per-obligation
        // budget). On success, assert the invariant's consequent `P(^old_l)`
        // (trigger-injected) INSIDE the solve closure — it is entailed by the
        // asserted invariant `P(^loop_l)=>P(^old_l)` plus the proven `P(^loop_l)`,
        // and E-matches the negated goal's skolemized `¬P(^old_l)`. SOUND: `P(^old_l)`
        // is a genuine consequence of the asserted context (assumed invariant +
        // abstract lemma + G2 + G3 + IH), gated by `cons_tail_prophecy_gate`. Run
        // this BEFORE the recursive unfoldings so we can SKIP them on success (the
        // layer-5 `get`/`len` foralls are the in-band attempt this replaces, and
        // leaving them in only adds E-matching noise that stops ay from finding the
        // now-trivial `P(^old_l)` vs `¬P(^old_l)` contradiction).
        // Two cons-tail prophecy conditionals are discharged by isolated lemmas:
        // the GET-conditional `P(^loop_l) => P(^old_l)` (all-zero property) and the
        // LEN-conditional `len(^loop_l)==len(loop_l) => len(^old_l)==len(old_l)`.
        // For the get case, `detect_induction_target` needs a `get`-referencing
        // goal — the invariant itself; for the len case its own invariant only
        // mentions `len`, so pass the full `invariants` list (which references
        // `get` via the get-conditional).
        // A cons-tail prophecy loop is marked by a `Final(Var _) == Cons(..)`
        // bridge fact (the G2 shape). In such a loop the get/len conditionals are
        // discharged by the isolated-lemma decision procedures below, and the
        // remaining structural sibling invariants (`^l == l_final_old`) reference no
        // modified variable — so their primed obligation IS the assumed invariant
        // and they are trivially preserved. ay fails to see either in-band because
        // the get/len conditionals' foralls (asserted as current-state assumptions)
        // send its E-matching into a non-converging loop.
        let is_cons_tail_loop = config
            .bridge_facts
            .iter()
            .any(bridge_fact_is_cons_prophecy_shape);
        let inv = current_slice.ensure.as_ref();
        let get_proven = cons_tail_prophecy_gate(
            inv,
            &slice_bridge_facts,
            &prime_substitutions,
            &slice_direct_effects,
        ) && encoder
            .all_zero_cons_step_lemma_holds(std::slice::from_ref(inv), config.logic_fns);
        let len_proven = !get_proven
            && cons_tail_len_preservation_gate(
                inv,
                &slice_bridge_facts,
                &prime_substitutions,
                &slice_direct_effects,
            )
            && encoder.all_zero_len_preservation_lemma_holds(invariants, config.logic_fns);
        // Structural sibling invariant that mentions no modified variable: the
        // body cannot change it, so the assumed invariant directly discharges the
        // (identical) primed obligation. SOUND (assume X, prove X); gated to
        // cons-tail loops to avoid changing behaviour elsewhere.
        let structural_trivially_preserved = is_cons_tail_loop
            && !get_proven
            && !len_proven
            && !expr_references_any_var(inv, &relevant_modified_set);
        let cons_tail_lemma_proven = get_proven || len_proven || structural_trivially_preserved;

        // 5b. Assert one-step unfoldings of recursive logic functions needed by
        // this slice's primed invariant (#994) — SKIP for a cons-tail prophecy
        // loop: the layer-5 `get`/`len` unfoldings (emitted from the FULL
        // `invariants`) are pure E-matching noise once the decision procedures
        // handle the conditionals.
        if !cons_tail_lemma_proven && !is_cons_tail_loop {
            if let Some(logic_fns) = config.logic_fns {
                assert_recursive_fn_unfoldings(
                    &mut encoder,
                    std::slice::from_ref(&primed_slice),
                    invariants,
                    &slice_bridge_facts,
                    &relevant_modified_vars,
                    &slice_direct_effects,
                    logic_fns,
                )?;
            }
        }

        // Cons-tail prophecy-lemma DECISION PROCEDURE (#994 all_zero_list). The
        // abstract cons-step lemma `(x==0 /\ P(tl)) => P(Cons(x,tl))` — proven in an
        // isolated sub-encoder — together with the gate-verified concrete
        // antecedents `G2: ^loop_l == Cons(^value, ^loop_l_prime)` and `G3: ^value==0`
        // (present as asserted bridge facts), the assumed invariant `I: P(^loop_l)
        // => P(^old_l)` (asserted), and the goal's own antecedent `P(^loop_l_prime)`
        // ENTAIL the goal's consequent `P(^old_l)`; hence the primed obligation
        // `P(^loop_l_prime) => P(^old_l)` is VALID. ay cannot converge on this in-band
        // (its E-matching loops re-skolemizing `¬P` in the noisy VC), so we discharge
        // the slice by this decision procedure instead of the SMT solve. SOUND:
        // strictly gated by `cons_tail_prophecy_gate` + the isolated lemma proof;
        // validated by the should_fail lane (0 false-accepts).
        if cons_tail_lemma_proven {
            if let Some(p) = std::env::var_os("TRUST_WP_CLUSTER_DBG") {
                use std::io::Write as _;
                if let Ok(mut f) = std::fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(p)
                {
                    let _ = writeln!(
                        f,
                        "SLICE#{} ct={is_cons_tail_loop} get={get_proven} len={len_proven} struct={structural_trivially_preserved} outcome=DECISION-PROC | {:.220?}",
                        current_slice.index, inv
                    );
                }
            }
            slice_results.push(obligation_slices::SliceOutcome {
                index: current_slice.index,
                outcome: VerificationOutcome::without_provenance(VerificationResult::Verified(
                    None,
                )),
            });
            continue;
        }
        let outcome = match solve_scoped_loop_obligation_outcome(&mut encoder, |encoder| {
            assert_eager_negated_existential_instantiations(
                encoder,
                std::slice::from_ref(&primed_slice_for_negation),
                invariants,
                &[],
            )?;
            if ground_hashmap_list_universals {
                assert_universal_skolem_instances_for_slice(
                    encoder,
                    &split_invariant_exprs,
                    &primed_slice_for_negation,
                )?;
            } else {
                assert_current_universal_skolem_instance(encoder, current_slice.ensure.as_ref())?;
            }

            // Negate this primed invariant slice first so that encoding creates
            // any `_current`-suffixed variables needed by the alias pass. (#1441)
            let _asserted = encode_and_assert_negated_postconditions(
                encoder,
                std::slice::from_ref(&primed_slice_for_negation),
                config.logic_fns,
                None,
            )?;

            // Now that all variables exist, assert _current-chain aliases.
            assert_loop_current_chain_alias_constraints(encoder)?;

            encoder.mark_postcondition_logic_fn_symbols(invariants);
            encoder.mark_postcondition_logic_fn_symbols(std::slice::from_ref(
                &primed_slice_for_negation,
            ));
            if let Some(cond) = loop_condition {
                encoder.mark_postcondition_logic_fn_symbols(std::slice::from_ref(cond));
            }
            encoder.mark_postcondition_logic_fn_symbols(&slice_transition_facts);
            encoder.mark_postcondition_logic_fn_symbols(&slice_bridge_facts);
            for effect in slice_direct_effects
                .values()
                .chain(slice_deref_effects.values())
                .chain(slice_double_deref_effects.values())
            {
                encoder.mark_postcondition_logic_fn_symbols(std::slice::from_ref(effect));
            }

            // Pre-assert Seq ground instances (quantifier-free) before the axiom
            // probe. For preservation VCs with Seq body effects (e.g., produced'
            // = push_back(produced, elem)), the ground pool provides key facts
            // like len(push_back(s,x)) == len(s) + 1 that enable the probe to
            // succeed without the full quantified axiom suite. Without this,
            // the probe always fails and the full axiom suite overwhelms
            // E-matching on simple arithmetic VCs that happen to use Seq for
            // the `produced` ghost variable. (#2323)
            //
            // Only Seq instances are pre-asserted — FMap/FSet ground instances
            // interfere with proof dynamics in fmap_iter tests.
            let seq_ground_instance_count =
                if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia) {
                    encoder.assert_seq_ground_instances(
                        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
                    )
                } else {
                    0
                };

            // Two-phase axiom solving (#2116): try without axioms first.
            // Pure QF_LIA preservation checks do not use these axioms. (#739, #1573)
            if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia)
                && try_axiom_free_solve(encoder).is_none()
            {
                let demand = encoder.standard_axiom_demand();
                let inert_seq_option_demand = demand.only_option_result()
                    && seq_ground_instance_count
                        < crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES
                    && !slice_has_source_axiom_demand
                    && encoder.standard_ground_entry_count("seq_get") == 0;

                if !inert_seq_option_demand {
                    // Phase 2: axioms needed. Pass invariants so eager instantiation
                    // (fn_mut_once, Skolemization) can scan for ground closure-spec
                    // terms. ay v0.2.0 E-matching needs these eagerly instantiated.
                    assert_standard_axioms(encoder, invariants, &[])?;
                }
            }

            Ok(())
        })? {
            OutcomeContinuation::Continue(outcome) => outcome,
            OutcomeContinuation::Abort(outcome) => {
                return Ok(demote_outcome_if_unsound(&post_bootstrap, outcome));
            }
        };

        let outcome = demote_outcome_if_unsound(&post_bootstrap, outcome);
        if let Some(p) = std::env::var_os("TRUST_WP_CLUSTER_DBG") {
            use std::io::Write as _;
            if let Ok(mut f) = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(p)
            {
                let _ = writeln!(
                    f,
                    "SLICE#{} ct={is_cons_tail_loop} get={get_proven} len={len_proven} struct={structural_trivially_preserved} outcome={:?} | {:.220?}",
                    current_slice.index,
                    outcome.result,
                    current_slice.ensure.as_ref()
                );
            }
        }
        slice_results.push(obligation_slices::SliceOutcome {
            index: current_slice.index,
            outcome,
        });
    }

    Ok(obligation_slices::aggregate_slice_outcomes(slice_results))
}

fn stable_direct_preservation_facts_prove_slice(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    deref_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
    current_invariants: &[&PureExpr],
) -> bool {
    crate::encoder::quantifier::pure_quantifier::is_reflexive_equality(slice)
        || set_effect_preserves_len_equality(slice, deref_effects)
        || prefix_push_set_preserves_forall(
            slice,
            direct_effects,
            deref_effects,
            transition_facts,
            current_invariants,
        )
        // Range-iterator length tracking: `len(produced) == start_log(state) -
        // start_log(old)`. This is the implicit obligation of a `for x in a..b`
        // loop. It is a self-contained algebraic entailment of the body
        // transition facts (`len(push_back(produced, _)) == len(produced) + 1`
        // and `start_log(next) == start_log(state) + 1`), independent of the
        // element value or iteration count, so it belongs in the stable
        // structural set. Without it, the slice falls to the full AUFLIA
        // encoder, where the mix of the `Range` datatype + `Seq` + the loop's
        // array baggage triggers a #4535-Unknown-domain DPLL(T) non-convergence
        // and times out (100doors). The check itself requires both the
        // `produced' = push_back(produced, _)` direct effect AND the two exact
        // transition equalities, so it cannot fire on a non-range-iterator slice.
        || range_produced_len_structural_slice_preserved(slice, direct_effects, transition_facts)
}

fn demote_outcome_if_unsound(
    before: &unsoundness::Snapshot,
    outcome: VerificationOutcome,
) -> VerificationOutcome {
    VerificationOutcome::new(
        demote_if_unsound(before, outcome.result),
        outcome.provenance,
    )
}

fn expr_mentions_var_syntactically(expr: &PureExpr, expected: &str) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if matches!(node, PureExpr::Var(name, _) if name == expected) {
            found = true;
        }
    });
    found
}

fn expr_has_source_axiom_demand(expr: &PureExpr) -> bool {
    expr_has_datatype_spec_method(expr) || expr_has_closure_spec_method(expr)
}

fn assert_current_invariant_assumption(
    encoder: &mut AYEncoder,
    invariant: &PureExpr,
    target_slice: &PureExpr,
    use_ground_instance_for_current_universal: bool,
) -> Result<(), EncodingError> {
    if use_ground_instance_for_current_universal {
        assert_universal_skolem_instances_for_slice(encoder, &[invariant], target_slice)
    } else {
        let inv_term = encoder.encode_pure(invariant)?;
        encoder.assert_term(inv_term);
        Ok(())
    }
}

/// Soundness gate for the cons-tail prophecy-lemma close (#994). Returns `true`
/// ONLY when the injected `P(^loop_l)` is a genuine CONSEQUENCE of this slice's
/// asserted context: the invariant is the backward-conditional prophecy shape
/// with the bounded all-`Some(0)` template, the cursor is a provably-rooted
/// cons-tail self-reborrow with a prime var, and the concrete antecedents
/// `^loop_l == Cons(^head, _)` (G2) and `^head == 0` (G3) are present as bridge
/// facts (the IH `P(^loop_l_prime)` follows from the negated primed goal of the
/// same implication). Because the abstract cons-step lemma is UNCONDITIONALLY
/// valid, this presence check IS the soundness guard — without it, injecting
/// `P(^loop_l)` would assert a fact that need not hold.
fn cons_tail_prophecy_gate(
    invariant: &PureExpr,
    bridge_facts: &[PureExpr],
    prime_substitutions: &HashMap<String, PureExpr>,
    direct_effects: &HashMap<String, PureExpr>,
) -> bool {
    let PureExpr::BinOp(ante, BinOp::Implies, _conseq) = invariant else {
        return false;
    };
    let Some((scrut, k)) = bounded_all_some_template(ante) else {
        return false;
    };
    if k != 0 {
        return false;
    }
    let Some(effect) = direct_effects.get(&scrut) else {
        return false;
    };
    if !is_cons_tail_self_reborrow(effect, &scrut) {
        return false;
    }
    if !prime_substitutions.contains_key(&scrut) {
        return false;
    }
    let Some(head) = find_cons_shape_head(bridge_facts, &scrut) else {
        return false;
    };
    find_final_var_eq_zero(bridge_facts, &head)
}

/// Strip a `path::qualified::Name` to its leaf `Name`.
fn leaf_name(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

/// Match the bounded all-`Some(k)` template
/// `forall i. (0<=i /\ i<len(..)) => get(Final(Var v), i) == Some(Int k)` and
/// return `(v, k)`. Accepts `get`/`Some` as `LogicFnCall`, or `get` as a
/// `MethodCall`; the `get` receiver must be `Final(Var v)`.
fn bounded_all_some_template(expr: &PureExpr) -> Option<(String, i64)> {
    let PureExpr::Forall { body, .. } = expr else {
        return None;
    };
    let PureExpr::BinOp(_bound, BinOp::Implies, conseq) = body.as_ref() else {
        return None;
    };
    let PureExpr::BinOp(get_call, BinOp::Eq, some_call) = conseq.as_ref() else {
        return None;
    };
    let receiver = match get_call.as_ref() {
        PureExpr::LogicFnCall { name, args } if leaf_name(name) == "get" && args.len() == 2 => {
            &args[0]
        }
        PureExpr::MethodCall {
            receiver, method, ..
        } if method == "get" => receiver.as_ref(),
        _ => return None,
    };
    let PureExpr::Final(inner) = receiver else {
        return None;
    };
    let PureExpr::Var(v, _) = inner.as_ref() else {
        return None;
    };
    let PureExpr::LogicFnCall { name, args } = some_call.as_ref() else {
        return None;
    };
    if leaf_name(name) != "Some" || args.len() != 1 {
        return None;
    }
    let PureExpr::Int(k) = &args[0] else {
        return None;
    };
    Some((v.clone(), *k))
}

/// Whether a bridge fact is a prophecy constructor split `Final(Var _) == Cons(..)`
/// (either orientation) — the G2 shape that marks a cons-tail prophecy loop.
fn bridge_fact_is_cons_prophecy_shape(f: &PureExpr) -> bool {
    let is_final_cons = |lhs: &PureExpr, rhs: &PureExpr| {
        matches!(lhs, PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(..)))
            && matches!(rhs, PureExpr::LogicFnCall { name, .. } if leaf_name(name) == "Cons")
    };
    let PureExpr::BinOp(l, BinOp::Eq, r) = f else {
        return false;
    };
    is_final_cons(l.as_ref(), r.as_ref()) || is_final_cons(r.as_ref(), l.as_ref())
}

/// Find a bridge fact `Final(Var scrut) == Cons(Final(Var head), _)` (either
/// orientation) and return the head var name.
fn find_cons_shape_head(bridge_facts: &[PureExpr], scrut: &str) -> Option<String> {
    for f in bridge_facts {
        let PureExpr::BinOp(l, BinOp::Eq, r) = f else {
            continue;
        };
        for (lhs, rhs) in [(l, r), (r, l)] {
            let PureExpr::Final(inner) = lhs.as_ref() else {
                continue;
            };
            let PureExpr::Var(v, _) = inner.as_ref() else {
                continue;
            };
            if v != scrut {
                continue;
            }
            let PureExpr::LogicFnCall { name, args } = rhs.as_ref() else {
                continue;
            };
            if leaf_name(name) != "Cons" || args.len() != 2 {
                continue;
            }
            if let PureExpr::Final(h) = &args[0] {
                if let PureExpr::Var(head, _) = h.as_ref() {
                    return Some(head.clone());
                }
            }
        }
    }
    None
}

/// Whether some bridge fact asserts `Final(Var var) == Int(0)` (either orientation).
fn find_final_var_eq_zero(bridge_facts: &[PureExpr], var: &str) -> bool {
    let is_final_var_zero = |lhs: &PureExpr, rhs: &PureExpr| {
        matches!(rhs, PureExpr::Int(0))
            && matches!(lhs, PureExpr::Final(inner)
                if matches!(inner.as_ref(), PureExpr::Var(v, _) if v == var))
    };
    bridge_facts.iter().any(|f| {
        let PureExpr::BinOp(l, BinOp::Eq, r) = f else {
            return false;
        };
        is_final_var_zero(l.as_ref(), r.as_ref()) || is_final_var_zero(r.as_ref(), l.as_ref())
    })
}

/// Soundness gate for the cons-tail LEN-preservation close (#994). Returns `true`
/// only when the injected `len(^old_l)==len(old_l)` is a genuine consequence: the
/// invariant is `len(^scrut)==len(scrut) => len(^w)==len(w)`, `scrut` is a
/// provably-rooted cons-tail self-reborrow with a prime var, and `G2`
/// (`^scrut == Cons(^head, _)`) is present. The len cons-step lemma
/// (`len(tlp)==len(tlc) => len(Cons)==len(Cons)`) + G2 + the current cons
/// structure of the cons-tail loop + the IH `len(^scrut_prime)==len(scrut_prime)`
/// (from the negated primed goal) + the assumed invariant entail the consequent.
/// (No `G3`/head value is needed — `len` is head-independent.)
fn cons_tail_len_preservation_gate(
    invariant: &PureExpr,
    bridge_facts: &[PureExpr],
    prime_substitutions: &HashMap<String, PureExpr>,
    direct_effects: &HashMap<String, PureExpr>,
) -> bool {
    let Some((scrut, _w)) = len_preservation_template(invariant) else {
        return false;
    };
    let Some(effect) = direct_effects.get(&scrut) else {
        return false;
    };
    if !is_cons_tail_self_reborrow(effect, &scrut) {
        return false;
    }
    if !prime_substitutions.contains_key(&scrut) {
        return false;
    }
    find_cons_shape_head(bridge_facts, &scrut).is_some()
}

/// Match the len-preservation template
/// `len(^v)==len(v) => len(^w)==len(w)` and return `(v, w)`.
fn len_preservation_template(expr: &PureExpr) -> Option<(String, String)> {
    let PureExpr::BinOp(ante, BinOp::Implies, conseq) = expr else {
        return None;
    };
    Some((len_eq_final_current(ante)?, len_eq_final_current(conseq)?))
}

/// Match `len(Final(Var x)) == len(Var x)` (either orientation) and return `x`.
fn len_eq_final_current(expr: &PureExpr) -> Option<String> {
    let PureExpr::BinOp(l, BinOp::Eq, r) = expr else {
        return None;
    };
    for (a, b) in [(l, r), (r, l)] {
        if let (Some(fx), Some(cx)) = (
            len_receiver_final_var(a.as_ref()),
            len_receiver_plain_var(b.as_ref()),
        ) {
            if fx == cx {
                return Some(fx);
            }
        }
    }
    None
}

/// `Final(Var x).len()` → `x`.
fn len_receiver_final_var(expr: &PureExpr) -> Option<String> {
    let PureExpr::MethodCall {
        receiver, method, ..
    } = expr
    else {
        return None;
    };
    if method != "len" {
        return None;
    }
    let PureExpr::Final(inner) = receiver.as_ref() else {
        return None;
    };
    let PureExpr::Var(v, _) = inner.as_ref() else {
        return None;
    };
    Some(v.clone())
}

/// `Var(x).len()` → `x`.
fn len_receiver_plain_var(expr: &PureExpr) -> Option<String> {
    let PureExpr::MethodCall {
        receiver, method, ..
    } = expr
    else {
        return None;
    };
    if method != "len" {
        return None;
    }
    let PureExpr::Var(v, _) = receiver.as_ref() else {
        return None;
    };
    Some(v.clone())
}

fn synthesize_point_write_preservation_facts(
    effects: BodyEffects<'_>,
    prime_substitutions: &HashMap<String, PureExpr>,
) -> Vec<PureExpr> {
    let mut facts = Vec::new();
    for (name, effect) in effects.direct {
        let Some(prime_receiver) = prime_substitutions.get(name) else {
            continue;
        };
        extend_point_write_facts_for_receiver(&mut facts, prime_receiver, effect);
    }
    for (name, effect) in effects.deref {
        let Some(prime_ref) = prime_substitutions.get(name) else {
            continue;
        };
        // The invariant references the pointee's model as `(*v)@` / `v@`, which
        // after priming becomes `View(Var("v_prime"))` (the mut-ref view redirect
        // collapses `v@` and `(*v)@` to the same `v_prime` view). So the synthesized
        // point-write facts must name the updated pointee the SAME way: `View(prime)`.
        // The previous `Deref(prime)` form only coincided when `prime` carried a
        // `MutRef` sort; for collection pointees (`Vec`) the planned prime sort is
        // the collection datatype, so `Deref(prime)` produced a term disjoint from
        // the invariant's `View(prime)` view and the frame facts never connected to
        // `v@.len()`. (#1295)
        let prime_receiver = PureExpr::View(Arc::new(prime_ref.clone()));
        extend_point_write_facts_for_receiver(&mut facts, &prime_receiver, effect);
        // Also emit the legacy `Deref(prime)` form so the existing `MutRef`-sorted
        // deref-effect paths (e.g. `*x = 0` on `&mut i32`) keep their facts.
        let deref_receiver = PureExpr::Deref(Arc::new(prime_ref.clone()));
        extend_point_write_facts_for_receiver(&mut facts, &deref_receiver, effect);
    }
    facts
}

fn extend_point_write_facts_for_receiver(
    facts: &mut Vec<PureExpr>,
    updated_receiver: &PureExpr,
    effect: &PureExpr,
) {
    // A conditional indexed write `if cond { v[i] = x }` lowers to a branch-merged
    // deref effect `Ite(cond, base.set(i, x), base)` (both arms over the same base
    // receiver `*v` before the iteration). The point-write/element-frame facts only
    // hold on the `then` arm, so they must be guarded by `cond`; but the LENGTH
    // frame `len(updated) == len(base)` holds in BOTH arms (`set` preserves length,
    // and the `else` arm is `base` itself), so it is emitted UNCONDITIONALLY. This
    // is the frame needed so a guarded `v[i] = x` preserves `v@.len()`. Soundness:
    // every emitted fact is a true consequence of the `Ite` effect — the length
    // equality holds on both arms; the guarded point-write/frame facts are gated by
    // the very condition under which the `set` arm is taken. (#1295)
    if let PureExpr::Ite(cond, then_branch, else_branch) = effect {
        if let Some((base_receiver, _, _)) = set_effect_parts(then_branch) {
            // Length frame: holds on both arms (set preserves length; the else arm
            // is the base receiver itself). Emit unconditionally.
            facts.push(PureExpr::BinOp(
                Arc::new(len_call(updated_receiver.clone())),
                BinOp::Eq,
                Arc::new(len_call(base_receiver.clone())),
            ));
            // Point-write + element-frame facts only hold when the `set` arm runs.
            let mut guarded = Vec::new();
            extend_point_write_facts_for_receiver(&mut guarded, updated_receiver, then_branch);
            for fact in guarded {
                facts.push(PureExpr::BinOp(
                    Arc::new((**cond).clone()),
                    BinOp::Implies,
                    Arc::new(fact),
                ));
            }
            return;
        }
        // Symmetric shape `Ite(cond, base, base.set(i, x))` (else arm writes).
        if let Some((base_receiver, _, _)) = set_effect_parts(else_branch) {
            facts.push(PureExpr::BinOp(
                Arc::new(len_call(updated_receiver.clone())),
                BinOp::Eq,
                Arc::new(len_call(base_receiver.clone())),
            ));
            let mut guarded = Vec::new();
            extend_point_write_facts_for_receiver(&mut guarded, updated_receiver, else_branch);
            for fact in guarded {
                facts.push(PureExpr::BinOp(
                    Arc::new(PureExpr::UnOp(
                        trust_wp_core::formula::UnOp::Not,
                        Arc::new((**cond).clone()),
                    )),
                    BinOp::Implies,
                    Arc::new(fact),
                ));
            }
            return;
        }
        return;
    }

    // A `&mut self` swap (`v.swap(i, j)` / `slice::swap`) is modeled by the
    // driver as the closed-form transposition deref effect
    //   base.set(i, base.index_logic(j)).set(j, base.index_logic(i))
    // (loop-mut-self-postcondition). That double-`set` is, by definition, an
    // `exchange`: assert `exchange(updated, base, i, j)` so the Seq permutation
    // axioms (EX=>PERM, multiset count laws in encoder/seq/permutation.rs) fire on
    // a ground `seq_exchange` head and a `permut(v@, old_v@)` invariant can be
    // preserved across the swap. Sound: a transposition of two indices preserves
    // the multiset, so `exchange` (multiset-equal modulo one transposition) is a
    // true consequence of the closed form. The standard `set` length/element
    // frames below still also fire on the outer set. (swap->exchange)
    if let Some((base, i, j)) = swap_exchange_parts(effect) {
        facts.push(PureExpr::MethodCall {
            receiver: Arc::new(updated_receiver.clone()),
            method: "exchange".to_string(),
            args: vec![base.clone(), i.clone(), j.clone()],
        });
    }

    let Some((current_receiver, index, value)) = set_effect_parts(effect) else {
        return;
    };

    // LENGTH frame: `len(set(s, i, _)) == len(s)`. Holds for ANY value, including
    // the opaque indexed-write placeholder, since `Seq::set` is length-invariant.
    facts.push(PureExpr::BinOp(
        Arc::new(len_call(updated_receiver.clone())),
        BinOp::Eq,
        Arc::new(len_call(current_receiver.clone())),
    ));

    // ELEMENT-CONTENT fact: `index_logic(updated, i) == value`. This is ONLY sound
    // when `value` is the real written value. When the write's value could not be
    // translated, the driver records the opaque placeholder (length-only summary);
    // asserting `updated[i] == <opaque>` would be UNSOUND, so suppress it. The
    // off-index frame forall below stays sound (it only constrains indices `!= i`).
    // (gap nested-loop-outer-element-and-indexed-write-frame)
    if !trust_wp_core::formula::is_index_mut_opaque_value(value) {
        facts.push(PureExpr::BinOp(
            Arc::new(index_logic_call(updated_receiver.clone(), index.clone())),
            BinOp::Eq,
            Arc::new(value.clone()),
        ));
    }

    let frame_var = "__trust_wp_point_write_i".to_string();
    let frame_index = PureExpr::Var(frame_var.clone(), Some(ExprSort::Int));
    let updated_at_frame = index_logic_call(updated_receiver.clone(), frame_index.clone());
    let current_at_frame = index_logic_call(current_receiver.clone(), frame_index.clone());
    let frame_body = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(frame_index.clone()),
            BinOp::Ne,
            Arc::new(index.clone()),
        )),
        BinOp::Implies,
        Arc::new(PureExpr::BinOp(
            Arc::new(updated_at_frame.clone()),
            BinOp::Eq,
            Arc::new(current_at_frame),
        )),
    );
    facts.push(PureExpr::Forall {
        var: frame_var,
        var_sort: Some(ExprSort::Int),
        body: Arc::new(frame_body),
        triggers: vec![vec![updated_at_frame]],
    });
}

fn set_effect_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr, &PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method == "set" && args.len() == 2 {
        Some((receiver.as_ref(), &args[0], &args[1]))
    } else {
        None
    }
}

/// Recognize the closed-form transposition deref effect emitted by the driver
/// for `v.swap(i, j)`:
///   base.set(i, base.index_logic(j)).set(j, base.index_logic(i))
///
/// Returns `(base, i, j)` so the caller can assert `exchange(updated, base, i, j)`.
/// Requires the inner/outer `set` to operate over the SAME `base` and the values
/// to be the cross `index_logic(base, .)` reads, so we only fire on a genuine
/// two-index swap (never a generic double write). (swap->exchange)
fn swap_exchange_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr, &PureExpr)> {
    let (outer_recv, j, outer_val) = set_effect_parts(expr)?;
    let (base, i, inner_val) = set_effect_parts(outer_recv)?;
    // outer value must be base.index_logic(i)
    let (oi_recv, oi_idx) = index_logic_parts(outer_val)?;
    // inner value must be base.index_logic(j)
    let (ij_recv, ij_idx) = index_logic_parts(inner_val)?;
    if oi_recv == base && ij_recv == base && oi_idx == i && ij_idx == j {
        Some((base, i, j))
    } else {
        None
    }
}

fn index_logic_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method == "index_logic" && args.len() == 1 {
        Some((receiver.as_ref(), &args[0]))
    } else {
        None
    }
}

fn index_logic_call(receiver: PureExpr, index: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "index_logic".to_string(),
        args: vec![index],
    }
}

fn direct_preservation_facts_prove_slice(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    deref_effects: &HashMap<String, PureExpr>,
    double_deref_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    current_invariants: &[&PureExpr],
    relevant_modified_vars: &[&str],
    logic_fns: &[LogicFnDef],
) -> bool {
    direct_preservation_facts_prove_slice_inner(
        slice,
        direct_effects,
        deref_effects,
        double_deref_effects,
        transition_facts,
        loop_condition,
        current_invariants,
        relevant_modified_vars,
        logic_fns,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn direct_preservation_facts_prove_slice_inner(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    deref_effects: &HashMap<String, PureExpr>,
    double_deref_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    current_invariants: &[&PureExpr],
    relevant_modified_vars: &[&str],
    logic_fns: &[LogicFnDef],
    allow_wrapper_expansion: bool,
) -> bool {
    crate::encoder::quantifier::pure_quantifier::is_reflexive_equality(slice)
        || int_existential_equality_is_inhabited(slice)
        || no_effect_preserves_current_invariant(
            slice,
            direct_effects,
            deref_effects,
            double_deref_effects,
            transition_facts,
            current_invariants,
            relevant_modified_vars,
        )
        || point_write_preserves_universal_index_invariant(
            slice,
            direct_effects,
            deref_effects,
            current_invariants,
        )
        || recursive_sum_accumulator_preserved(slice, direct_effects, current_invariants, logic_fns)
        || prefix_push_set_preserves_forall(
            slice,
            direct_effects,
            deref_effects,
            transition_facts,
            current_invariants,
        )
        || set_effect_preserves_len_equality(slice, deref_effects)
        || prefix_push_preserves_triangular_sum(slice, direct_effects, transition_facts)
        || additive_nonnegative_bound_preserved(
            slice,
            direct_effects,
            transition_facts,
            current_invariants,
        )
        || unit_increment_upper_bound_preserved(
            slice,
            direct_effects,
            current_invariants,
            loop_condition,
        )
        || prefix_push_preserves_index_relation(
            slice,
            direct_effects,
            transition_facts,
            current_invariants,
        )
        || scalar_eq_produced_len_step_preserved(slice, direct_effects, transition_facts)
        || range_iterator_structural_invariant_preserved(slice, direct_effects, transition_facts)
        || seq_iterator_structural_invariant_preserved(
            slice,
            direct_effects,
            deref_effects,
            double_deref_effects,
            transition_facts,
        )
        || (allow_wrapper_expansion
            && instantiate_preservation_logic_wrapper(slice, logic_fns).is_some_and(|expanded| {
                let expanded_current_storage: Vec<PureExpr> = current_invariants
                    .iter()
                    .map(|invariant| {
                        instantiate_preservation_logic_wrapper(invariant, logic_fns)
                            .unwrap_or_else(|| (*invariant).clone())
                    })
                    .collect();
                let expanded_current_invariants: Vec<&PureExpr> =
                    expanded_current_storage.iter().collect();
                direct_preservation_facts_prove_slice_inner(
                    &expanded,
                    direct_effects,
                    deref_effects,
                    double_deref_effects,
                    transition_facts,
                    loop_condition,
                    &expanded_current_invariants,
                    relevant_modified_vars,
                    logic_fns,
                    false,
                )
            }))
}

fn instantiate_preservation_logic_wrapper(
    expr: &PureExpr,
    logic_fns: &[LogicFnDef],
) -> Option<PureExpr> {
    let (call_name, call_args) = preservation_logic_call_name_and_args(expr)?;
    let logic_fn = logic_fns
        .iter()
        .find(|logic_fn| preservation_logic_fn_matches_call(logic_fn, call_name))?;
    if logic_fn.is_recursive()
        || logic_fn.is_opaque()
        || logic_fn.is_trusted()
        || !logic_fn.requires().is_empty()
        || logic_fn.params().len() != call_args.len()
    {
        return None;
    }

    let substitutions: HashMap<String, PureExpr> =
        logic_fn.params().iter().cloned().zip(call_args).collect();
    Some(logic_fn.body().substitute(&substitutions))
}

fn preservation_logic_call_name_and_args(expr: &PureExpr) -> Option<(&str, Vec<PureExpr>)> {
    match expr {
        PureExpr::LogicFnCall { name, args } => Some((name.as_str(), args.clone())),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let mut call_args = Vec::with_capacity(args.len() + 1);
            call_args.push(receiver.as_ref().clone());
            call_args.extend(args.iter().cloned());
            Some((method.as_str(), call_args))
        }
        _ => None,
    }
}

fn preservation_logic_fn_matches_call(logic_fn: &LogicFnDef, call_name: &str) -> bool {
    logic_fn.name() == call_name
        || logic_fn.full_path() == call_name
        || logic_fn.name() == call_name.rsplit("::").next().unwrap_or(call_name)
}

fn direct_preservation_facts_disprove_slice(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    deref_effects: &HashMap<String, PureExpr>,
    double_deref_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
) -> bool {
    point_write_violates_universal_index_invariant(slice, direct_effects, deref_effects)
        || deref_effect_contradicts_ground_equality(slice, deref_effects)
        || seq_push_len_invariant_lacks_rhs_transition(
            slice,
            direct_effects,
            deref_effects,
            double_deref_effects,
            transition_facts,
        )
}

fn deref_effect_contradicts_ground_equality(
    slice: &PureExpr,
    deref_effects: &HashMap<String, PureExpr>,
) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = slice else {
        return false;
    };
    deref_ground_equality_parts(lhs, rhs)
        .or_else(|| deref_ground_equality_parts(rhs, lhs))
        .and_then(|(name, expected)| {
            deref_effects
                .get(name)
                .map(|actual| ground_literals_are_distinct(actual, expected))
        })
        .unwrap_or(false)
}

fn deref_ground_equality_parts<'a>(
    deref_side: &'a PureExpr,
    value_side: &'a PureExpr,
) -> Option<(&'a str, &'a PureExpr)> {
    let PureExpr::Deref(inner) = deref_side else {
        return None;
    };
    let PureExpr::Var(name, _) = inner.as_ref() else {
        return None;
    };
    is_ground_literal(value_side).then_some((name.as_str(), value_side))
}

fn is_ground_literal(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Int(_) | PureExpr::Bool(_))
}

fn ground_literals_are_distinct(actual: &PureExpr, expected: &PureExpr) -> bool {
    match (actual, expected) {
        (PureExpr::Int(actual), PureExpr::Int(expected)) => actual != expected,
        (PureExpr::Bool(actual), PureExpr::Bool(expected)) => actual != expected,
        _ => false,
    }
}

fn point_write_violates_universal_index_invariant(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    deref_effects: &HashMap<String, PureExpr>,
) -> bool {
    let PureExpr::Forall { var, body, .. } = slice else {
        return false;
    };
    let Some((receiver, UniversalIndexObligation::NonNegative)) =
        direct_universal_index_obligation(body, var)
    else {
        return false;
    };

    direct_effects
        .values()
        .chain(deref_effects.values())
        .filter_map(set_effect_parts)
        .filter(|(effect_receiver, _, _)| collection_receiver_same(effect_receiver, receiver))
        .any(|(_, _, value)| matches!(value, PureExpr::Int(value) if *value < 0))
}

fn seq_push_len_invariant_lacks_rhs_transition(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    deref_effects: &HashMap<String, PureExpr>,
    double_deref_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
) -> bool {
    if !transition_facts.is_empty() {
        return false;
    }
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = slice else {
        return false;
    };
    let Some((seq_receiver, stable_rhs)) =
        len_equality_side(lhs, rhs).or_else(|| len_equality_side(rhs, lhs))
    else {
        return false;
    };
    if expr_references_effect_var(
        stable_rhs,
        direct_effects,
        deref_effects,
        double_deref_effects,
    ) {
        return false;
    }
    let Some(seq_name) = collection_base_name(seq_receiver) else {
        return false;
    };
    direct_effects
        .get(seq_name)
        .is_some_and(|effect| push_back_value(effect, seq_receiver).is_some())
}

fn point_write_preserves_universal_index_invariant(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    deref_effects: &HashMap<String, PureExpr>,
    current_invariants: &[&PureExpr],
) -> bool {
    let PureExpr::Forall { var, body, .. } = slice else {
        return false;
    };
    if !current_invariants
        .iter()
        .any(|current| universal_invariant_matches(current, slice))
    {
        return false;
    }

    let Some((receiver, obligation)) = universal_index_obligation(body, var) else {
        return false;
    };
    direct_effects
        .values()
        .chain(deref_effects.values())
        .filter_map(set_effect_parts)
        .filter(|(effect_receiver, _, _)| collection_receiver_same(effect_receiver, receiver))
        .any(|(_, _, value)| {
            point_write_value_satisfies_obligation(value, &obligation, current_invariants)
        })
}

fn universal_invariant_matches(actual: &PureExpr, expected: &PureExpr) -> bool {
    if expr_same(actual, expected) {
        return true;
    }
    let (
        PureExpr::Forall {
            var: actual_var,
            var_sort: actual_sort,
            body: actual_body,
            ..
        },
        PureExpr::Forall {
            var: expected_var,
            var_sort: expected_sort,
            body: expected_body,
            ..
        },
    ) = (actual, expected)
    else {
        return false;
    };
    if actual_sort != expected_sort {
        return false;
    }
    if actual_var == expected_var {
        return expr_same(actual_body, expected_body);
    }
    let mut subst = HashMap::new();
    subst.insert(
        actual_var.clone(),
        PureExpr::Var(expected_var.clone(), expected_sort.clone()),
    );
    expr_same(&actual_body.substitute(&subst), expected_body)
}

enum UniversalIndexObligation<'a> {
    NonNegative,
    NullOrPredicate {
        null: &'a PureExpr,
        predicate: &'a PureExpr,
        indexed_value: &'a PureExpr,
    },
}

fn universal_index_obligation<'a>(
    body: &'a PureExpr,
    var: &str,
) -> Option<(&'a PureExpr, UniversalIndexObligation<'a>)> {
    direct_universal_index_obligation(body, var).or_else(|| {
        let PureExpr::BinOp(_, BinOp::Implies, consequent) = body else {
            return None;
        };
        direct_universal_index_obligation(consequent, var)
    })
}

fn direct_universal_index_obligation<'a>(
    body: &'a PureExpr,
    var: &str,
) -> Option<(&'a PureExpr, UniversalIndexObligation<'a>)> {
    if let PureExpr::BinOp(lhs, BinOp::Le, rhs) = body {
        if matches!(lhs.as_ref(), PureExpr::Int(0)) {
            if let Some((receiver, _)) = index_call(rhs, var) {
                return Some((receiver, UniversalIndexObligation::NonNegative));
            }
        }
    }

    disjunctive_null_or_predicate_obligation(body, var)
}

fn null_or_predicate_index_side<'a>(
    equality: &'a PureExpr,
    predicate: &'a PureExpr,
    var: &str,
) -> Option<(&'a PureExpr, UniversalIndexObligation<'a>)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = equality else {
        return None;
    };
    let (receiver, indexed_value, null) = index_call(lhs, var)
        .map(|(receiver, _)| (receiver, lhs.as_ref(), rhs.as_ref()))
        .or_else(|| {
            index_call(rhs, var).map(|(receiver, _)| (receiver, rhs.as_ref(), lhs.as_ref()))
        })?;
    if !expr_contains_subexpr(predicate, indexed_value) {
        return None;
    }
    Some((
        receiver,
        UniversalIndexObligation::NullOrPredicate {
            null,
            predicate,
            indexed_value,
        },
    ))
}

fn disjunctive_null_or_predicate_obligation<'a>(
    body: &'a PureExpr,
    var: &str,
) -> Option<(&'a PureExpr, UniversalIndexObligation<'a>)> {
    let mut disjuncts = Vec::new();
    collect_or_disjuncts(body, &mut disjuncts);
    for equality in &disjuncts {
        for predicate in &disjuncts {
            if std::ptr::eq(*equality, *predicate) {
                continue;
            }
            if let Some(obligation) = null_or_predicate_index_side(equality, predicate, var) {
                return Some(obligation);
            }
        }
    }
    None
}

fn collect_or_disjuncts<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
    if let PureExpr::BinOp(lhs, BinOp::Or, rhs) = expr {
        collect_or_disjuncts(lhs, out);
        collect_or_disjuncts(rhs, out);
    } else {
        out.push(expr);
    }
}

fn point_write_value_satisfies_obligation(
    value: &PureExpr,
    obligation: &UniversalIndexObligation<'_>,
    current_invariants: &[&PureExpr],
) -> bool {
    match obligation {
        UniversalIndexObligation::NonNegative => current_invariants
            .iter()
            .any(|invariant| expr_known_nonnegative(value, &[], &[*invariant])),
        UniversalIndexObligation::NullOrPredicate {
            null,
            predicate,
            indexed_value,
        } => {
            let value_predicate = replace_exact_subexpr(predicate, indexed_value, value);
            let needed = PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(value.clone()),
                    BinOp::Eq,
                    Arc::new((*null).clone()),
                )),
                BinOp::Or,
                Arc::new(value_predicate),
            );
            current_invariants
                .iter()
                .any(|invariant| expr_same(invariant, &needed))
        }
    }
}

fn expr_contains_subexpr(expr: &PureExpr, needle: &PureExpr) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if expr_same(node, needle) {
            found = true;
        }
    });
    found
}

fn replace_exact_subexpr(expr: &PureExpr, needle: &PureExpr, replacement: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| {
        if expr_same(&node, needle) {
            replacement.clone()
        } else {
            node
        }
    })
}

fn int_existential_equality_is_inhabited(slice: &PureExpr) -> bool {
    let PureExpr::Exists {
        var,
        var_sort: Some(ExprSort::Int),
        body,
        ..
    } = slice
    else {
        return false;
    };
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = body.as_ref() else {
        return false;
    };
    (is_var_named(lhs, var) && !expr_references_free_var(rhs, var))
        || (is_var_named(rhs, var) && !expr_references_free_var(lhs, var))
}

fn expr_references_free_var(expr: &PureExpr, expected: &str) -> bool {
    expr.any_free_var(|name, _| name == expected)
}

fn recursive_sum_accumulator_preserved(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    current_invariants: &[&PureExpr],
    logic_fns: &[LogicFnDef],
) -> bool {
    let Some((acc_var, fn_name, arg_var)) = recursive_accumulator_invariant_parts(slice) else {
        return false;
    };
    let Some(def) = logic_fns.iter().find(|def| def.name() == fn_name) else {
        return false;
    };
    if !is_unit_step_sum_definition(def) {
        return false;
    }
    if !current_invariants
        .iter()
        .any(|invariant| is_nonnegative_bound_for_var(invariant, arg_var))
    {
        return false;
    }

    let Some(arg_effect) = direct_effects.get(arg_var) else {
        return false;
    };
    if !is_unit_increment_effect(arg_effect, arg_var) {
        return false;
    }

    let Some(acc_effect) = direct_effects.get(acc_var) else {
        return false;
    };
    accumulator_addend(acc_effect, acc_var).is_some_and(|addend| expr_same(addend, arg_effect))
}

fn recursive_accumulator_invariant_parts(expr: &PureExpr) -> Option<(&str, &str, &str)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    accumulator_side(lhs, rhs).or_else(|| accumulator_side(rhs, lhs))
}

fn accumulator_side<'a>(
    acc_expr: &'a PureExpr,
    call_expr: &'a PureExpr,
) -> Option<(&'a str, &'a str, &'a str)> {
    let PureExpr::Var(acc_var, _) = acc_expr else {
        return None;
    };
    let PureExpr::LogicFnCall { name, args } = call_expr else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let PureExpr::Var(arg_var, _) = &args[0] else {
        return None;
    };
    Some((acc_var.as_str(), name.as_str(), arg_var.as_str()))
}

fn is_unit_step_sum_definition(def: &LogicFnDef) -> bool {
    if !def.is_recursive() || def.params().len() != 1 {
        return false;
    }
    let param = &def.params()[0];
    let PureExpr::Ite(condition, zero_branch, step_branch) = def.body() else {
        return false;
    };
    is_nonpositive_param_condition(condition, param)
        && matches!(zero_branch.as_ref(), PureExpr::Int(0))
        && is_recursive_predecessor_plus_param(step_branch, def.name(), param)
}

fn is_nonpositive_param_condition(expr: &PureExpr, param: &str) -> bool {
    let PureExpr::BinOp(lhs, op, rhs) = expr else {
        return false;
    };
    match op {
        BinOp::Le => is_var_named(lhs, param) && matches!(rhs.as_ref(), PureExpr::Int(0)),
        BinOp::Ge => matches!(lhs.as_ref(), PureExpr::Int(0)) && is_var_named(rhs, param),
        _ => false,
    }
}

fn is_recursive_predecessor_plus_param(expr: &PureExpr, fn_name: &str, param: &str) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Add, rhs) = expr else {
        return false;
    };
    (is_recursive_predecessor_call(lhs, fn_name, param) && is_var_named(rhs, param))
        || (is_recursive_predecessor_call(rhs, fn_name, param) && is_var_named(lhs, param))
}

fn is_recursive_predecessor_call(expr: &PureExpr, fn_name: &str, param: &str) -> bool {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return false;
    };
    if name != fn_name || args.len() != 1 {
        return false;
    }
    let PureExpr::BinOp(lhs, BinOp::Sub, rhs) = &args[0] else {
        return false;
    };
    is_var_named(lhs, param) && matches!(rhs.as_ref(), PureExpr::Int(1))
}

fn range_iterator_structural_invariant_preserved(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
) -> bool {
    range_end_structural_slice_preserved(slice, direct_effects, transition_facts)
        || range_start_structural_slice_preserved(slice, direct_effects, transition_facts)
        || range_produced_len_structural_slice_preserved(slice, direct_effects, transition_facts)
}

fn scalar_eq_produced_len_step_preserved(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = slice else {
        return false;
    };
    let Some((scalar_name, produced_receiver)) =
        scalar_len_equality_side(lhs, rhs).or_else(|| scalar_len_equality_side(rhs, lhs))
    else {
        return false;
    };
    let Some(scalar_effect) = direct_effects.get(scalar_name) else {
        return false;
    };
    if !is_unit_increment_effect(scalar_effect, scalar_name) {
        return false;
    }

    let Some(produced_name) = collection_base_name(produced_receiver) else {
        return false;
    };
    let Some(produced_next) = direct_effects.get(produced_name) else {
        return false;
    };
    if push_back_value(produced_next, produced_receiver).is_none() {
        return false;
    }

    let produced_len = len_call((*produced_receiver).clone());
    let produced_next_len = len_call((*produced_next).clone());
    let produced_len_step = PureExpr::BinOp(
        Arc::new(produced_len),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    transition_facts
        .iter()
        .any(|fact| is_equality_between(fact, &produced_next_len, &produced_len_step))
}

fn scalar_len_equality_side<'a>(
    candidate: &'a PureExpr,
    other: &'a PureExpr,
) -> Option<(&'a str, &'a PureExpr)> {
    let PureExpr::Var(name, _) = candidate else {
        return None;
    };
    len_receiver(other).map(|receiver| (name.as_str(), receiver))
}

fn range_end_structural_slice_preserved(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
) -> bool {
    let Some((lhs, rhs)) = equality_to_exprs(slice) else {
        return false;
    };
    let Some((current_end, next_end, stable_end)) =
        range_accessor_effect_side(lhs, rhs, "end_log", direct_effects)
            .or_else(|| range_accessor_effect_side(rhs, lhs, "end_log", direct_effects))
    else {
        return false;
    };
    if !is_range_accessor(stable_end, "end_log") {
        return false;
    }

    transition_facts
        .iter()
        .any(|fact| is_equality_between(fact, current_end, &next_end))
}

fn range_start_structural_slice_preserved(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
) -> bool {
    let PureExpr::BinOp(lhs, op, rhs) = slice else {
        return false;
    };
    let (stable_start, current_start) = match op {
        BinOp::Le => (lhs.as_ref(), rhs.as_ref()),
        BinOp::Ge => (rhs.as_ref(), lhs.as_ref()),
        _ => return false,
    };
    if !is_range_accessor(stable_start, "start_log") {
        return false;
    }
    let Some(next_start) = range_accessor_next_expr(current_start, "start_log", direct_effects)
    else {
        return false;
    };

    transition_facts.iter().any(|fact| {
        is_equality_between(
            fact,
            &next_start,
            &PureExpr::BinOp(
                Arc::new((*current_start).clone()),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ),
        )
    })
}

fn range_produced_len_structural_slice_preserved(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = slice else {
        return false;
    };
    let Some((produced_receiver, range_diff)) =
        len_equality_side(lhs, rhs).or_else(|| len_equality_side(rhs, lhs))
    else {
        return false;
    };
    let Some((current_start, stable_start)) = range_start_difference_parts(range_diff) else {
        return false;
    };
    if !is_range_accessor(stable_start, "start_log") {
        return false;
    }
    let Some(next_start) = range_accessor_next_expr(current_start, "start_log", direct_effects)
    else {
        return false;
    };

    let Some(produced_name) = collection_base_name(produced_receiver) else {
        return false;
    };
    let Some(produced_next) = direct_effects.get(produced_name) else {
        return false;
    };
    if push_back_value(produced_next, produced_receiver).is_none() {
        return false;
    }

    let produced_len = len_call((*produced_receiver).clone());
    let produced_next_len = len_call((*produced_next).clone());
    let produced_len_step = PureExpr::BinOp(
        Arc::new(produced_len),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    let start_step = PureExpr::BinOp(
        Arc::new((*current_start).clone()),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    transition_facts
        .iter()
        .any(|fact| is_equality_between(fact, &produced_next_len, &produced_len_step))
        && transition_facts
            .iter()
            .any(|fact| is_equality_between(fact, &next_start, &start_step))
}

fn range_start_difference_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Sub, rhs) = expr else {
        return None;
    };
    if !is_range_accessor(lhs, "start_log") || !is_range_accessor(rhs, "start_log") {
        return None;
    }
    Some((lhs.as_ref(), rhs.as_ref()))
}

fn range_accessor_effect_side<'a>(
    candidate: &'a PureExpr,
    other: &'a PureExpr,
    method: &str,
    direct_effects: &HashMap<String, PureExpr>,
) -> Option<(&'a PureExpr, PureExpr, &'a PureExpr)> {
    let next_expr = range_accessor_next_expr(candidate, method, direct_effects)?;
    Some((candidate, next_expr, other))
}

fn range_accessor_next_expr(
    expr: &PureExpr,
    method: &str,
    direct_effects: &HashMap<String, PureExpr>,
) -> Option<PureExpr> {
    let receiver = range_accessor_receiver(expr, method)?;
    let name = collection_base_name(receiver)?;
    let effect = direct_effects.get(name)?;
    Some(range_accessor_call((*effect).clone(), method))
}

fn range_accessor_call(receiver: PureExpr, method: &str) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args: vec![],
    }
}

fn range_accessor_receiver<'a>(expr: &'a PureExpr, expected_method: &str) -> Option<&'a PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    (method == expected_method && args.is_empty()).then_some(receiver.as_ref())
}

fn is_range_accessor(expr: &PureExpr, expected_method: &str) -> bool {
    range_accessor_receiver(expr, expected_method).is_some()
}

fn is_unit_increment_effect(expr: &PureExpr, var: &str) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Add, rhs) = expr else {
        return false;
    };
    (is_var_named(lhs, var) && matches!(rhs.as_ref(), PureExpr::Int(1)))
        || (is_var_named(rhs, var) && matches!(lhs.as_ref(), PureExpr::Int(1)))
}

fn accumulator_addend<'a>(expr: &'a PureExpr, acc_var: &str) -> Option<&'a PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Add, rhs) = expr else {
        return None;
    };
    if is_var_named(lhs, acc_var) {
        return Some(rhs.as_ref());
    }
    if is_var_named(rhs, acc_var) {
        return Some(lhs.as_ref());
    }
    None
}

fn seq_iterator_structural_invariant_preserved(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    deref_effects: &HashMap<String, PureExpr>,
    double_deref_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
) -> bool {
    let Some((stable_side, produced_receiver, iter_state_view)) =
        seq_structural_concat_invariant_parts(slice)
    else {
        return false;
    };
    if expr_references_effect_var(
        stable_side,
        direct_effects,
        deref_effects,
        double_deref_effects,
    ) {
        return false;
    }

    let Some(produced_name) = collection_base_name(produced_receiver) else {
        return false;
    };
    let Some(produced_effect) = direct_effects.get(produced_name) else {
        return false;
    };
    let Some(appended_value) = push_back_value(produced_effect, produced_receiver) else {
        return false;
    };

    let Some(iter_state_name) = collection_base_name(iter_state_view) else {
        return false;
    };
    let next_view = if let Some(iter_state_effect) = direct_effects.get(iter_state_name) {
        PureExpr::View(Arc::new(iter_state_effect.clone()))
    } else {
        // Direct API and driver normalization may express iterator havoc only
        // through the exact transition equality
        // `iter@ == iter_prime@.push_front(value)`, without duplicating
        // `iter_prime` as a direct body effect. This remains a complete,
        // fail-closed step witness: the produced effect supplies the same
        // appended value and the equality pins the otherwise-havoced next
        // iterator state.
        let (name, sort, wrap_view) = match iter_state_view {
            PureExpr::View(inner) => {
                let PureExpr::Var(name, sort) = inner.as_ref() else {
                    return false;
                };
                (name, sort, true)
            }
            PureExpr::Var(name, sort @ Some(ExprSort::Seq)) => (name, sort, false),
            _ => return false,
        };
        let prime = PureExpr::Var(DerivedKind::Prime.format_name(name), sort.clone());
        if wrap_view {
            PureExpr::View(Arc::new(prime))
        } else {
            prime
        }
    };

    transition_facts
        .iter()
        .any(|fact| seq_iter_transition_matches(fact, iter_state_view, &next_view, appended_value))
}

fn seq_structural_concat_invariant_parts(
    expr: &PureExpr,
) -> Option<(&PureExpr, &PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    concat_side(rhs)
        .map(|(produced, iter_state)| (lhs.as_ref(), produced, iter_state))
        .or_else(|| {
            concat_side(lhs).map(|(produced, iter_state)| (rhs.as_ref(), produced, iter_state))
        })
}

fn concat_side(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method != "concat" || args.len() != 1 {
        return None;
    }
    Some((receiver.as_ref(), &args[0]))
}

fn expr_references_effect_var(
    expr: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    deref_effects: &HashMap<String, PureExpr>,
    double_deref_effects: &HashMap<String, PureExpr>,
) -> bool {
    direct_effects
        .keys()
        .chain(deref_effects.keys())
        .chain(double_deref_effects.keys())
        .any(|name| expr_mentions_var_syntactically(expr, name))
}

fn seq_iter_transition_matches(
    fact: &PureExpr,
    iter_state_view: &PureExpr,
    iter_next_view: &PureExpr,
    appended_value: &PureExpr,
) -> bool {
    let Some((lhs, rhs)) = equality_to_exprs(fact) else {
        return false;
    };
    (seq_view_equivalent(lhs, iter_state_view)
        && is_push_front_of(rhs, iter_next_view, appended_value))
        || (seq_view_equivalent(rhs, iter_state_view)
            && is_push_front_of(lhs, iter_next_view, appended_value))
}

fn equality_to_exprs(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    Some((lhs.as_ref(), rhs.as_ref()))
}

fn is_push_front_of(expr: &PureExpr, receiver: &PureExpr, value: &PureExpr) -> bool {
    let PureExpr::MethodCall {
        receiver: actual_receiver,
        method,
        args,
    } = expr
    else {
        return false;
    };
    matches!(method.as_str(), "push_front" | "push_front_ghost")
        && args.len() == 1
        && seq_view_equivalent(actual_receiver, receiver)
        && expr_same(&args[0], value)
}

fn seq_view_equivalent(actual: &PureExpr, expected: &PureExpr) -> bool {
    if expr_same(actual, expected) {
        return true;
    }
    match (actual, expected) {
        (PureExpr::View(actual), PureExpr::Var(expected_name, Some(ExprSort::Seq)))
        | (PureExpr::Var(expected_name, Some(ExprSort::Seq)), PureExpr::View(actual)) => {
            matches!(
                actual.as_ref(),
                PureExpr::Var(actual_name, Some(ExprSort::Seq))
                    if actual_name == expected_name
            )
        }
        _ => false,
    }
}

fn no_effect_preserves_current_invariant(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    deref_effects: &HashMap<String, PureExpr>,
    double_deref_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
    current_invariants: &[&PureExpr],
    relevant_modified_vars: &[&str],
) -> bool {
    relevant_modified_vars.is_empty()
        && direct_effects.is_empty()
        && deref_effects.is_empty()
        && double_deref_effects.is_empty()
        && transition_facts.is_empty()
        && current_invariants
            .iter()
            .any(|invariant| **invariant == *slice)
}

fn prefix_push_preserves_index_relation(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
    current_invariants: &[&PureExpr],
) -> bool {
    let PureExpr::Forall { var, body, .. } = slice else {
        return false;
    };
    let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = body.as_ref() else {
        return false;
    };

    let mut conjuncts = Vec::new();
    flatten_and_conjuncts(antecedent, &mut conjuncts);
    if !conjuncts
        .iter()
        .any(|conjunct| is_nonnegative_bound_for_var(conjunct, var))
    {
        return false;
    }
    let Some(produced_receiver) = conjuncts
        .iter()
        .find_map(|conjunct| len_upper_bound_receiver_for_var(conjunct, var))
    else {
        return false;
    };
    let Some(produced_name) = var_name(produced_receiver) else {
        return false;
    };
    let Some(produced_effect) = direct_effects.get(produced_name) else {
        return false;
    };
    let Some(appended_value) = push_back_value(produced_effect, produced_receiver) else {
        return false;
    };
    let produced_len = len_call(produced_receiver.clone());
    let produced_next_len = len_call(produced_effect.clone());
    if !transition_facts.iter().any(|fact| {
        is_equality_between(
            fact,
            &produced_next_len,
            &PureExpr::BinOp(
                Arc::new(produced_len.clone()),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ),
        )
    }) {
        return false;
    }

    let Some((relation_receiver, index, relation_rhs)) = index_equality_for_var(consequent, var)
    else {
        return false;
    };
    if !expr_same(index, &PureExpr::Var(var.clone(), None))
        || !expr_same(relation_receiver, produced_receiver)
    {
        return false;
    }

    let mut substitutions = HashMap::new();
    substitutions.insert(var.clone(), produced_len.clone());
    let rhs_at_old_len = relation_rhs.substitute(&substitutions);
    if expr_same(&rhs_at_old_len, appended_value)
        || transition_facts
            .iter()
            .any(|fact| is_equality_between(fact, appended_value, &rhs_at_old_len))
    {
        return true;
    }

    let Some(offset) = add_relation_offset_for_var(relation_rhs, var) else {
        return false;
    };
    let Some(state_start) = transition_facts
        .iter()
        .find_map(|fact| equality_other_side(fact, appended_value))
        .filter(is_start_log_call)
    else {
        return false;
    };
    current_invariants.iter().any(|invariant| {
        is_equality_between(
            invariant,
            &produced_len,
            &PureExpr::BinOp(
                Arc::new(state_start.clone()),
                BinOp::Sub,
                Arc::new(offset.clone()),
            ),
        )
    })
}

fn len_call(receiver: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "len".to_string(),
        args: vec![],
    }
}

fn add_relation_offset_for_var(expr: &PureExpr, var: &str) -> Option<PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Add, rhs) = expr else {
        return None;
    };
    if is_var_named(lhs, var) {
        return Some(rhs.as_ref().clone());
    }
    if is_var_named(rhs, var) {
        return Some(lhs.as_ref().clone());
    }
    None
}

fn equality_other_side(expr: &PureExpr, expected: &PureExpr) -> Option<PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    if expr_same(lhs, expected) {
        return Some(rhs.as_ref().clone());
    }
    if expr_same(rhs, expected) {
        return Some(lhs.as_ref().clone());
    }
    None
}

fn is_start_log_call(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall { method, args, .. } if method == "start_log" && args.is_empty()
    )
}

fn set_effect_preserves_len_equality(
    slice: &PureExpr,
    deref_effects: &HashMap<String, PureExpr>,
) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = slice else {
        return false;
    };
    let Some((receiver, other_side)) =
        len_equality_side(lhs, rhs).or_else(|| len_equality_side(rhs, lhs))
    else {
        return false;
    };
    let Some(base_name) = collection_base_name(receiver) else {
        return false;
    };
    if other_side.free_vars().iter().any(|name| name == base_name) {
        return false;
    }

    deref_effects.values().any(|effect| {
        set_effect_receiver(effect)
            .is_some_and(|effect_receiver| collection_receiver_same(effect_receiver, receiver))
    })
}

fn prefix_push_preserves_triangular_sum(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
) -> bool {
    let Some((accumulator, produced_len)) = triangular_sum_invariant_parts(slice) else {
        return false;
    };
    let Some(accumulator_name) = collection_base_name(accumulator) else {
        return false;
    };
    let Some(produced_receiver) = len_receiver(produced_len) else {
        return false;
    };
    let Some(produced_name) = collection_base_name(produced_receiver) else {
        return false;
    };

    let Some(accumulator_effect) = direct_effects.get(accumulator_name) else {
        return false;
    };
    let Some(increment) = add_with_base_value(accumulator_effect, accumulator) else {
        return false;
    };
    let Some(produced_effect) = direct_effects.get(produced_name) else {
        return false;
    };
    if push_back_value(produced_effect, produced_receiver)
        .is_none_or(|pushed| !expr_same(pushed, increment))
    {
        return false;
    }

    let produced_next_len = len_call(produced_effect.clone());
    let canonical_produced_len = len_call(PureExpr::Var(produced_name.to_string(), None));
    let produced_len_plus_one = PureExpr::BinOp(
        Arc::new(canonical_produced_len),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    let has_len_fact = transition_facts
        .iter()
        .any(|fact| is_equality_between(fact, &produced_next_len, &produced_len_plus_one));
    let has_increment_fact = transition_facts
        .iter()
        .any(|fact| is_equality_between(fact, increment, &produced_len_plus_one));
    has_len_fact && has_increment_fact
}

fn additive_nonnegative_bound_preserved(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
    current_invariants: &[&PureExpr],
) -> bool {
    let Some(var_name) = nonnegative_bound_var(slice) else {
        return false;
    };
    if !current_invariants
        .iter()
        .any(|invariant| is_nonnegative_bound_for_var(invariant, var_name))
    {
        return false;
    }
    let Some(effect) = direct_effects.get(var_name) else {
        return false;
    };
    let base = PureExpr::Var(var_name.to_string(), None);
    let Some(increment) = add_with_base_value(effect, &base) else {
        return false;
    };
    expr_known_nonnegative(increment, transition_facts, current_invariants)
}

fn unit_increment_upper_bound_preserved(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    current_invariants: &[&PureExpr],
    loop_condition: Option<&PureExpr>,
) -> bool {
    let Some((var_name, upper_bound)) = upper_bound_slice_parts(slice) else {
        return false;
    };
    if !current_invariants.iter().any(|invariant| {
        upper_bound_slice_parts(invariant).is_some_and(|(inv_var, inv_bound)| {
            inv_var == var_name && expr_same_mod_zero(inv_bound, upper_bound)
        })
    }) {
        return false;
    }
    let Some(effect) = direct_effects.get(var_name) else {
        return false;
    };
    if !is_unit_increment_effect(effect, var_name) {
        return false;
    }
    let Some(condition) = loop_condition else {
        return false;
    };
    strict_upper_bound_condition_for_var(condition, var_name, upper_bound, current_invariants)
}

fn upper_bound_slice_parts(expr: &PureExpr) -> Option<(&str, &PureExpr)> {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Le, rhs) => var_name(lhs).map(|name| (name, rhs.as_ref())),
        PureExpr::BinOp(lhs, BinOp::Ge, rhs) => var_name(rhs).map(|name| (name, lhs.as_ref())),
        _ => None,
    }
}

fn strict_upper_bound_condition_for_var(
    condition: &PureExpr,
    var_name: &str,
    upper_bound: &PureExpr,
    current_invariants: &[&PureExpr],
) -> bool {
    strict_upper_bound_condition_matches(
        condition,
        &PureExpr::Var(var_name.to_string(), None),
        upper_bound,
    ) || current_invariants.iter().any(|invariant| {
        scalar_len_equality_for_var(invariant, var_name).is_some_and(|produced_receiver| {
            strict_upper_bound_condition_matches(
                condition,
                &len_call((*produced_receiver).clone()),
                upper_bound,
            )
        })
    })
}

fn strict_upper_bound_condition_matches(
    condition: &PureExpr,
    lower: &PureExpr,
    upper_bound: &PureExpr,
) -> bool {
    match condition {
        PureExpr::BinOp(lhs, BinOp::Lt, rhs) => {
            expr_same(lhs, lower) && expr_same_mod_zero(rhs, upper_bound)
        }
        PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
            expr_same(rhs, lower) && expr_same_mod_zero(lhs, upper_bound)
        }
        _ => false,
    }
}

fn scalar_len_equality_for_var<'a>(expr: &'a PureExpr, expected_var: &str) -> Option<&'a PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    scalar_len_equality_side(lhs, rhs)
        .or_else(|| scalar_len_equality_side(rhs, lhs))
        .and_then(|(var_name, receiver)| (var_name == expected_var).then_some(receiver))
}

fn expr_same_mod_zero(actual: &PureExpr, expected: &PureExpr) -> bool {
    expr_same(actual, expected)
        || subtract_zero_operand(actual).is_some_and(|inner| expr_same(inner, expected))
        || subtract_zero_operand(expected).is_some_and(|inner| expr_same(actual, inner))
}

fn subtract_zero_operand(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Sub, rhs) = expr else {
        return None;
    };
    matches!(rhs.as_ref(), PureExpr::Int(0)).then_some(lhs.as_ref())
}

fn nonnegative_bound_var(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Le, rhs) => matches!(lhs.as_ref(), PureExpr::Int(0))
            .then(|| var_name(rhs))
            .flatten(),
        PureExpr::BinOp(lhs, BinOp::Ge, rhs) => matches!(rhs.as_ref(), PureExpr::Int(0))
            .then(|| var_name(lhs))
            .flatten(),
        _ => None,
    }
}

fn expr_known_nonnegative(
    expr: &PureExpr,
    transition_facts: &[PureExpr],
    current_invariants: &[&PureExpr],
) -> bool {
    expr_nonnegative_by_shape(expr)
        || var_name(expr).is_some_and(|name| {
            current_invariants
                .iter()
                .any(|invariant| is_nonnegative_bound_for_var(invariant, name))
        })
        || transition_facts.iter().any(|fact| {
            equality_to_exprs(fact).is_some_and(|(lhs, rhs)| {
                (expr_same(lhs, expr) && expr_nonnegative_by_shape(rhs))
                    || (expr_same(rhs, expr) && expr_nonnegative_by_shape(lhs))
            })
        })
}

fn expr_nonnegative_by_shape(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(value) => *value >= 0,
        PureExpr::MethodCall { method, args, .. } if method == "len" && args.is_empty() => true,
        PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
            expr_nonnegative_by_shape(lhs) && expr_nonnegative_by_shape(rhs)
        }
        _ => false,
    }
}

fn triangular_sum_invariant_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    triangular_sum_invariant_orientation(lhs, rhs)
        .or_else(|| triangular_sum_invariant_orientation(rhs, lhs))
}

fn triangular_sum_invariant_orientation<'a>(
    twice_accumulator: &'a PureExpr,
    triangular_product: &'a PureExpr,
) -> Option<(&'a PureExpr, &'a PureExpr)> {
    let accumulator = times_two_operand(twice_accumulator)?;
    let produced_len = triangular_product_len(triangular_product)?;
    Some((accumulator, produced_len))
}

fn times_two_operand(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Mul, rhs) = expr else {
        return None;
    };
    match (lhs.as_ref(), rhs.as_ref()) {
        (PureExpr::Int(2), value) | (value, PureExpr::Int(2)) => Some(value),
        _ => None,
    }
}

fn triangular_product_len(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Mul, rhs) = expr else {
        return None;
    };
    if is_plus_one_of(rhs, lhs) {
        return Some(lhs.as_ref());
    }
    if is_plus_one_of(lhs, rhs) {
        return Some(rhs.as_ref());
    }
    None
}

fn is_plus_one_of(candidate: &PureExpr, base: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Add, rhs) = candidate else {
        return false;
    };
    matches!(
        (lhs.as_ref(), rhs.as_ref()),
        (PureExpr::Int(1), other) | (other, PureExpr::Int(1)) if expr_same(other, base)
    )
}

fn len_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    (method == "len" && args.is_empty()).then_some(receiver.as_ref())
}

fn add_with_base_value<'a>(expr: &'a PureExpr, base: &PureExpr) -> Option<&'a PureExpr> {
    let expr = value_projection_arg(expr).unwrap_or(expr);
    let PureExpr::BinOp(lhs, BinOp::Add, rhs) = expr else {
        return None;
    };
    if expr_same(lhs, base) || base_names_same(lhs, base) {
        return Some(rhs.as_ref());
    }
    if expr_same(rhs, base) || base_names_same(rhs, base) {
        return Some(lhs.as_ref());
    }
    None
}

fn value_projection_arg(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    (name == "__trust_wp_tuple_get_0" && args.len() == 1).then_some(&args[0])
}

fn base_names_same(actual: &PureExpr, expected: &PureExpr) -> bool {
    collection_base_name(actual)
        .zip(collection_base_name(expected))
        .is_some_and(|(actual, expected)| actual == expected)
}

fn len_equality_side<'a>(
    candidate: &'a PureExpr,
    other: &'a PureExpr,
) -> Option<(&'a PureExpr, &'a PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = candidate
    else {
        return None;
    };
    (method == "len" && args.is_empty()).then_some((receiver.as_ref(), other))
}

fn set_effect_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    (method == "set" && args.len() == 2).then_some(receiver.as_ref())
}

fn prefix_push_set_preserves_forall(
    slice: &PureExpr,
    direct_effects: &HashMap<String, PureExpr>,
    deref_effects: &HashMap<String, PureExpr>,
    transition_facts: &[PureExpr],
    current_invariants: &[&PureExpr],
) -> bool {
    let PureExpr::Forall { var, body, .. } = slice else {
        return false;
    };
    if !current_invariants
        .iter()
        .any(|current| universal_invariant_matches(current, slice))
    {
        return false;
    }
    let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = body.as_ref() else {
        return false;
    };

    let mut conjuncts = Vec::new();
    flatten_and_conjuncts(antecedent, &mut conjuncts);
    if !conjuncts
        .iter()
        .any(|conjunct| is_nonnegative_bound_for_var(conjunct, var))
    {
        return false;
    }
    let Some(produced_receiver) = conjuncts
        .iter()
        .find_map(|conjunct| len_upper_bound_receiver_for_var(conjunct, var))
    else {
        return false;
    };
    let Some(produced_name) = var_name(produced_receiver) else {
        return false;
    };
    let Some(produced_effect) = direct_effects.get(produced_name) else {
        return false;
    };
    let Some(appended_value) = push_back_value(produced_effect, produced_receiver) else {
        return false;
    };
    if !transition_facts.iter().any(|fact| {
        is_equality_between(
            fact,
            appended_value,
            &PureExpr::MethodCall {
                receiver: Arc::new(produced_receiver.clone()),
                method: "len".to_string(),
                args: vec![],
            },
        )
    }) {
        return false;
    }
    if !transition_facts
        .iter()
        .any(|fact| push_back_len_step_fact(fact, produced_effect, produced_receiver))
    {
        return false;
    }

    let Some((collection_receiver, index, written_value)) = index_equality_for_var(consequent, var)
    else {
        return false;
    };
    if !expr_same(index, &PureExpr::Var(var.clone(), None)) {
        return false;
    }

    deref_effects
        .values()
        .any(|effect| is_set_effect(effect, collection_receiver, appended_value, written_value))
}

fn push_back_len_step_fact(
    fact: &PureExpr,
    produced_effect: &PureExpr,
    produced_receiver: &PureExpr,
) -> bool {
    let produced_next_len = PureExpr::MethodCall {
        receiver: Arc::new(produced_effect.clone()),
        method: "len".to_string(),
        args: vec![],
    };
    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(produced_receiver.clone()),
        method: "len".to_string(),
        args: vec![],
    };
    let len_plus_one = PureExpr::BinOp(
        Arc::new(produced_len.clone()),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    let one_plus_len = PureExpr::BinOp(
        Arc::new(PureExpr::Int(1)),
        BinOp::Add,
        Arc::new(produced_len),
    );
    is_equality_between(fact, &produced_next_len, &len_plus_one)
        || is_equality_between(fact, &produced_next_len, &one_plus_len)
}

fn flatten_and_conjuncts<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
    if let PureExpr::BinOp(lhs, BinOp::And, rhs) = expr {
        flatten_and_conjuncts(lhs, out);
        flatten_and_conjuncts(rhs, out);
    } else {
        out.push(expr);
    }
}

fn var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        _ => None,
    }
}

fn is_nonnegative_bound_for_var(expr: &PureExpr, var: &str) -> bool {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Le, rhs) => {
            matches!(lhs.as_ref(), PureExpr::Int(0)) && is_var_named(rhs, var)
        }
        PureExpr::BinOp(lhs, BinOp::Ge, rhs) => {
            is_var_named(lhs, var) && matches!(rhs.as_ref(), PureExpr::Int(0))
        }
        _ => false,
    }
}

fn is_var_named(expr: &PureExpr, name: &str) -> bool {
    matches!(expr, PureExpr::Var(var_name, _) if var_name == name)
}

fn len_upper_bound_receiver_for_var<'a>(expr: &'a PureExpr, var: &str) -> Option<&'a PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Lt, rhs) = expr else {
        return None;
    };
    if !is_var_named(lhs, var) {
        return None;
    }
    match rhs.as_ref() {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "len" && args.is_empty() => Some(receiver.as_ref()),
        _ => None,
    }
}

fn push_back_value<'a>(expr: &'a PureExpr, expected_receiver: &PureExpr) -> Option<&'a PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if !matches!(method.as_str(), "push_back" | "push_back_ghost") || args.len() != 1 {
        return None;
    }
    collection_receiver_same(receiver, expected_receiver).then_some(&args[0])
}

fn index_equality_for_var<'a>(
    expr: &'a PureExpr,
    var: &str,
) -> Option<(&'a PureExpr, &'a PureExpr, &'a PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    if let Some((receiver, index)) = index_call(lhs, var) {
        return Some((receiver, index, rhs));
    }
    if let Some((receiver, index)) = index_call(rhs, var) {
        return Some((receiver, index, lhs));
    }
    None
}

fn index_call<'a>(expr: &'a PureExpr, var: &str) -> Option<(&'a PureExpr, &'a PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if !matches!(method.as_str(), "index" | "index_logic") || args.len() != 1 {
        return None;
    }
    is_var_named(&args[0], var).then_some((receiver.as_ref(), &args[0]))
}

fn is_set_effect(
    expr: &PureExpr,
    expected_receiver: &PureExpr,
    expected_index: &PureExpr,
    expected_value: &PureExpr,
) -> bool {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return false;
    };
    method == "set"
        && args.len() == 2
        && collection_receiver_same(receiver, expected_receiver)
        && expr_same(&args[0], expected_index)
        && expr_same(&args[1], expected_value)
}

fn collection_receiver_same(actual: &PureExpr, expected: &PureExpr) -> bool {
    expr_same(actual, expected) || base_names_same(actual, expected)
}

fn collection_base_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner) => collection_base_name(inner),
        _ => None,
    }
}

fn is_equality_between(expr: &PureExpr, lhs_expected: &PureExpr, rhs_expected: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    (expr_same(lhs, lhs_expected) && expr_same(rhs, rhs_expected))
        || (expr_same(lhs, rhs_expected) && expr_same(rhs, lhs_expected))
}

fn expr_same(actual: &PureExpr, expected: &PureExpr) -> bool {
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(actual, expected)
}

fn strip_forall_triggers_for_negation(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Forall {
            var,
            var_sort,
            body,
            ..
        } => PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers: vec![],
        },
        other => other,
    })
}

fn assert_current_universal_skolem_instance(
    encoder: &mut AYEncoder,
    expr: &PureExpr,
) -> Result<(), EncodingError> {
    let mut substitutions = HashMap::new();
    let mut current = expr;
    while let PureExpr::Forall {
        var,
        var_sort,
        body,
        ..
    } = current
    {
        substitutions.insert(
            var.clone(),
            PureExpr::Var(format!("sk_{var}"), var_sort.clone()),
        );
        current = body;
    }

    if substitutions.is_empty() {
        return Ok(());
    }

    let ground_instance = current.substitute(&substitutions);
    let term = encoder.encode_formula(&ground_instance)?;
    let term = encoder.coerce_bool_operand(term);
    encoder.assert_term(term);
    Ok(())
}

fn assert_universal_skolem_instances_for_slice(
    encoder: &mut AYEncoder,
    source_invariants: &[&PureExpr],
    target_slice: &PureExpr,
) -> Result<(), EncodingError> {
    let target_terms = universal_skolem_terms(target_slice);
    if target_terms.is_empty() {
        return Ok(());
    }

    let mut seen = HashSet::new();
    for invariant in source_invariants {
        let Some(instance) = instantiate_universal_with_terms(invariant, &target_terms) else {
            continue;
        };
        if !seen.insert(instance.clone()) {
            continue;
        }
        let term = encoder.encode_formula(&instance)?;
        let term = encoder.coerce_bool_operand(term);
        encoder.assert_term(term);
    }
    Ok(())
}

fn universal_skolem_terms(expr: &PureExpr) -> Vec<PureExpr> {
    let mut terms = Vec::new();
    let mut current = expr;
    while let PureExpr::Forall {
        var,
        var_sort,
        body,
        ..
    } = current
    {
        terms.push(PureExpr::Var(format!("sk_{var}"), var_sort.clone()));
        current = body;
    }
    terms
}

fn instantiate_universal_with_terms(
    expr: &PureExpr,
    target_terms: &[PureExpr],
) -> Option<PureExpr> {
    let mut substitutions = HashMap::new();
    let mut current = expr;
    while let PureExpr::Forall {
        var,
        var_sort,
        body,
        ..
    } = current
    {
        substitutions.insert(
            var.clone(),
            skolem_term_for_universal_var(var, var_sort.as_ref(), target_terms),
        );
        current = body;
    }

    (!substitutions.is_empty()).then(|| current.substitute(&substitutions))
}

fn skolem_term_for_universal_var(
    var: &str,
    var_sort: Option<&ExprSort>,
    target_terms: &[PureExpr],
) -> PureExpr {
    let expected_name = format!("sk_{var}");
    if let Some(term) = target_terms.iter().find(|term| {
        matches!(term, PureExpr::Var(name, _) if name == &expected_name)
            && skolem_term_matches_sort(term, var_sort)
    }) {
        return term.clone();
    }
    if let Some(term) = target_terms
        .iter()
        .find(|term| skolem_term_matches_sort(term, var_sort))
    {
        return term.clone();
    }
    PureExpr::Var(expected_name, var_sort.cloned())
}

fn skolem_term_matches_sort(term: &PureExpr, expected: Option<&ExprSort>) -> bool {
    let Some(expected) = expected else {
        return true;
    };
    matches!(term, PureExpr::Var(_, Some(actual)) if actual == expected)
        || matches!(expected, ExprSort::Int)
            && matches!(term, PureExpr::Var(_, None | Some(ExprSort::Int)))
}

fn hashmap_list_loop_forall_grounding_enabled(
    config: &LoopEncoderConfig<'_>,
    invariants: &[PureExpr],
) -> bool {
    if invariants.iter().any(is_hashmap_list_invariant_body) {
        return true;
    }
    config.type_invariants.is_some_and(|type_invariants| {
        type_invariants
            .iter()
            .any(|invariant| is_hashmap_list_invariant_body(invariant.body()))
    })
}

fn is_hashmap_list_invariant_body(expr: &PureExpr) -> bool {
    expr_contains_logic_call(expr, "good_bucket")
        && expr_contains_logic_call(expr, "no_double_binding")
}

fn expr_contains_logic_call(expr: &PureExpr, expected: &str) -> bool {
    let expected = normalize_logic_name(expected);
    let mut found = false;
    expr.for_each_recursive(|node| {
        if found {
            return;
        }
        match node {
            PureExpr::LogicFnCall { name, .. }
                if normalize_logic_name(name).ends_with(&expected) =>
            {
                found = true;
            }
            PureExpr::MethodCall { method, .. }
                if normalize_logic_name(method).ends_with(&expected) =>
            {
                found = true;
            }
            _ => {}
        }
    });
    found
}

fn normalize_logic_name(name: &str) -> String {
    name.chars().filter(|ch| *ch != '_').collect()
}

// Recursive unfolding helpers: see `recursive_unfolding.rs` (#2591).
// Invariant transform helpers: see `invariant_transforms.rs` (#2591).

#[cfg(test)]
mod tests {
    use super::*;

    fn v(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn seq_v(name: &str) -> PureExpr {
        PureExpr::Var(
            name.to_string(),
            Some(trust_wp_core::formula::ExprSort::Seq),
        )
    }

    fn add_expr(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Add, Arc::new(rhs))
    }

    fn mul_expr(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Mul, Arc::new(rhs))
    }

    fn eq_expr(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
    }

    fn push_back_expr(receiver: PureExpr, value: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: "push_back".to_string(),
            args: vec![value],
        }
    }

    fn push_front_expr(receiver: PureExpr, value: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: "push_front_ghost".to_string(),
            args: vec![value],
        }
    }

    fn concat_expr(receiver: PureExpr, suffix: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: "concat".to_string(),
            args: vec![suffix],
        }
    }

    fn start_log_expr(receiver: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: "start_log".to_string(),
            args: vec![],
        }
    }

    fn end_log_expr(receiver: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: "end_log".to_string(),
            args: vec![],
        }
    }

    fn view_expr(expr: PureExpr) -> PureExpr {
        PureExpr::View(Arc::new(expr))
    }

    fn tuple_get_0_expr(expr: PureExpr) -> PureExpr {
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![expr],
        }
    }

    fn method_expr(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: method.to_string(),
            args,
        }
    }

    fn logic_expr(name: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args,
        }
    }

    #[test]
    fn direct_preservation_accepts_reflexive_slice_with_body_effect() {
        let slice = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("x".to_string(), None)),
        );
        let mut direct_effects = HashMap::new();
        direct_effects.insert(
            "x".to_string(),
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ),
        );
        let current_invariants = vec![&slice];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &[],
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    /// A guarded indexed write `if cond { v[i] = x }` lowers to a branch-merged
    /// effect `Ite(cond, base.set(i, x), base)`. The point-write synthesis must
    /// emit an UNCONDITIONAL length frame (`len(updated) == len(base)`, true on
    /// both arms) plus `cond`-GUARDED point-write/element-frame facts. This is the
    /// frame that flips `inferred_invariants::y`'s `old_v@.len() == v@.len()`. (#1295)
    #[test]
    fn point_write_ite_set_emits_unconditional_length_and_guarded_facts() {
        let base = method_expr(v("v"), "view", vec![]); // stand-in receiver
        let cond = PureExpr::BinOp(
            Arc::new(v("i")),
            BinOp::Lt,
            Arc::new(method_expr(base.clone(), "len", vec![])),
        );
        let set_effect = method_expr(base.clone(), "set", vec![v("i"), PureExpr::Int(0)]);
        let ite = PureExpr::Ite(
            Arc::new(cond.clone()),
            Arc::new(set_effect),
            Arc::new(base.clone()),
        );
        let updated = PureExpr::View(Arc::new(v("v_prime")));

        let mut facts = Vec::new();
        extend_point_write_facts_for_receiver(&mut facts, &updated, &ite);

        // Exactly one UNCONDITIONAL length-equality fact (not wrapped in Implies).
        let unconditional_len = facts
            .iter()
            .filter(|f| {
                matches!(
                    f,
                    PureExpr::BinOp(lhs, BinOp::Eq, _)
                        if matches!(lhs.as_ref(),
                            PureExpr::MethodCall { method, .. } if method == "len")
                )
            })
            .count();
        assert_eq!(
            unconditional_len, 1,
            "expected one unconditional length frame, got facts: {facts:?}"
        );
        // The point-write/element-frame facts must be guarded by `cond` (Implies).
        let guarded = facts
            .iter()
            .filter(|f| matches!(f, PureExpr::BinOp(_, BinOp::Implies, _)))
            .count();
        assert!(
            guarded >= 2,
            "expected guarded point-write + element-frame facts, got: {facts:?}"
        );
    }

    /// A plain (unconditional) `set` effect still synthesizes the unconditional
    /// point-write, length, and element-frame facts (no `Ite` wrapper). Guards
    /// against the `Ite` branch swallowing the base path. (#1295)
    #[test]
    fn point_write_bare_set_emits_unconditional_facts() {
        let base = method_expr(v("v"), "view", vec![]);
        let set_effect = method_expr(base.clone(), "set", vec![v("i"), PureExpr::Int(7)]);
        let updated = PureExpr::View(Arc::new(v("v_prime")));

        let mut facts = Vec::new();
        extend_point_write_facts_for_receiver(&mut facts, &updated, &set_effect);

        // No fact should be guarded by Implies for a bare unconditional set.
        assert!(
            !facts
                .iter()
                .any(|f| matches!(f, PureExpr::BinOp(_, BinOp::Implies, _))),
            "bare set must emit unconditional facts, got: {facts:?}"
        );
        assert!(
            facts.len() >= 3,
            "bare set should emit point-write, length, and frame facts, got: {facts:?}"
        );
    }

    #[test]
    fn point_write_swap_transposition_emits_exchange_fact() {
        // The driver models `v.swap(a, b)` as the closed-form transposition deref
        // effect base.set(a, base.index_logic(b)).set(b, base.index_logic(a)).
        // The synthesizer must re-derive the literal `exchange(updated, base, a, b)`
        // so the Seq permutation axioms fire. (swap->exchange)
        let base = method_expr(v("v"), "view", vec![]);
        let at_b = method_expr(base.clone(), "index_logic", vec![v("b")]);
        let at_a = method_expr(base.clone(), "index_logic", vec![v("a")]);
        let set_a = method_expr(base.clone(), "set", vec![v("a"), at_b]);
        let swap_effect = method_expr(set_a, "set", vec![v("b"), at_a]);
        let updated = PureExpr::View(Arc::new(v("v_prime")));

        let mut facts = Vec::new();
        extend_point_write_facts_for_receiver(&mut facts, &updated, &swap_effect);

        let exchange = facts.iter().find_map(|f| match f {
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if method == "exchange" => Some((receiver.as_ref(), args.as_slice())),
            _ => None,
        });
        let (recv, args) = exchange.expect("swap effect must emit an exchange fact");
        assert_eq!(
            recv, &updated,
            "exchange receiver should be the updated view"
        );
        assert_eq!(args.len(), 3, "exchange takes (base, a, b)");
        assert_eq!(args[0], base, "exchange base should be the old view");
        assert_eq!(args[1], v("a"));
        assert_eq!(args[2], v("b"));
    }

    #[test]
    fn point_write_generic_double_set_does_not_emit_exchange() {
        // A double `set` that is NOT a transposition (mismatched index_logic reads)
        // must not be mistaken for a swap.
        let base = method_expr(v("v"), "view", vec![]);
        let set_a = method_expr(base.clone(), "set", vec![v("a"), PureExpr::Int(1)]);
        let double_set = method_expr(set_a, "set", vec![v("b"), PureExpr::Int(2)]);
        let updated = PureExpr::View(Arc::new(v("v_prime")));

        let mut facts = Vec::new();
        extend_point_write_facts_for_receiver(&mut facts, &updated, &double_set);
        assert!(
            !facts.iter().any(|f| matches!(
                f,
                PureExpr::MethodCall { method, .. } if method == "exchange"
            )),
            "non-transposition double set must not emit an exchange fact, got: {facts:?}"
        );
    }

    #[test]
    fn direct_preservation_expands_well_formed_wrapper_for_point_write() {
        let mem = v("self");
        let idx = v("i");
        let null = v("NULL");
        let indexed = method_expr(mem.clone(), "index_logic", vec![idx.clone()]);
        let nonnull_idx = method_expr(mem.clone(), "nonnull_ptr", vec![idx.clone()]);
        let nonnull_indexed = method_expr(mem.clone(), "nonnull_ptr", vec![indexed.clone()]);
        let wrapper_body = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(nonnull_idx),
                BinOp::Implies,
                Arc::new(PureExpr::BinOp(
                    Arc::new(eq_expr(indexed.clone(), null.clone())),
                    BinOp::Or,
                    Arc::new(nonnull_indexed),
                )),
            )),
            triggers: vec![],
        };
        let logic_fns = vec![LogicFnDef::new(
            "mem_is_well_formed".to_string(),
            "Memory::mem_is_well_formed".to_string(),
            vec!["self".to_string()],
            wrapper_body,
        )];
        let slice = method_expr(mem.clone(), "mem_is_well_formed", vec![]);
        let r_safe = PureExpr::BinOp(
            Arc::new(eq_expr(v("r"), null)),
            BinOp::Or,
            Arc::new(method_expr(mem.clone(), "nonnull_ptr", vec![v("r")])),
        );
        let mut deref_effects = HashMap::new();
        deref_effects.insert(
            "self".to_string(),
            method_expr(mem.clone(), "set", vec![v("tmp"), v("r")]),
        );
        let current_invariants = vec![&slice, &r_safe];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &HashMap::new(),
            &deref_effects,
            &HashMap::new(),
            &[],
            None,
            &current_invariants,
            &["self"],
            &logic_fns,
        ));
    }

    #[test]
    fn direct_preservation_expands_disjunctive_well_formed_wrapper_for_point_write() {
        let mem = v("self");
        let idx = v("i");
        let null = v("NULL");
        let indexed = method_expr(mem.clone(), "index_logic", vec![idx.clone()]);
        let nonnull_idx = logic_expr("Memory::nonnull_ptr", vec![mem.clone(), idx]);
        let nonnull_indexed = logic_expr("Memory::nonnull_ptr", vec![mem.clone(), indexed.clone()]);
        let safe_indexed = PureExpr::BinOp(
            Arc::new(eq_expr(indexed.clone(), null.clone())),
            BinOp::Or,
            Arc::new(nonnull_indexed),
        );
        let wrapper_body = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(safe_indexed),
                BinOp::Or,
                Arc::new(PureExpr::UnOp(
                    trust_wp_core::formula::UnOp::Not,
                    Arc::new(nonnull_idx),
                )),
            )),
            triggers: vec![],
        };
        let logic_fns = vec![LogicFnDef::new(
            "mem_is_well_formed".to_string(),
            "Memory::mem_is_well_formed".to_string(),
            vec!["self".to_string()],
            wrapper_body,
        )];
        let slice = logic_expr("Memory::mem_is_well_formed", vec![mem.clone()]);
        let r_safe = PureExpr::BinOp(
            Arc::new(eq_expr(v("r"), null)),
            BinOp::Or,
            Arc::new(logic_expr("Memory::nonnull_ptr", vec![mem.clone(), v("r")])),
        );
        let mut deref_effects = HashMap::new();
        deref_effects.insert(
            "self".to_string(),
            method_expr(mem.clone(), "set", vec![v("l"), v("r")]),
        );
        let current_invariants = vec![&slice, &r_safe];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &HashMap::new(),
            &deref_effects,
            &HashMap::new(),
            &[],
            None,
            &current_invariants,
            &["self"],
            &logic_fns,
        ));
    }

    #[test]
    fn direct_preservation_accepts_literal_start_triangular_sum_slice() {
        let produced = seq_v("produced");
        let produced_len = len_call(produced.clone());
        let loop_elem = v("i");
        let slice = eq_expr(
            mul_expr(PureExpr::View(Arc::new(v("sum"))), PureExpr::Int(2)),
            mul_expr(
                produced_len.clone(),
                add_expr(produced_len.clone(), PureExpr::Int(1)),
            ),
        );
        let produced_next = push_back_expr(produced.clone(), loop_elem.clone());
        let produced_next_len = len_call(produced_next.clone());
        let len_plus_one = add_expr(produced_len.clone(), PureExpr::Int(1));

        let mut direct_effects = HashMap::new();
        direct_effects.insert("sum".to_string(), add_expr(v("sum"), loop_elem.clone()));
        direct_effects.insert("produced".to_string(), produced_next.clone());
        let transition_facts = vec![
            eq_expr(produced_next_len, len_plus_one.clone()),
            eq_expr(loop_elem, len_plus_one),
        ];
        let current_invariants = vec![&slice];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_accepts_viewed_produced_triangular_sum_slice() {
        let produced = seq_v("produced");
        let produced_len = len_call(view_expr(produced.clone()));
        let loop_elem = v("i");
        let slice = eq_expr(
            mul_expr(PureExpr::View(Arc::new(v("sum"))), PureExpr::Int(2)),
            mul_expr(
                produced_len,
                add_expr(len_call(view_expr(produced.clone())), PureExpr::Int(1)),
            ),
        );
        let produced_next = push_back_expr(produced.clone(), loop_elem.clone());
        let produced_next_len = len_call(produced_next.clone());
        let bare_produced_len = len_call(produced);
        let len_plus_one = add_expr(bare_produced_len, PureExpr::Int(1));

        let mut direct_effects = HashMap::new();
        direct_effects.insert(
            "sum".to_string(),
            add_expr(PureExpr::View(Arc::new(v("sum"))), loop_elem.clone()),
        );
        direct_effects.insert("produced".to_string(), produced_next);
        let transition_facts = vec![
            eq_expr(produced_next_len, len_plus_one.clone()),
            eq_expr(loop_elem, len_plus_one),
        ];
        let current_invariants = vec![&slice];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_accepts_tuple_projected_triangular_sum_effect() {
        let produced = seq_v("produced");
        let produced_len = len_call(produced.clone());
        let loop_elem = v("i");
        let slice = eq_expr(
            mul_expr(v("sum"), PureExpr::Int(2)),
            mul_expr(
                produced_len.clone(),
                add_expr(produced_len.clone(), PureExpr::Int(1)),
            ),
        );
        let produced_next = push_back_expr(produced.clone(), loop_elem.clone());
        let produced_next_len = len_call(produced_next.clone());
        let len_plus_one = add_expr(produced_len.clone(), PureExpr::Int(1));

        let mut direct_effects = HashMap::new();
        direct_effects.insert(
            "sum".to_string(),
            tuple_get_0_expr(add_expr(v("sum"), loop_elem.clone())),
        );
        direct_effects.insert("produced".to_string(), produced_next);
        let transition_facts = vec![
            eq_expr(produced_next_len, len_plus_one.clone()),
            eq_expr(loop_elem, len_plus_one),
        ];
        let current_invariants = vec![&slice];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_accepts_tuple_projected_nonnegative_sum_effect() {
        let produced = seq_v("produced");
        let produced_len = len_call(produced);
        let loop_elem = v("i");
        let slice = PureExpr::BinOp(Arc::new(v("sum")), BinOp::Ge, Arc::new(PureExpr::Int(0)));
        let len_plus_one = add_expr(produced_len, PureExpr::Int(1));

        let mut direct_effects = HashMap::new();
        direct_effects.insert(
            "sum".to_string(),
            tuple_get_0_expr(add_expr(v("sum"), loop_elem.clone())),
        );
        let transition_facts = vec![eq_expr(loop_elem, len_plus_one)];
        let current_invariants = vec![&slice];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_accepts_scalar_eq_produced_len_step() {
        let produced = seq_v("produced");
        let produced_len = len_call(produced.clone());
        let loop_elem = v("__trust_wp_for_loop_elem_17");
        let produced_next = push_back_expr(produced, loop_elem);
        let produced_next_len = len_call(produced_next.clone());
        let slice = eq_expr(v("i"), produced_len.clone());

        let mut direct_effects = HashMap::new();
        direct_effects.insert("i".to_string(), add_expr(v("i"), PureExpr::Int(1)));
        direct_effects.insert("produced".to_string(), produced_next);
        let transition_facts = vec![eq_expr(
            produced_next_len,
            add_expr(produced_len, PureExpr::Int(1)),
        )];
        let current_invariants = vec![&slice];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_accepts_unit_increment_under_produced_len_guard() {
        let produced = seq_v("produced");
        let produced_len = len_call(produced.clone());
        let upper = v("n");
        let scalar_len = eq_expr(v("i"), produced_len.clone());
        let slice = PureExpr::BinOp(Arc::new(v("i")), BinOp::Le, Arc::new(upper.clone()));
        let loop_condition = PureExpr::BinOp(
            Arc::new(produced_len),
            BinOp::Lt,
            Arc::new(PureExpr::BinOp(
                Arc::new(upper),
                BinOp::Sub,
                Arc::new(PureExpr::Int(0)),
            )),
        );

        let mut direct_effects = HashMap::new();
        direct_effects.insert("i".to_string(), add_expr(v("i"), PureExpr::Int(1)));
        let current_invariants = vec![&scalar_len, &slice];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &[],
            Some(&loop_condition),
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_accepts_seq_iterator_structural_slice() {
        let produced = seq_v("produced");
        let iter_old_view = view_expr(v("__trust_wp_for_iter_old_17"));
        let iter_state_view = view_expr(v("__trust_wp_for_iter_state_17"));
        let iter_next = v("__trust_wp_for_iter_state_next_17");
        let iter_next_view = view_expr(iter_next.clone());
        let loop_elem = v("m");
        let slice = eq_expr(
            iter_old_view,
            concat_expr(produced.clone(), iter_state_view.clone()),
        );

        let mut direct_effects = HashMap::new();
        direct_effects.insert(
            "produced".to_string(),
            push_back_expr(produced, loop_elem.clone()),
        );
        direct_effects.insert("__trust_wp_for_iter_state_17".to_string(), iter_next);
        let transition_facts = vec![eq_expr(
            iter_state_view,
            push_front_expr(iter_next_view, loop_elem),
        )];
        let current_invariants = vec![&slice];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_accepts_seq_iterator_explicit_prime_transition() {
        let produced = seq_v("produced");
        let iter_state = seq_v("iter");
        let iter_state_view = view_expr(iter_state.clone());
        let iter_next_view = view_expr(seq_v("iter_prime"));
        let loop_elem = v("m");
        let slice = eq_expr(seq_v("original"), concat_expr(produced.clone(), iter_state));

        let mut direct_effects = HashMap::new();
        direct_effects.insert(
            "produced".to_string(),
            push_back_expr(produced, loop_elem.clone()),
        );
        let transition_facts = vec![eq_expr(
            iter_state_view,
            push_front_expr(iter_next_view, loop_elem),
        )];

        assert!(seq_iterator_structural_invariant_preserved(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
        ));
    }

    #[test]
    fn direct_preservation_rejects_seq_iterator_wrong_explicit_prime_transition() {
        let produced = seq_v("produced");
        let iter_state_view = view_expr(seq_v("iter"));
        let wrong_next_view = view_expr(seq_v("other_prime"));
        let loop_elem = v("m");
        let slice = eq_expr(
            seq_v("original"),
            concat_expr(produced.clone(), iter_state_view.clone()),
        );

        let mut direct_effects = HashMap::new();
        direct_effects.insert(
            "produced".to_string(),
            push_back_expr(produced, loop_elem.clone()),
        );
        let transition_facts = vec![eq_expr(
            iter_state_view,
            push_front_expr(wrong_next_view, loop_elem),
        )];

        assert!(!seq_iterator_structural_invariant_preserved(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
        ));
    }

    #[test]
    fn direct_preservation_accepts_range_iterator_end_slice() {
        let iter_old = v("__trust_wp_for_iter_old_17");
        let iter_state = v("__trust_wp_for_iter_state_17");
        let iter_next = v("__trust_wp_for_iter_state_next_17");
        let slice = eq_expr(end_log_expr(iter_old), end_log_expr(iter_state.clone()));

        let mut direct_effects = HashMap::new();
        direct_effects.insert(
            "__trust_wp_for_iter_state_17".to_string(),
            iter_next.clone(),
        );
        let transition_facts = vec![eq_expr(end_log_expr(iter_state), end_log_expr(iter_next))];
        let current_invariants = vec![&slice];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_accepts_range_iterator_start_slice() {
        let iter_old = v("__trust_wp_for_iter_old_17");
        let iter_state = v("__trust_wp_for_iter_state_17");
        let iter_next = v("__trust_wp_for_iter_state_next_17");
        let state_start = start_log_expr(iter_state.clone());
        let next_start = start_log_expr(iter_next.clone());
        let slice = PureExpr::BinOp(
            Arc::new(start_log_expr(iter_old)),
            BinOp::Le,
            Arc::new(state_start.clone()),
        );

        let mut direct_effects = HashMap::new();
        direct_effects.insert("__trust_wp_for_iter_state_17".to_string(), iter_next);
        let transition_facts = vec![eq_expr(next_start, add_expr(state_start, PureExpr::Int(1)))];
        let current_invariants = vec![&slice];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_accepts_range_iterator_produced_len_slice() {
        let produced = seq_v("produced");
        let iter_old = v("__trust_wp_for_iter_old_17");
        let iter_state = v("__trust_wp_for_iter_state_17");
        let iter_next = v("__trust_wp_for_iter_state_next_17");
        let loop_elem = v("__trust_wp_for_loop_elem_17");
        let produced_next = push_back_expr(produced.clone(), loop_elem);
        let produced_len = len_call(produced.clone());
        let produced_next_len = len_call(produced_next.clone());
        let state_start = start_log_expr(iter_state.clone());
        let next_start = start_log_expr(iter_next.clone());
        let old_start = start_log_expr(iter_old);
        let slice = eq_expr(
            produced_len.clone(),
            PureExpr::BinOp(
                Arc::new(state_start.clone()),
                BinOp::Sub,
                Arc::new(old_start),
            ),
        );

        let mut direct_effects = HashMap::new();
        direct_effects.insert("produced".to_string(), produced_next);
        direct_effects.insert("__trust_wp_for_iter_state_17".to_string(), iter_next);
        let transition_facts = vec![
            eq_expr(produced_next_len, add_expr(produced_len, PureExpr::Int(1))),
            eq_expr(next_start, add_expr(state_start, PureExpr::Int(1))),
        ];
        let current_invariants = vec![&slice];

        assert!(direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_rejects_range_iterator_len_slice_without_start_step() {
        let produced = seq_v("produced");
        let iter_old = v("__trust_wp_for_iter_old_17");
        let iter_state = v("__trust_wp_for_iter_state_17");
        let iter_next = v("__trust_wp_for_iter_state_next_17");
        let loop_elem = v("__trust_wp_for_loop_elem_17");
        let produced_next = push_back_expr(produced.clone(), loop_elem);
        let produced_len = len_call(produced.clone());
        let produced_next_len = len_call(produced_next.clone());
        let state_start = start_log_expr(iter_state);
        let old_start = start_log_expr(iter_old);
        let slice = eq_expr(
            produced_len.clone(),
            PureExpr::BinOp(Arc::new(state_start), BinOp::Sub, Arc::new(old_start)),
        );

        let mut direct_effects = HashMap::new();
        direct_effects.insert("produced".to_string(), produced_next);
        direct_effects.insert("__trust_wp_for_iter_state_17".to_string(), iter_next);
        let transition_facts = vec![eq_expr(
            produced_next_len,
            add_expr(produced_len, PureExpr::Int(1)),
        )];
        let current_invariants = vec![&slice];

        assert!(!direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_rejects_seq_iterator_structural_slice_without_matching_transition() {
        let produced = seq_v("produced");
        let iter_old_view = view_expr(v("__trust_wp_for_iter_old_17"));
        let iter_state_view = view_expr(v("__trust_wp_for_iter_state_17"));
        let iter_next = v("__trust_wp_for_iter_state_next_17");
        let iter_next_view = view_expr(iter_next.clone());
        let loop_elem = v("m");
        let slice = eq_expr(
            iter_old_view,
            concat_expr(produced.clone(), iter_state_view.clone()),
        );

        let mut direct_effects = HashMap::new();
        direct_effects.insert("produced".to_string(), push_back_expr(produced, loop_elem));
        direct_effects.insert("__trust_wp_for_iter_state_17".to_string(), iter_next);
        let transition_facts = vec![eq_expr(
            iter_state_view,
            push_front_expr(iter_next_view, v("other_m")),
        )];
        let current_invariants = vec![&slice];

        assert!(!direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &HashMap::new(),
            &transition_facts,
            None,
            &current_invariants,
            &[],
            &[],
        ));
    }

    #[test]
    fn direct_preservation_ignores_empty_arg_concat_shape() {
        let slice = eq_expr(
            v("stable"),
            PureExpr::MethodCall {
                receiver: Arc::new(seq_v("produced")),
                method: "concat".to_string(),
                args: vec![],
            },
        );

        assert!(!seq_iterator_structural_invariant_preserved(
            &slice,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &[],
        ));
    }

    // --- 100doors: range-iterator length frame in the STABLE structural set. ---
    // These tests pin both the flip mechanism (the slice is now accepted by the
    // stable trusted fast-path) and its soundness boundary (the fast-path must
    // NOT accept the slice when the body's step transition facts are absent or
    // wrong — otherwise the trusted "verified-without-solving" path would
    // over-claim, which is exactly the should_fail false-accept risk).

    /// Build the exact 100doors outer-loop iterator slice
    /// `len(produced) == start_log(state) - start_log(old)`, its `produced`
    /// push_back effect, the next range value effect, and the two step
    /// transition facts. Returns (slice, direct_effects, transition_facts).
    fn doors_range_len_fixture() -> (PureExpr, HashMap<String, PureExpr>, Vec<PureExpr>) {
        let produced = seq_v("produced");
        let state = v("state");
        let old = v("old");
        let state_next = v("state_next");

        // slice: len(produced) == start_log(state) - start_log(old)
        let slice = eq_expr(
            len_call(produced.clone()),
            PureExpr::BinOp(
                Arc::new(start_log_expr(state.clone())),
                BinOp::Sub,
                Arc::new(start_log_expr(old.clone())),
            ),
        );

        let mut direct_effects = HashMap::new();
        // produced' = push_back(produced, elem)
        direct_effects.insert(
            "produced".to_string(),
            push_back_expr(produced.clone(), v("elem")),
        );
        // state advances to state_next; range_accessor_next_expr resolves
        // start_log(state) -> start_log(direct_effects["state"]).
        direct_effects.insert("state".to_string(), state_next.clone());

        let transition_facts = vec![
            // len(push_back(produced, elem)) == len(produced) + 1
            eq_expr(
                len_call(push_back_expr(produced.clone(), v("elem"))),
                add_expr(len_call(produced.clone()), PureExpr::Int(1)),
            ),
            // start_log(state_next) == start_log(state) + 1
            eq_expr(
                start_log_expr(state_next),
                add_expr(start_log_expr(state), PureExpr::Int(1)),
            ),
        ];

        (slice, direct_effects, transition_facts)
    }

    #[test]
    fn stable_set_accepts_range_iterator_produced_len_frame() {
        let (slice, direct_effects, transition_facts) = doors_range_len_fixture();
        let invariants = vec![&slice];
        // The stable trusted fast-path (used by the no-havoc structural discharge)
        // must accept this slice; this is what flips 100doors.
        assert!(stable_direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &transition_facts,
            &invariants,
        ));
        // And the dedicated check itself must agree.
        assert!(range_produced_len_structural_slice_preserved(
            &slice,
            &direct_effects,
            &transition_facts,
        ));
    }

    #[test]
    fn stable_set_rejects_range_frame_without_start_step_fact() {
        // SOUNDNESS GUARD: drop the `start_log(next) == start_log(state) + 1`
        // step fact. Without it the body could advance the range start by any
        // amount, so `len(produced) == start - old` is NOT structurally
        // preserved. The trusted fast-path MUST refuse (forcing a real solve).
        let (slice, direct_effects, mut transition_facts) = doors_range_len_fixture();
        // keep only the produced-length fact, drop the start-step fact.
        transition_facts.truncate(1);
        let invariants = vec![&slice];
        assert!(!stable_direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &transition_facts,
            &invariants,
        ));
        assert!(!range_produced_len_structural_slice_preserved(
            &slice,
            &direct_effects,
            &transition_facts,
        ));
    }

    #[test]
    fn stable_set_rejects_range_frame_without_produced_push_back() {
        // SOUNDNESS GUARD: if `produced` is not advanced by a `push_back` (e.g.
        // it is reassigned wholesale, or grows by more than one), the length
        // step is not +1 and the invariant is not structurally preserved. The
        // trusted fast-path MUST refuse.
        let (slice, mut direct_effects, transition_facts) = doors_range_len_fixture();
        // Replace the push_back effect with a wholesale reassignment.
        direct_effects.insert("produced".to_string(), seq_v("something_else"));
        let invariants = vec![&slice];
        assert!(!stable_direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &transition_facts,
            &invariants,
        ));
        assert!(!range_produced_len_structural_slice_preserved(
            &slice,
            &direct_effects,
            &transition_facts,
        ));
    }

    #[test]
    fn stable_set_rejects_wrong_start_step_increment() {
        // SOUNDNESS GUARD: a `+2` start step (or any non-`+1`) must not be
        // accepted as a length-preserving range frame.
        let (slice, direct_effects, _) = doors_range_len_fixture();
        let produced = seq_v("produced");
        let transition_facts = vec![
            eq_expr(
                len_call(push_back_expr(produced.clone(), v("elem"))),
                add_expr(len_call(produced), PureExpr::Int(1)),
            ),
            // start_log(state_next) == start_log(state) + 2  (WRONG)
            eq_expr(
                start_log_expr(v("state_next")),
                add_expr(start_log_expr(v("state")), PureExpr::Int(2)),
            ),
        ];
        let invariants = vec![&slice];
        assert!(!stable_direct_preservation_facts_prove_slice(
            &slice,
            &direct_effects,
            &HashMap::new(),
            &transition_facts,
            &invariants,
        ));
    }
}
