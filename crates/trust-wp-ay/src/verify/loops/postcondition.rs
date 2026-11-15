// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Postcondition verification for loops.
//!
//! Implements: invariant ∧ ¬condition => postcondition[result/return_expr]

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
    time::Instant,
};

use tracing::debug;
use trust_wp_core::{
    formula::{BinOp, ExprSort, PureExpr},
    logic::LogicFnDef,
};

use super::{
    super::{
        assert_eager_negated_existential_instantiations, assert_standard_axioms,
        axiom_free_solve_with_sat, demote_if_unsound, encode_and_assert_negated_postconditions,
        obligation_slices,
        setup::{bootstrap_encoder, BootstrapRequest, ExprSlice, LogicFnInput, TypeInvariantInput},
        AxiomFreeOutcome, VerificationOutcome, VerificationResult,
    },
    encoder_setup::{
        assert_condition_facts, assert_loop_current_chain_alias_constraints,
        collect_loop_sort_plan, encode_and_assert_requires, prove_empty_postcondition_outcome,
        solve_scoped_loop_obligation_with_base_recheck_outcome, OutcomeContinuation,
    },
    expr_helpers::{collect_final_var_names, expr_references_any_var, strip_scalar_views},
    prime_substitutions::{build_prime_substitutions, sort_to_expr_sort},
    LoopVcBase, PostconditionInputs,
};
use crate::{
    encoder::{
        infer_expr_sort,
        sort_context::{effective_expr_annotation, DerivedKind},
        unsoundness, AYEncoder,
    },
    error::EncodingError,
};

/// Verify postcondition: invariant ∧ ¬condition => postcondition[result/return_expr]
///
/// When `return_expr` is `Some`, substitutes `result` with the return expression
/// in the postcondition before encoding (e.g., `result == n` becomes `i == n`
/// when `return_expr = Var("i")`). This avoids adding an equality assertion
/// to the SMT context, which would trigger ay's equality-splitting limitation
/// in QF_LIA (#622).
#[allow(clippy::too_many_lines)] // Postcondition encoding keeps substitution + exit-guard logic in one path.
pub(in crate::verify::loops) fn verify_postcondition(
    base: &LoopVcBase<'_>,
    inputs: PostconditionInputs<'_>,
) -> Result<VerificationResult, EncodingError> {
    Ok(verify_postcondition_outcome(base, inputs)?.result)
}

pub(in crate::verify::loops) fn verify_postcondition_outcome(
    base: &LoopVcBase<'_>,
    inputs: PostconditionInputs<'_>,
) -> Result<VerificationOutcome, EncodingError> {
    let invariants = base.invariants;
    let loop_condition = base.loop_condition;
    let condition_is_body_break = base.condition_is_body_break;
    let modified_vars = base.modified_vars;
    let effects = base.effects;
    let config = base.config;
    let debug_timing = std::env::var("TRUST_WP_LOOP_DEBUG_TIMING").is_ok();
    let phase_start = Instant::now();
    let mut last_phase = phase_start;

    if inputs.ensures.is_empty() {
        return prove_empty_postcondition_outcome(config);
    }
    // Defensive guard: reject residual Old(...) that the driver should have
    // rewritten (#2095). Old(Deref(...)) is the allowed mutable-borrow form.
    for ens in inputs.ensures {
        if let Some(var) = find_residual_non_deref_old(ens) {
            return Err(EncodingError::Unsupported {
                message: format!(
                    "residual old({var}) in loop postcondition — driver should have rewritten this"
                ),
                span: None,
                contract_text: None,
            });
        }
    }

    // Substitute `result` with the return expression in postconditions (#622).
    // Instead of asserting `result = return_expr` as an SMT equality (which
    // triggers ay's disequality-split loop for transitive equality), we replace
    // `Var("result")` with `return_expr` in the ensures expressions. This
    // produces an equivalent verification condition with fewer SMT variables.
    //
    // For body-break loops, the return expression must be primed before
    // substitution. The loop body executes before the break condition is
    // tested, so `return i` after `loop { i += 1; if cond { break } }`
    // returns post-body `i`, not pre-body `i`. Without priming, the
    // postcondition VC uses the unprimed (pre-body) value, making
    // postconditions like `result == n` unprovable. (#1399)
    let substituted_ensures: Vec<PureExpr>;
    let effective_ensures = if let Some(ret_expr) = inputs.return_expr {
        let primed_ret_expr = if condition_is_body_break && loop_condition.is_some() {
            let m_set: HashSet<&str> = modified_vars.iter().copied().collect();
            if expr_references_any_var(ret_expr, &m_set) {
                // Build PureExpr-level prime map: var → Var("var_prime", sort).
                // The SMT declarations for these primed variables are created
                // later by build_prime_substitutions; here we only need the
                // name mapping so that effective_ensures references the correct
                // (post-body) variable names. Propagate ExprSort from body_effect
                // so register_sort_hints correctly identifies Bool/Seq primed vars.
                let prime_name_map: HashMap<String, PureExpr> = modified_vars
                    .iter()
                    .map(|v| {
                        let expr_sort = effects
                            .direct
                            .get(*v)
                            .and_then(|e| sort_to_expr_sort(&infer_expr_sort(e)));
                        (
                            (*v).to_string(),
                            PureExpr::Var(DerivedKind::Prime.format_name(v), expr_sort),
                        )
                    })
                    .collect();
                ret_expr.substitute_filtered(&m_set, &prime_name_map)
            } else {
                ret_expr.clone()
            }
        } else {
            ret_expr.clone()
        };
        let mut subs = HashMap::new();
        subs.insert("result".to_string(), primed_ret_expr.clone());
        // Also map "*result" → return_expr so that Deref(Var("result"))
        // (e.g., `*result` in postconditions of Ghost-returning functions)
        // substitutes directly instead of creating an unconstrained
        // "y_current" variable. The substitute() method checks for
        // "*result" when it encounters Deref(Var("result")). (#1581)
        subs.insert("*result".to_string(), primed_ret_expr);
        substituted_ensures = inputs.ensures.iter().map(|e| e.substitute(&subs)).collect();
        &substituted_ensures
    } else if condition_is_body_break && loop_condition.is_some() {
        // Body-break without return_expr: the ensures reference the loop
        // variables directly (e.g., `i == n`). For body-break, the values
        // at loop exit are post-body (primed), so substitute modified vars
        // with their primed names in the ensures. (#2698)
        //
        // Without this, the ensures reference pre-body `i` while the exit
        // condition references post-body `i'`, creating a disconnect that
        // prevents postcondition proofs. With priming, ensures `i == n`
        // becomes `i' == n`, which combined with exit_cond `i' >= n` and
        // invariant `i <= n` and body effect `i' = i + 1`, gives:
        // `i' >= n AND i <= n AND i' = i + 1 AND NOT(i' == n)` → UNSAT.
        let m_set: HashSet<&str> = modified_vars.iter().copied().collect();
        let prime_name_map: HashMap<String, PureExpr> = modified_vars
            .iter()
            .map(|v| {
                let expr_sort = effects
                    .direct
                    .get(*v)
                    .and_then(|e| sort_to_expr_sort(&infer_expr_sort(e)));
                (
                    (*v).to_string(),
                    PureExpr::Var(DerivedKind::Prime.format_name(v), expr_sort),
                )
            })
            .collect();
        substituted_ensures = inputs
            .ensures
            .iter()
            .map(|e| e.substitute_filtered(&m_set, &prime_name_map))
            .collect();
        &substituted_ensures
    } else {
        inputs.ensures
    };

    // Preserve loop-entry values for variables that are not modified by the loop body.
    // Without this frame, postcondition VCs can freely assign unconstrained values
    // to untouched locals (e.g., `x` in `unused_in_loop`), producing false failures.
    let modified_set: HashSet<&str> = modified_vars.iter().copied().collect();
    // Uses NamedBindingValue.lhs_var() to preserve MIR-derived sort. (#2053 Slice B)
    let frame_assignments: Vec<PureExpr> = inputs
        .pre_loop_assignments
        .iter()
        .filter(|(name, binding)| {
            // Skip variables whose name is modified by the loop body.
            if modified_set.contains(name.as_str()) {
                return false;
            }
            // Skip variables whose value expression references any modified
            // variable. Without this, `let n = v.len()` where `v` is modified
            // would produce an unsound frame constraint `n == v.len()`
            // (asserting post-loop v.len() equals pre-loop v.len()). (#2158)
            !expr_references_any_var(&binding.value, &modified_set)
        })
        .map(|(name, binding)| {
            PureExpr::BinOp(
                Arc::new(binding.lhs_var(name)),
                BinOp::Eq,
                Arc::new(binding.value.clone()),
            )
        })
        .collect();
    let canonical_post_extra_facts: Vec<PureExpr> = inputs
        .post_extra_facts
        .iter()
        .map(super::expr_helpers::canonicalize_fmap_new)
        .collect();
    let fmap_len_fact_sources: Vec<PureExpr> = frame_assignments
        .iter()
        .chain(canonical_post_extra_facts.iter())
        .cloned()
        .collect();
    let mut post_extra_facts = canonical_post_extra_facts;
    for fact in super::expr_helpers::derive_fmap_len_facts(&fmap_len_fact_sources) {
        if !post_extra_facts.contains(&fact) {
            post_extra_facts.push(fact);
        }
    }

    let cond_vec: Vec<PureExpr> = loop_condition.into_iter().cloned().collect();
    let effect_values: Vec<PureExpr> = if condition_is_body_break && loop_condition.is_some() {
        effects.direct.values().cloned().collect()
    } else {
        Vec::new()
    };
    let deref_effect_values: Vec<PureExpr> = if condition_is_body_break && loop_condition.is_some()
    {
        effects.deref.values().cloned().collect()
    } else {
        Vec::new()
    };
    let double_deref_effect_values: Vec<PureExpr> =
        if condition_is_body_break && loop_condition.is_some() {
            effects.double_deref.values().cloned().collect()
        } else {
            Vec::new()
        };
    // Build ExprSlice arrays for bootstrap_encoder. Formula slices get Bool
    // sort hints; value slices get sort hints only. (#2195)
    let mut bootstrap_slices: Vec<ExprSlice<'_>> = vec![
        ExprSlice::formula(invariants),
        ExprSlice::formula(effective_ensures),
        ExprSlice::formula(&frame_assignments),
        ExprSlice::formula(inputs.requires),
    ];
    if !post_extra_facts.is_empty() {
        bootstrap_slices.push(ExprSlice::formula(&post_extra_facts));
    }
    if !cond_vec.is_empty() {
        bootstrap_slices.push(ExprSlice::formula(&cond_vec));
    }
    if !effect_values.is_empty() {
        bootstrap_slices.push(ExprSlice::value(&effect_values));
    }
    if !deref_effect_values.is_empty() {
        bootstrap_slices.push(ExprSlice::value(&deref_effect_values));
    }
    if !double_deref_effect_values.is_empty() {
        bootstrap_slices.push(ExprSlice::value(&double_deref_effect_values));
    }
    let mut encoder = bootstrap_encoder(BootstrapRequest {
        expr_slices: &bootstrap_slices,
        result_postconditions: Some(effective_ensures),
        result_expr: inputs.return_expr,
        logic_fns: config.logic_fns.map(LogicFnInput::PrefilteredGroundOnly),
        mode_overrides: config.mode_overrides,
        type_invariants: config.type_invariants.map(TypeInvariantInput::Prefiltered),
        track: config.track.unwrap_or_default(),
        timeout: config.timeout,
        type_constants: config.type_constants,
        closure_captures: None,
        adt_decls: config.adt_decls,
        adt_field_ranges: config.adt_field_ranges,
    })?;
    // Post-bootstrap snapshot: absorb SortFallbackToIntFromLogicFn increments
    // from sort hint collection during bootstrap. (#2062)
    let post_bootstrap = unsoundness::snapshot();
    if debug_timing {
        let now = Instant::now();
        debug!(
            "[loop-timing/post] encoder_setup: {:?} (total {:?})",
            now.duration_since(last_phase),
            now.duration_since(phase_start)
        );
        last_phase = now;
    }

    // Compute function-level preconditions that reference only unmodified
    // parameters (e.g., unsigned nonneg `x >= 0`). Requires that mention
    // loop-modified variables must be excluded — they describe pre-loop state
    // and would unsoundly constrain the post-loop value. (#1295, #904)
    // Skolemize existentials containing postcondition_mut (#1364).
    let unmodified_requires: Vec<PureExpr> = inputs
        .requires
        .iter()
        .filter(|req| !expr_references_any_var(req, &modified_set))
        .cloned()
        .collect();
    encode_and_assert_requires(&mut encoder, &unmodified_requires)?;

    let ground_hashmap_list_universals =
        hashmap_list_loop_forall_grounding_enabled(config, invariants);

    // Assert invariant.
    // Strip scalar View wrappers to avoid creating intermediate `_view`
    // SMT variables that can cause ay-dpll's LIA bound-tightening to
    // diverge on otherwise-trivial postcondition VCs. (#1581)
    // Pre-synthesize triggers for triggerless foralls so that ay-dpll's
    // E-matching fires reliably on quantified invariant assumptions. (#2116)
    for inv in invariants {
        if ground_hashmap_list_universals && matches!(inv, PureExpr::Forall { .. }) {
            continue;
        }
        let normalized = super::invariant_transforms::normalize_fmap_get_biconditional(inv);
        let triggered = super::invariant_transforms::inject_forall_triggers(&normalized);
        let simplified = strip_scalar_views(&triggered);
        let term = encoder.encode_pure(&simplified)?;
        encoder.assert_term(term);
    }

    // Assert frame equalities for variables untouched by the loop.
    for assignment in &frame_assignments {
        let term = encoder.encode_pure(assignment)?;
        encoder.assert_term(term);
    }

    // Off-loop general recursive-logic-fn defining-equation unfolder on the
    // LOOP-postcondition premises (#recursive-unfolder, #route-100 r7).
    // Recursive fns get no global defining axiom, so invariants like
    // `ix@ < l.len()` leave `logic_len` fully uninterpreted here — the decoded
    // binary_search_list len loop_postcondition counterexample exploits exactly
    // that (its validated sat model picks len_logic(l)!=0 on the loop-exit
    // path). Seed the case-lifted bounded defining equations from the
    // invariants + requires. SOUND: each fact is a true per-branch instance of
    // the fn's own definition (coercing facts dropped); env-gated with the rest
    // of the unfolder rollout.
    if std::env::var_os("TRUST_WP_OFFLOOP").is_some() {
        if let Some(logic_fns) = config.logic_fns {
            let mut premise_exprs: Vec<PureExpr> = invariants.to_vec();
            premise_exprs.extend(unmodified_requires.iter().cloned());
            super::recursive_unfolding::assert_offloop_recursive_defining_unfoldings(
                &mut encoder,
                &premise_exprs,
                Some(logic_fns),
            )?;
        }
    }
    if debug_timing {
        let now = Instant::now();
        debug!(
            "[loop-timing/post] invariants+requires+frame: {:?} (total {:?})",
            now.duration_since(last_phase),
            now.duration_since(phase_start)
        );
        last_phase = now;
    }

    let mut prime_substitutions = HashMap::new();
    if condition_is_body_break && loop_condition.is_some() {
        // For body-break loops, the exit condition is checked against post-body
        // state, so we need the same prime substitution map used in preservation.
        let sort_plan = collect_loop_sort_plan(&mut encoder, modified_vars, effects.direct);
        sort_plan.apply(&mut encoder)?;
        prime_substitutions =
            build_prime_substitutions(&mut encoder, &sort_plan, modified_vars, effects)?;
    }

    // Assert loop exit condition.
    //
    // Both header-while and body-break store the CONTINUATION condition
    // (find_body_break_condition negates the break predicate to produce
    // the continuation form). At loop exit, continuation is FALSE, so we
    // assert NOT(condition) — giving: invariant AND NOT(cond) => ensures.
    //
    // For body-break loops the condition is checked against post-body
    // (primed) state, so we substitute modified vars with their primed
    // names before negation. (#2698)
    if let Some(cond) = loop_condition {
        let effective_cond = if condition_is_body_break {
            // Prime the continuation condition for body-break: substitute
            // modified vars with their post-body primed equivalents.
            let modified_set: HashSet<&str> = modified_vars.iter().copied().collect();
            cond.substitute_filtered(&modified_set, &prime_substitutions)
        } else {
            cond.clone()
        };
        let cond_term = encoder.encode_pure(&effective_cond)?;
        let cond_term = encoder.coerce_bool_operand(cond_term);
        // At exit, continuation is FALSE → assert NOT(cond).
        let negated_cond = encoder.solver_mut().not(cond_term);
        encoder.assert_term(negated_cond);
    }
    assert_condition_facts(&mut encoder, config)?;
    if debug_timing {
        let now = Instant::now();
        debug!(
            "[loop-timing/post] exit_condition: {:?} (total {:?})",
            now.duration_since(last_phase),
            now.duration_since(phase_start)
        );
        let _ = now; // final phase; keep consistent pattern for future phases
    }

    // Assert extra postcondition facts (e.g., iterator completion: produced == input).
    // For Creusot for-loops, when the iterator is exhausted, `produced` contains
    // all elements of the original input sequence. (#1581)
    for fact in &post_extra_facts {
        let term = encoder.encode_pure(fact)?;
        encoder.assert_term(term);
    }

    // Assert borrow resolution for mutable reference parameters. (#1295)
    //
    // When the loop body writes through a dereference (`*x = expr`), the
    // postcondition may reference the final value of the mutable borrow via
    // `^x` (encoded as `x_final`). At function exit the borrow resolves,
    // meaning the prophecy variable equals the current value:
    //   x_final == x_current
    //
    // Without this constraint, `x_final` is a free variable in the
    // postcondition VC and the solver trivially finds counterexamples.
    //
    // Contract: caller must exclude vars whose pointee is mutated after loop
    // exit (for example in post-loop blocks before return). For those vars,
    // loop-exit `x_current` is not function-exit state, so this loop-local
    // resolution must be deferred to function-level verification. (#1823)
    for (var, deref_effect_expr) in effects.deref {
        let current_name = DerivedKind::Current.format_name(var);
        let final_name = DerivedKind::Final.format_name(var);
        let deref_sort = if encoder.is_bool_var(var) {
            ay_dpll::api::Sort::Bool
        } else {
            // Context-aware inference for deref effects. (#1965)
            encoder.infer_expr_sort_with_context(deref_effect_expr, None)
        };
        let current_var = encoder.get_or_declare_var(&current_name, deref_sort.clone())?;
        let final_var = encoder.get_or_declare_var(&final_name, deref_sort.clone())?;
        encoder.assert_eq(final_var, current_var);
    }

    // Phase 4 (#759): Borrow resolution for unchanged mutable reference parameters.
    //
    // When the postcondition references `^y` (Final(Var("y"))) for a mutable
    // reference parameter `y` that is NOT modified by the loop body, the borrow
    // resolves at function exit to the unchanged current value:
    //   y_final == y_current
    //
    // The existing loop above handles variables IN deref_body_effect (modified
    // via `*x = expr`). This block handles the complementary case: mut refs
    // whose prophecy appears in the postcondition but whose pointee is untouched
    // by the loop. Without this, `y_final` is a free SMT variable and the solver
    // trivially produces counterexamples for postconditions like `^y == 42`.
    //
    // Guard: only resolve variables NOT in modified_vars and NOT already in
    // deref_body_effect (those are handled above). Variables in modified_vars
    // may have been reassigned (e.g., `y = other_ref`) so their prophecy
    // resolution is different.
    let final_var_names = collect_final_var_names(effective_ensures);
    let final_var_sorts = collect_final_var_inner_sorts(effective_ensures);
    for var_name in &final_var_names {
        // Skip variables already resolved by the deref_body_effect loop above
        if effects.deref.contains_key(var_name.as_str()) {
            continue;
        }
        // Skip variables modified by the loop body (reassigned, not just deref-written)
        if modified_set.contains(var_name.as_str()) {
            continue;
        }
        let current_name = DerivedKind::Current.format_name(var_name);
        let final_name = DerivedKind::Final.format_name(var_name);
        let sort = if let Some(expr_sort) = final_var_sorts.get(var_name) {
            encoder.sort_from_expr_sort(expr_sort.clone())
        } else if encoder.is_bool_var(var_name)
            || encoder.is_bool_var(&current_name)
            || encoder.is_bool_var(&final_name)
        {
            ay_dpll::api::Sort::Bool
        } else {
            encoder.resolve_var_sort_or_int(&current_name)
        };
        let current_var = encoder.get_or_declare_var(&current_name, sort.clone())?;
        let final_var = encoder.get_or_declare_var(&final_name, sort.clone())?;
        if sort == ay_dpll::api::Sort::Bool {
            let resolution = encoder.eq_or_iff(final_var, current_var, &sort);
            encoder.assert_term(resolution);
        } else {
            encoder.assert_eq(final_var, current_var);
        }
    }

    // Early vacuity guard (#2440): check if invariants alone are contradictory
    // using a separate encoder. If so, any proof is vacuous.
    {
        let base_exprs: Vec<PureExpr> = invariants.to_vec();
        if super::encoder_setup::is_base_vacuous(&base_exprs) {
            return Ok(VerificationOutcome::without_provenance(demote_if_unsound(
                &post_bootstrap,
                VerificationResult::Unknown(crate::verify::UnknownReason::SolverMessage(
                    crate::verify::solver_tail::VACUOUS_PROOF_MESSAGE.to_string(),
                )),
            )));
        }
    }

    // --- Per-slice obligation verification via push/pop (#2286) ---
    //
    // Each ensures clause is checked independently against the shared base
    // context. This matches the function and mut_borrow verification paths,
    // preventing a quantifier-heavy postcondition from making sibling
    // scalar obligations harder to prove.
    let slices = obligation_slices::split_ensures(effective_ensures);
    let mut slice_results: Vec<obligation_slices::SliceOutcome> = Vec::with_capacity(slices.len());
    // Snapshot all scope-sensitive assert-once state before the slice loop.
    // Restoring per-iteration prevents cross-slice assertion loss from stale
    // dedup entries left by popped scopes. (#2618)
    let dedup_baseline = encoder.dedup_snapshot();

    for slice in &slices {
        encoder.restore_dedup(dedup_baseline.clone());
        // A narrowly certified Seq lane with an explicit non-vacuity witness:
        // every premise and the goal is an equality between Seq variables
        // (viewed directly or through `reverse`), and the goal follows by
        // equality congruence. Assigning every variable the empty sequence
        // satisfies the complete base, so this cannot hide a contradictory
        // premise set. This closes the common iterator-completion theorem
        // without depending on AY's quantified Seq model-validation path.
        let seq_reverse_empty_witness_lane = loop_condition.is_none()
            && !condition_is_body_break
            && modified_vars.is_empty()
            && effects.direct.is_empty()
            && effects.deref.is_empty()
            && effects.double_deref.is_empty()
            && inputs.return_expr.is_none()
            && inputs.pre_loop_assignments.is_empty()
            && inputs.requires.is_empty()
            && config
                .type_invariants
                .is_none_or(|definitions| definitions.is_empty())
            && config
                .logic_fns
                .is_none_or(|definitions| definitions.is_empty())
            && config
                .mode_overrides
                .is_none_or(|overrides| overrides.is_empty())
            && config.type_constants.is_none_or(HashMap::is_empty)
            && config.transition_facts.is_empty()
            && config.bridge_facts.is_empty()
            && config.adt_decls.is_none()
            && config.adt_field_ranges.is_none()
            && seq_reverse_equality_congruence_has_empty_witness(
                slice.ensure.as_ref(),
                invariants,
                &post_extra_facts,
            );
        if seq_reverse_empty_witness_lane {
            let outcome = super::encoder_setup::prove_structural_loop_goal_outcome(
                config,
                "__trust_wp_loop_postcondition_seq_reverse_structural",
            )?;
            slice_results.push(obligation_slices::SliceOutcome {
                index: slice.index,
                outcome: demote_outcome_if_unsound(&post_bootstrap, outcome),
            });
            continue;
        }
        let cursor_specialization_lane = effects.direct.is_empty()
            && effects.deref.is_empty()
            && effects.double_deref.is_empty()
            && inputs.return_expr.is_none()
            && inputs.pre_loop_assignments.is_empty()
            && inputs.requires.is_empty()
            && post_extra_facts.is_empty()
            && config
                .type_invariants
                .is_none_or(|definitions| definitions.is_empty())
            && config
                .logic_fns
                .is_none_or(|definitions| definitions.is_empty())
            && config
                .mode_overrides
                .is_none_or(|overrides| overrides.is_empty())
            && config.type_constants.is_none_or(HashMap::is_empty)
            && config.transition_facts.is_empty()
            && config.bridge_facts.is_empty()
            && config.adt_decls.is_none()
            && config.adt_field_ranges.is_none()
            && list_index_cursor_postcondition_follows_directly(
                slice.ensure.as_ref(),
                invariants,
                loop_condition,
                condition_is_body_break,
            );
        if cursor_specialization_lane {
            let outcome = super::encoder_setup::prove_structural_loop_goal_outcome(
                config,
                "__trust_wp_loop_postcondition_list_index_cursor_structural",
            )?;
            slice_results.push(obligation_slices::SliceOutcome {
                index: slice.index,
                outcome: demote_outcome_if_unsound(&post_bootstrap, outcome),
            });
            continue;
        }
        if list_reversal_list_postcondition_follows_directly(
            slice.ensure.as_ref(),
            invariants,
            loop_condition,
            condition_is_body_break,
            config.logic_fns,
        ) {
            let outcome = super::encoder_setup::prove_structural_loop_goal_outcome(
                config,
                "__trust_wp_loop_postcondition_list_reversal_structural",
            )?;
            slice_results.push(obligation_slices::SliceOutcome {
                index: slice.index,
                outcome: demote_outcome_if_unsound(&post_bootstrap, outcome),
            });
            continue;
        }
        let rescue_unaxiomatized_user_logic_sat =
            loop_postcondition_has_unregistered_user_logic_call(
                slice.ensure.as_ref(),
                config.logic_fns,
            );
        let mut axiom_free_counterexample = None;
        let mut unaxiomatized_user_logic_without_standard_demand = false;
        let unchanged_mut_ref_fact = unchanged_mut_ref_postcondition_follows_requires(
            slice.ensure.as_ref(),
            &unmodified_requires,
            &modified_set,
            effects.deref,
        )
        .then(|| slice.ensure.as_ref().clone());
        let equality_congruence_fact =
            equality_congruence_consequence(slice.ensure.as_ref(), invariants, &post_extra_facts);
        let outcome =
            match solve_scoped_loop_obligation_with_base_recheck_outcome(&mut encoder, |encoder| {
                assert_eager_negated_existential_instantiations(
                    encoder,
                    effective_ensures,
                    invariants,
                    &[],
                )?;

                if let Some(fact) = &unchanged_mut_ref_fact {
                    let term = encoder.encode_pure(fact)?;
                    encoder.assert_term(term);
                }

                // Materialize a quantifier-free equality consequence before
                // asking the solver to negate the goal. For example:
                //
                //   result@ == produced@.reverse()
                //   produced@ == input@
                //   --------------------------------
                //   result@ == input@.reverse()
                //
                // This is ordinary equality congruence, not a collection
                // axiom. Making the consequence explicit keeps AY from
                // entering its quantified Seq fallback for a theorem that
                // needs no Seq semantics. The recognizer below is fail-closed
                // around binders and does not rewrite beneath `old(...)`.
                if let Some(fact) = &equality_congruence_fact {
                    let term = encoder.encode_pure(fact)?;
                    encoder.assert_term(term);
                }

                // Negate this postcondition slice first so that encoding creates any
                // `_current`-suffixed variables needed by the alias pass. (#1302, #1441)
                let _asserted = encode_and_assert_negated_postconditions(
                    encoder,
                    std::slice::from_ref(slice.ensure.as_ref()),
                    config.logic_fns,
                    None,
                )?;

                // Bounded structural-induction lemma for recursive-datatype
                // `get`/`len` logic fns: when this postcondition slice needs
                // `forall i. 0<=i<len(l) ==> is-Some(get(l,i))` (the "every
                // in-range index is defined" fact), discharge it via the
                // datatype's induction principle (base + step sub-proofs) and
                // assert the proven, E-matchable conclusion. SOUND — emits only
                // a genuine theorem, inert otherwise. (#all_zero Obl1)
                encoder.emit_bounded_get_some_structural_induction(
                    std::slice::from_ref(slice.ensure.as_ref()),
                    config.logic_fns,
                    config.mode_overrides,
                );

                if ground_hashmap_list_universals {
                    assert_universal_skolem_instances_for_slice(
                        encoder,
                        invariants,
                        slice.ensure.as_ref(),
                    )?;
                }

                // Now that all variables exist, assert _current-chain aliases.
                // Postconditions may introduce new `_current` variables from nested
                // derefs (e.g., x_current_current). (#1302, #2286)
                assert_loop_current_chain_alias_constraints(encoder)?;

                encoder.mark_postcondition_logic_fn_symbols(effective_ensures);
                encoder.mark_postcondition_logic_fn_symbols(invariants);
                encoder.mark_postcondition_logic_fn_symbols(&unmodified_requires);
                encoder.mark_postcondition_logic_fn_symbols(&post_extra_facts);

                // Pre-assert Seq ground instances before axiom probe. (#2323)
                if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia) {
                    encoder.assert_seq_ground_instances(
                        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
                    );
                }

                // Two-phase axiom solving (#2116): try without axioms first.
                // Skip for QF_LIA: pure arithmetic obligations don't use the
                // closure/tuple/ADT UF symbols covered by these axioms. (#1573, #1924)
                if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia) {
                    let no_pending_standard_axiom_demand =
                        !loop_has_pending_standard_axiom_demand(encoder, invariants);
                    if rescue_unaxiomatized_user_logic_sat && no_pending_standard_axiom_demand {
                        unaxiomatized_user_logic_without_standard_demand = true;
                    }

                    let mut axiom_free_proved = false;
                    match axiom_free_solve_with_sat(encoder) {
                        AxiomFreeOutcome::Unsat => {
                            axiom_free_proved = true;
                        }
                        AxiomFreeOutcome::Sat(counterexample) => {
                            if rescue_unaxiomatized_user_logic_sat
                                && no_pending_standard_axiom_demand
                            {
                                axiom_free_counterexample = Some(counterexample);
                            }
                        }
                        AxiomFreeOutcome::Inconclusive => {}
                    }

                    if !axiom_free_proved {
                        // Phase 2: axioms needed. Pass invariants as the "requires"
                        // equivalent so eager instantiation (fn_mut_once, Skolemization)
                        // can find ground closure-spec terms. ay v0.2.0 E-matching
                        // needs these eagerly instantiated.
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

        let mut outcome = outcome;
        if let VerificationResult::Unknown(ref reason) = outcome.result {
            if let Some(counterexample) = axiom_free_counterexample {
                if loop_should_rescue_with_axiom_free_sat(reason) {
                    outcome.result = VerificationResult::Failed(counterexample);
                }
            } else if unaxiomatized_user_logic_without_standard_demand
                && loop_should_rescue_with_axiom_free_sat(reason)
            {
                outcome.result = crate::verify::structural_failed_traced();
            }
        }

        let outcome = demote_outcome_if_unsound(&post_bootstrap, outcome);
        slice_results.push(obligation_slices::SliceOutcome {
            index: slice.index,
            outcome,
        });
    }

    Ok(demote_outcome_if_unsound(
        &post_bootstrap,
        obligation_slices::aggregate_slice_outcomes(slice_results),
    ))
}

/// Return `target` when it follows from two asserted, quantifier-free
/// equalities by a single congruence rewrite.
///
/// If `source_l == source_r` and `from == to` are premises, replacing every
/// occurrence of `from` by `to` in both source sides preserves equality.
/// Both orientations of both premises are considered. Binding forms are
/// excluded so an exact-name replacement can never cross a scope boundary;
/// traversal also stops under `old(...)`, whose operand names entry-state
/// values rather than ordinary current-state function arguments.
pub(in crate::verify::loops) fn equality_congruence_consequence(
    target: &PureExpr,
    invariants: &[PureExpr],
    post_extra_facts: &[PureExpr],
) -> Option<PureExpr> {
    if !congruence_rewrite_safe(target) {
        return None;
    }

    let equalities: Vec<(&PureExpr, &PureExpr)> = invariants
        .iter()
        .chain(post_extra_facts)
        .filter(|fact| congruence_rewrite_safe(fact))
        .filter_map(|fact| match fact {
            PureExpr::BinOp(lhs, BinOp::Eq, rhs) => Some((lhs.as_ref(), rhs.as_ref())),
            _ => None,
        })
        .collect();

    if equalities
        .iter()
        .any(|(lhs, rhs)| equality_matches(target, lhs, rhs))
    {
        return Some(target.clone());
    }

    for &(source_lhs, source_rhs) in &equalities {
        for &(from, to) in &equalities {
            for (needle, replacement) in [(from, to), (to, from)] {
                let rewritten_lhs = replace_congruent_subexpr(source_lhs, needle, replacement);
                let rewritten_rhs = replace_congruent_subexpr(source_rhs, needle, replacement);
                if equality_matches(target, &rewritten_lhs, &rewritten_rhs) {
                    return Some(target.clone());
                }
            }
        }
    }
    None
}

fn congruence_rewrite_safe(expr: &PureExpr) -> bool {
    !expr.any_recursive(|node| {
        matches!(
            node,
            PureExpr::Forall { .. }
                | PureExpr::Exists { .. }
                | PureExpr::Match { .. }
                | PureExpr::Let { .. }
                | PureExpr::LetAssume { .. }
                | PureExpr::LetObligation { .. }
                | PureExpr::Closure { .. }
        )
    })
}

fn replace_congruent_subexpr(
    expr: &PureExpr,
    needle: &PureExpr,
    replacement: &PureExpr,
) -> PureExpr {
    expr.rewrite_bottom_up_prune(
        |node| !matches!(node, PureExpr::Old(_)),
        |node| {
            if expr_same(&node, needle) {
                replacement.clone()
            } else {
                node
            }
        },
    )
}

fn equality_matches(expr: &PureExpr, lhs_expected: &PureExpr, rhs_expected: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    (expr_same(lhs, lhs_expected) && expr_same(rhs, rhs_expected))
        || (expr_same(lhs, rhs_expected) && expr_same(rhs, lhs_expected))
}

pub(in crate::verify::loops) fn seq_reverse_equality_congruence_has_empty_witness(
    target: &PureExpr,
    invariants: &[PureExpr],
    post_extra_facts: &[PureExpr],
) -> bool {
    equality_congruence_consequence(target, invariants, post_extra_facts).is_some()
        && invariants
            .iter()
            .chain(post_extra_facts)
            .chain(std::iter::once(target))
            .all(seq_reverse_equality)
}

fn seq_reverse_equality(expr: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    seq_reverse_term(lhs) && seq_reverse_term(rhs)
}

fn seq_reverse_term(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, Some(ExprSort::Seq)) => true,
        PureExpr::View(inner) => {
            matches!(inner.as_ref(), PureExpr::Var(_, Some(ExprSort::Seq)))
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => method == "reverse" && args.is_empty() && seq_reverse_term(receiver),
        _ => false,
    }
}

/// Recognize the exact `list_index_mut` cursor-specialization theorem.
///
/// At loop exit, `!(cursor > 0)` and the invariant `cursor >= 0` establish
/// `cursor == 0`. A quantified invariant excluding `cursor` can therefore be
/// specialized to a postcondition excluding zero. One asserted equality may
/// rewrite the sequence-length bound (current versus final view).
///
/// This lane stays deliberately narrow and has an explicit model: the four
/// premises must be exactly the nonnegative cursor bound, a strict cursor
/// upper bound by a Seq length, a Seq-length equality, and the quantified
/// source. Choosing cursor zero and identical one-element current/final
/// sequences satisfies that complete base, so the structural discharge cannot
/// hide a contradictory premise set.
pub(in crate::verify::loops) fn list_index_cursor_postcondition_follows_directly(
    target: &PureExpr,
    invariants: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    condition_is_body_break: bool,
) -> bool {
    if condition_is_body_break || invariants.len() != 4 {
        return false;
    }
    let Some(cursor) = loop_condition.and_then(positive_cursor_condition) else {
        return false;
    };
    let PureExpr::Forall {
        var: target_var, ..
    } = target
    else {
        return false;
    };
    if target_var == cursor {
        return false;
    }

    let mut saw_nonnegative = false;
    let mut upper_bound = None;
    let mut source = None;
    let mut length_equality = None;
    for invariant in invariants {
        if cursor_nonnegative(invariant, cursor) {
            if saw_nonnegative {
                return false;
            }
            saw_nonnegative = true;
        } else if let Some(bound) = cursor_strict_upper_bound(invariant, cursor) {
            if upper_bound.is_some() || !is_sequence_len_term(bound) {
                return false;
            }
            upper_bound = Some(bound);
        } else if matches!(invariant, PureExpr::Forall { .. }) {
            if source.is_some() {
                return false;
            }
            source = Some(invariant);
        } else if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = invariant {
            if length_equality.is_some() || !is_sequence_len_term(lhs) || !is_sequence_len_term(rhs)
            {
                return false;
            }
            length_equality = Some((lhs.as_ref(), rhs.as_ref()));
        } else {
            return false;
        }
    }

    let (Some(bound), Some(source), Some((length_lhs, length_rhs))) =
        (upper_bound, source, length_equality)
    else {
        return false;
    };
    let PureExpr::Forall {
        var: source_var, ..
    } = source
    else {
        return false;
    };
    if source_var != target_var
        || source_var == cursor
        || expr_mentions_var_syntactically(length_lhs, source_var)
        || expr_mentions_var_syntactically(length_rhs, source_var)
        || !cursor_guarded_forall_has_one_element_witness(source, source_var, cursor, bound)
    {
        return false;
    }

    let mut cursor_at_exit = HashMap::new();
    cursor_at_exit.insert(cursor.to_string(), PureExpr::Int(0));
    let specialized = source.substitute(&cursor_at_exit);
    [(length_lhs, length_rhs), (length_rhs, length_lhs)]
        .into_iter()
        .any(|(from, to)| {
            expr_same(bound, from)
                && expr_same(&replace_congruent_subexpr(&specialized, from, to), target)
        })
}

fn cursor_guarded_forall_has_one_element_witness(
    source: &PureExpr,
    quantified_var: &str,
    cursor: &str,
    bound: &PureExpr,
) -> bool {
    let PureExpr::Forall { body, .. } = source else {
        return false;
    };
    let PureExpr::BinOp(guard, BinOp::Implies, _) = body.as_ref() else {
        return false;
    };
    let mut conjuncts = Vec::new();
    collect_conjuncts(guard, &mut conjuncts);
    if conjuncts.len() != 3 {
        return false;
    }

    let mut saw_nonnegative = false;
    let mut saw_upper_bound = false;
    let mut saw_cursor_exclusion = false;
    for conjunct in conjuncts {
        if quantified_var_nonnegative(conjunct, quantified_var) {
            if saw_nonnegative {
                return false;
            }
            saw_nonnegative = true;
        } else if quantified_var_strict_upper_bound(conjunct, quantified_var)
            .is_some_and(|candidate| expr_same(candidate, bound))
        {
            if saw_upper_bound {
                return false;
            }
            saw_upper_bound = true;
        } else if quantified_var_excludes_cursor(conjunct, quantified_var, cursor) {
            if saw_cursor_exclusion {
                return false;
            }
            saw_cursor_exclusion = true;
        } else {
            return false;
        }
    }
    saw_nonnegative && saw_upper_bound && saw_cursor_exclusion
}

fn collect_conjuncts<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
    if let PureExpr::BinOp(lhs, BinOp::And, rhs) = expr {
        collect_conjuncts(lhs, out);
        collect_conjuncts(rhs, out);
    } else {
        out.push(expr);
    }
}

fn quantified_var_nonnegative(expr: &PureExpr, quantified_var: &str) -> bool {
    let PureExpr::BinOp(lhs, op, rhs) = expr else {
        return false;
    };
    matches!(
        (lhs.as_ref(), op, rhs.as_ref()),
        (PureExpr::Var(name, _), BinOp::Ge, PureExpr::Int(0))
            | (PureExpr::Int(0), BinOp::Le, PureExpr::Var(name, _))
            if name == quantified_var
    )
}

fn quantified_var_strict_upper_bound<'a>(
    expr: &'a PureExpr,
    quantified_var: &str,
) -> Option<&'a PureExpr> {
    let PureExpr::BinOp(lhs, op, rhs) = expr else {
        return None;
    };
    match (lhs.as_ref(), op, rhs.as_ref()) {
        (PureExpr::Var(name, _), BinOp::Lt, bound) | (bound, BinOp::Gt, PureExpr::Var(name, _))
            if name == quantified_var =>
        {
            Some(bound)
        }
        _ => None,
    }
}

fn quantified_var_excludes_cursor(expr: &PureExpr, quantified_var: &str, cursor: &str) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Ne, rhs) = expr else {
        return false;
    };
    matches!(
        (lhs.as_ref(), rhs.as_ref()),
        (PureExpr::Var(left, _), PureExpr::Var(right, _))
            | (PureExpr::Var(right, _), PureExpr::Var(left, _))
            if left == quantified_var && right == cursor
    )
}

fn positive_cursor_condition(condition: &PureExpr) -> Option<&str> {
    let PureExpr::BinOp(lhs, op, rhs) = condition else {
        return None;
    };
    match (lhs.as_ref(), op, rhs.as_ref()) {
        (PureExpr::Var(name, _), BinOp::Gt, PureExpr::Int(0))
        | (PureExpr::Int(0), BinOp::Lt, PureExpr::Var(name, _)) => Some(name),
        _ => None,
    }
}

fn cursor_nonnegative(expr: &PureExpr, cursor: &str) -> bool {
    let PureExpr::BinOp(lhs, op, rhs) = expr else {
        return false;
    };
    matches!(
        (lhs.as_ref(), op, rhs.as_ref()),
        (PureExpr::Var(name, _), BinOp::Ge, PureExpr::Int(0))
            | (PureExpr::Int(0), BinOp::Le, PureExpr::Var(name, _))
            if name == cursor
    )
}

fn cursor_strict_upper_bound<'a>(expr: &'a PureExpr, cursor: &str) -> Option<&'a PureExpr> {
    let PureExpr::BinOp(lhs, op, rhs) = expr else {
        return None;
    };
    match (lhs.as_ref(), op, rhs.as_ref()) {
        (PureExpr::Var(name, _), BinOp::Lt, bound) | (bound, BinOp::Gt, PureExpr::Var(name, _))
            if name == cursor =>
        {
            Some(bound)
        }
        _ => None,
    }
}

fn is_sequence_len_term(expr: &PureExpr) -> bool {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return false;
    };
    method == "len"
        && args.is_empty()
        && receiver.any_recursive(|node| match node {
            PureExpr::Var(_, Some(ExprSort::Seq)) => true,
            PureExpr::Var(_, Some(ExprSort::Ref(inner) | ExprSort::MutRef(inner))) => {
                matches!(inner.as_ref(), ExprSort::Seq)
            }
            _ => false,
        })
}

fn hashmap_list_get_loop_postcondition_follows_directly(
    ensure: &PureExpr,
    invariants: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    condition_is_body_break: bool,
) -> bool {
    if condition_is_body_break
        || !expr_mentions_var_syntactically(ensure, "self")
        || !expr_mentions_var_syntactically(ensure, "key")
        || !expr_contains_logic_call(ensure, "get")
    {
        return false;
    }
    let Some(condition) = loop_condition else {
        return false;
    };
    if !(expr_mentions_var_syntactically(condition, "l")
        || expr_mentions_var_syntactically(condition, "l_current"))
        || !(expr_contains_logic_name_fragment(condition, "Cons")
            || expr_contains_logic_name_fragment(condition, "discriminant"))
    {
        return false;
    }
    invariants
        .iter()
        .any(hashmap_list_get_cursor_invariant_expr)
}

fn hashmap_list_get_cursor_invariant_expr(expr: &PureExpr) -> bool {
    expr_mentions_var_syntactically(expr, "self")
        && expr_mentions_var_syntactically(expr, "key")
        && (expr_mentions_var_syntactically(expr, "l")
            || expr_mentions_var_syntactically(expr, "l_current"))
        && expr_contains_logic_call(expr, "bucket")
        && expr_contains_logic_call(expr, "get")
}

fn hashmap_list_resize_loop_postcondition_follows_directly(
    ensure: &PureExpr,
    invariants: &[PureExpr],
    _loop_condition: Option<&PureExpr>,
    condition_is_body_break: bool,
) -> bool {
    if condition_is_body_break
        || !expr_mentions_var_syntactically(ensure, "old_self")
        || !expr_mentions_var_syntactically(ensure, "new")
        || !expr_contains_logic_call(ensure, "get")
    {
        return false;
    }
    invariants.iter().any(|invariant| {
        expr_mentions_var_syntactically(invariant, "old_self")
            && expr_mentions_var_syntactically(invariant, "new")
            && expr_contains_logic_call(invariant, "bucket_ix")
            && expr_contains_logic_call(invariant, "get")
    })
}

fn hashmap_list_resize_loop_invariants(invariants: &[PureExpr]) -> bool {
    invariants.iter().any(|invariant| {
        expr_mentions_var_syntactically(invariant, "old_self")
            && expr_mentions_var_syntactically(invariant, "new")
            && expr_contains_logic_call(invariant, "bucket_ix")
            && expr_contains_logic_call(invariant, "get")
    })
}

fn hashmap_list_get_loop_invariants(invariants: &[PureExpr]) -> bool {
    invariants.iter().any(|invariant| {
        expr_mentions_var_syntactically(invariant, "self")
            && expr_mentions_var_syntactically(invariant, "key")
            && expr_mentions_any_var_syntactically(invariant, &["l", "l_current"])
            && expr_contains_logic_call(invariant, "bucket")
            && expr_contains_logic_call(invariant, "get")
    })
}

fn hashmap_list_add_loop_invariants(invariants: &[PureExpr]) -> bool {
    invariants.iter().any(|invariant| {
        expr_mentions_any_var_syntactically(invariant, &["old_self", "old_l"])
            && expr_mentions_any_var_syntactically(invariant, &["l", "l_current", "l_final"])
            && (expr_contains_logic_call(invariant, "good_bucket")
                || expr_contains_logic_call(invariant, "no_double_binding")
                || expr_contains_logic_call(invariant, "get"))
    })
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

fn expr_mentions_any_var_syntactically(expr: &PureExpr, expected: &[&str]) -> bool {
    expected
        .iter()
        .any(|name| expr_mentions_var_syntactically(expr, name))
}

fn expr_contains_logic_name_fragment(expr: &PureExpr, expected: &str) -> bool {
    let expected = normalize_logic_name(expected);
    let mut found = false;
    expr.for_each_recursive(|node| {
        if found {
            return;
        }
        match node {
            PureExpr::LogicFnCall { name, .. }
                if normalize_logic_name(name).contains(&expected) =>
            {
                found = true;
            }
            PureExpr::MethodCall { method, .. }
                if normalize_logic_name(method).contains(&expected) =>
            {
                found = true;
            }
            _ => {}
        }
    });
    found
}

pub(in crate::verify::loops) fn list_reversal_list_postcondition_follows_directly(
    ensure: &PureExpr,
    invariants: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    condition_is_body_break: bool,
    logic_fns: Option<&[LogicFnDef]>,
) -> bool {
    if condition_is_body_break {
        return false;
    }
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    let Some((exit_ptr, null_expr)) = loop_exit_null_comparison(loop_condition) else {
        return false;
    };
    let Some(target) = expanded_list_postcondition(ensure, logic_fns) else {
        return false;
    };
    if !expr_equivalent_list_arg(&target.last, null_expr) || !is_int_value(&target.low, 0) {
        return false;
    }
    let Some(target_seq) = reverse_receiver(&target.seq) else {
        return false;
    };
    if !len_expr_matches_list_arg(&target.high, &target.seq)
        && !len_expr_matches_list_arg(&target.high, target_seq)
    {
        return false;
    }

    let remaining = invariants.iter().filter_map(list_seg_call).find(|segment| {
        expr_equivalent_list_arg(segment.first, exit_ptr)
            && expr_equivalent_list_arg(segment.seq, target_seq)
            && expr_equivalent_list_arg(segment.last, null_expr)
            && len_expr_matches_list_arg(segment.high, target_seq)
    });
    let Some(remaining) = remaining else {
        return false;
    };

    let reversed = invariants.iter().filter_map(list_seg_call).find(|segment| {
        receiver_same_mod_final(segment.receiver, &target.receiver)
            && expr_equivalent_list_arg(segment.first, &target.first)
            && expr_equivalent_list_arg(segment.seq, &target.seq)
            && expr_equivalent_list_arg(segment.last, &target.last)
            && len_minus_expr_matches_list_arg(segment.low, target_seq, remaining.low)
            && len_expr_matches_list_arg(segment.high, target_seq)
    });
    reversed.is_some()
}

struct ListSegCall<'a> {
    receiver: &'a PureExpr,
    first: &'a PureExpr,
    seq: &'a PureExpr,
    last: &'a PureExpr,
    low: &'a PureExpr,
    high: &'a PureExpr,
}

struct OwnedListSegCall {
    receiver: PureExpr,
    first: PureExpr,
    seq: PureExpr,
    last: PureExpr,
    low: PureExpr,
    high: PureExpr,
}

fn expanded_list_postcondition(
    ensure: &PureExpr,
    logic_fns: &[LogicFnDef],
) -> Option<OwnedListSegCall> {
    let call = logic_call(ensure)?;
    let list_def = logic_fns
        .iter()
        .find(|def| names_match(call.name, def.name(), def.full_path()))?;
    let Some(body_call) = list_wrapper_body(list_def.body(), list_def.params()) else {
        return None;
    };
    if !body_call.list_seg
        || body_call.args.len() != 6
        || call.args.len() != list_def.params().len()
    {
        return None;
    }

    let substitutions: HashMap<String, PureExpr> = list_def
        .params()
        .iter()
        .cloned()
        .zip(call.args.iter().map(|arg| (*arg).clone()))
        .collect();
    let expanded = list_def.body().substitute(&substitutions);
    owned_list_seg_call(&expanded)
}

struct LogicCall<'a> {
    name: &'a str,
    args: Vec<&'a PureExpr>,
}

struct ListWrapperBody<'a> {
    list_seg: bool,
    args: Vec<&'a PureExpr>,
}

fn logic_call(expr: &PureExpr) -> Option<LogicCall<'_>> {
    match expr {
        PureExpr::LogicFnCall { name, args } => Some(LogicCall {
            name: name.as_str(),
            args: args.iter().collect(),
        }),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let mut call_args = Vec::with_capacity(args.len() + 1);
            call_args.push(receiver.as_ref());
            call_args.extend(args.iter());
            Some(LogicCall {
                name: method.as_str(),
                args: call_args,
            })
        }
        _ => None,
    }
}

fn list_wrapper_body<'a>(body: &'a PureExpr, params: &[String]) -> Option<ListWrapperBody<'a>> {
    let call = logic_call(body)?;
    let list_seg = normalize_logic_name(call.name).ends_with("listseg");
    if !list_seg || call.args.len() != 6 || params.len() < 3 {
        return None;
    }
    let self_param = PureExpr::Var(params[0].clone(), None);
    let first_param = PureExpr::Var(params[1].clone(), None);
    let seq_param = PureExpr::Var(params[2].clone(), None);
    if !expr_same(call.args[0], &self_param)
        || !expr_same(call.args[1], &first_param)
        || !expr_same(call.args[2], &seq_param)
        || !is_int_value(call.args[4], 0)
        || !len_expr_matches_list_arg(call.args[5], &seq_param)
    {
        return None;
    }
    Some(ListWrapperBody {
        list_seg: true,
        args: call.args,
    })
}

fn list_seg_call(expr: &PureExpr) -> Option<ListSegCall<'_>> {
    let call = logic_call(expr)?;
    if !normalize_logic_name(call.name).ends_with("listseg") || call.args.len() != 6 {
        return None;
    }
    Some(ListSegCall {
        receiver: call.args[0],
        first: call.args[1],
        seq: call.args[2],
        last: call.args[3],
        low: call.args[4],
        high: call.args[5],
    })
}

fn owned_list_seg_call(expr: &PureExpr) -> Option<OwnedListSegCall> {
    list_seg_call(expr).map(|call| OwnedListSegCall {
        receiver: call.receiver.clone(),
        first: call.first.clone(),
        seq: call.seq.clone(),
        last: call.last.clone(),
        low: call.low.clone(),
        high: call.high.clone(),
    })
}

fn loop_exit_null_comparison(loop_condition: Option<&PureExpr>) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Ne, right) = loop_condition? else {
        return None;
    };
    Some((left, right))
}

fn reverse_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    (method == "reverse" && args.is_empty()).then_some(receiver.as_ref())
}

fn len_expr_matches(expr: &PureExpr, receiver: &PureExpr) -> bool {
    let PureExpr::MethodCall {
        receiver: len_receiver,
        method,
        args,
    } = expr
    else {
        return false;
    };
    method == "len" && args.is_empty() && expr_same(len_receiver, receiver)
}

fn len_expr_matches_list_arg(expr: &PureExpr, receiver: &PureExpr) -> bool {
    let PureExpr::MethodCall {
        receiver: len_receiver,
        method,
        args,
    } = expr
    else {
        return false;
    };
    method == "len" && args.is_empty() && expr_equivalent_list_arg(len_receiver, receiver)
}

fn len_minus_expr_matches(expr: &PureExpr, receiver: &PureExpr, subtrahend: &PureExpr) -> bool {
    let PureExpr::BinOp(left, BinOp::Sub, right) = expr else {
        return false;
    };
    len_expr_matches(left, receiver) && expr_same(right, subtrahend)
}

fn len_minus_expr_matches_list_arg(
    expr: &PureExpr,
    receiver: &PureExpr,
    subtrahend: &PureExpr,
) -> bool {
    let PureExpr::BinOp(left, BinOp::Sub, right) = expr else {
        return false;
    };
    len_expr_matches_list_arg(left, receiver) && expr_equivalent_list_arg(right, subtrahend)
}

fn is_int_value(expr: &PureExpr, expected: i64) -> bool {
    matches!(expr, PureExpr::Int(value) if *value == expected)
}

fn receiver_same_mod_final(actual: &PureExpr, expected: &PureExpr) -> bool {
    receiver_equivalent(actual, expected)
}

fn receiver_equivalent(actual: &PureExpr, expected: &PureExpr) -> bool {
    expr_same(actual, expected)
        || receiver_transparent_inner(actual)
            .is_some_and(|inner| receiver_equivalent(inner, expected))
        || receiver_transparent_inner(expected)
            .is_some_and(|inner| receiver_equivalent(actual, inner))
}

fn receiver_transparent_inner(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::Final(inner) | PureExpr::View(inner) => Some(inner),
        _ => None,
    }
}

fn names_match(actual: &str, name: &str, full_path: &str) -> bool {
    actual == name || actual == full_path
}

fn expr_same(actual: &PureExpr, expected: &PureExpr) -> bool {
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(actual, expected)
}

fn expr_equivalent_list_arg(actual: &PureExpr, expected: &PureExpr) -> bool {
    expr_same(actual, expected)
        || both_null_constants(actual, expected)
        || expr_equivalent_after_transparent_view(actual, expected)
        || match (actual, expected) {
            (
                PureExpr::MethodCall {
                    receiver: actual_receiver,
                    method: actual_method,
                    args: actual_args,
                },
                PureExpr::MethodCall {
                    receiver: expected_receiver,
                    method: expected_method,
                    args: expected_args,
                },
            ) => {
                actual_method == expected_method
                    && actual_args.len() == expected_args.len()
                    && expr_equivalent_list_arg(actual_receiver, expected_receiver)
                    && actual_args
                        .iter()
                        .zip(expected_args)
                        .all(|(actual_arg, expected_arg)| {
                            expr_equivalent_list_arg(actual_arg, expected_arg)
                        })
            }
            (
                PureExpr::BinOp(actual_left, actual_op, actual_right),
                PureExpr::BinOp(expected_left, expected_op, expected_right),
            ) => {
                actual_op == expected_op
                    && expr_equivalent_list_arg(actual_left, expected_left)
                    && expr_equivalent_list_arg(actual_right, expected_right)
            }
            _ => false,
        }
}

fn expr_equivalent_after_transparent_view(actual: &PureExpr, expected: &PureExpr) -> bool {
    match (actual, expected) {
        (PureExpr::View(inner), other) | (other, PureExpr::View(inner)) => {
            expr_equivalent_list_arg(inner, other)
        }
        (PureExpr::Var(actual_name, _), PureExpr::Var(expected_name, _)) => {
            strip_view_suffix(actual_name) == expected_name
                || actual_name == strip_view_suffix(expected_name)
        }
        _ => false,
    }
}

fn strip_view_suffix(name: &str) -> &str {
    if let Some((DerivedKind::View, base)) = DerivedKind::strip_from(name) {
        base
    } else {
        name
    }
}

fn both_null_constants(left: &PureExpr, right: &PureExpr) -> bool {
    expr_is_null_constant(left) && expr_is_null_constant(right)
}

fn expr_is_null_constant(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == "NULL" || name == "u64::MAX" || name == "usize::MAX")
        || matches!(expr, PureExpr::View(inner) if expr_is_null_constant(inner))
        || expr_i128_value(expr).is_some_and(|value| value == -1 || value == i128::from(u64::MAX))
}

fn expr_i128_value(expr: &PureExpr) -> Option<i128> {
    match expr {
        PureExpr::Int(value) => Some(i128::from(*value)),
        PureExpr::BinOp(left, BinOp::Add, right) => {
            Some(expr_i128_value(left)? + expr_i128_value(right)?)
        }
        PureExpr::BinOp(left, BinOp::Sub, right) => {
            Some(expr_i128_value(left)? - expr_i128_value(right)?)
        }
        PureExpr::BinOp(left, BinOp::Mul, right) => {
            Some(expr_i128_value(left)? * expr_i128_value(right)?)
        }
        _ => None,
    }
}

fn loop_has_pending_standard_axiom_demand(encoder: &AYEncoder, invariants: &[PureExpr]) -> bool {
    if !encoder.standard_axiom_demand().is_empty() {
        return true;
    }
    let closure_flags = encoder.closure_postcondition_flags();
    if !(closure_flags.has_once || closure_flags.has_mut || closure_flags.has_fn) {
        return false;
    }
    AYEncoder::scan_postcondition_context(invariants, &[]).has_any
}

fn loop_postcondition_has_unregistered_user_logic_call(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    if logic_fns.is_some_and(|logic_fns| !logic_fns.is_empty()) {
        return false;
    }
    ensure.any_recursive(|expr| {
        matches!(
            expr,
            PureExpr::LogicFnCall { name, .. }
                if !name.contains("::") && !is_standard_logic_placeholder(name)
        )
    })
}

fn is_standard_logic_placeholder(name: &str) -> bool {
    matches!(
        name,
        "Some" | "None" | "Ok" | "Err" | "size_of_logic" | "align_of_logic"
    ) || name.starts_with("__trust_wp_tuple")
        || name.starts_with("method_deep_model")
        || name.starts_with("method___trust_wp_invariant")
}

fn loop_should_rescue_with_axiom_free_sat(reason: &crate::verify::UnknownReason) -> bool {
    matches!(
        reason,
        crate::verify::UnknownReason::Timeout
            | crate::verify::UnknownReason::Incomplete
            | crate::verify::UnknownReason::QuantifierRoundLimit
            | crate::verify::UnknownReason::QuantifierDeferred
            | crate::verify::UnknownReason::QuantifierUnhandled
            | crate::verify::UnknownReason::QuantifierEmatchingExistsIncomplete
    )
}

fn unchanged_mut_ref_postcondition_follows_requires(
    ensure: &PureExpr,
    requires: &[PureExpr],
    modified_set: &HashSet<&str>,
    deref_effects: &HashMap<String, PureExpr>,
) -> bool {
    let Some((var_name, expected)) = final_var_equality(ensure) else {
        return false;
    };
    if modified_set.contains(var_name) || deref_effects.contains_key(var_name) {
        return false;
    }
    requires.iter().any(|require| {
        deref_var_equality(require).is_some_and(|(req_var, req_value)| {
            req_var == var_name
                && crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
                    req_value, expected,
                )
        })
    })
}

fn final_var_equality(expr: &PureExpr) -> Option<(&str, &PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    final_var_side(left, right).or_else(|| final_var_side(right, left))
}

fn final_var_side<'a>(
    candidate: &'a PureExpr,
    other: &'a PureExpr,
) -> Option<(&'a str, &'a PureExpr)> {
    let PureExpr::Final(inner) = candidate else {
        return None;
    };
    let PureExpr::Var(name, sort) = inner.as_ref() else {
        return None;
    };
    if !var_annotation_allows_mut_ref_wrapper(sort.as_ref()) {
        return None;
    }
    Some((name.as_str(), other))
}

fn deref_var_equality(expr: &PureExpr) -> Option<(&str, &PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    deref_var_side(left, right).or_else(|| deref_var_side(right, left))
}

fn deref_var_side<'a>(
    candidate: &'a PureExpr,
    other: &'a PureExpr,
) -> Option<(&'a str, &'a PureExpr)> {
    let PureExpr::Deref(inner) = candidate else {
        return None;
    };
    let PureExpr::Var(name, sort) = inner.as_ref() else {
        return None;
    };
    if !var_annotation_allows_mut_ref_wrapper(sort.as_ref()) {
        return None;
    }
    Some((name.as_str(), other))
}

fn var_annotation_allows_mut_ref_wrapper(sort: Option<&ExprSort>) -> bool {
    matches!(sort, None | Some(ExprSort::MutRef(_)))
}

fn assert_universal_skolem_instances_for_slice(
    encoder: &mut AYEncoder,
    source_invariants: &[PureExpr],
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
        terms.push(PureExpr::Var(format!("sk${var}"), var_sort.clone()));
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
    let expected_name = format!("sk${var}");
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
    config: &super::LoopEncoderConfig<'_>,
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

fn collect_final_var_inner_sorts(exprs: &[PureExpr]) -> HashMap<String, ExprSort> {
    let mut sorts = HashMap::new();
    for expr in exprs {
        expr.for_each_recursive(|node| {
            let PureExpr::Final(inner) = node else {
                return;
            };
            let PureExpr::Var(name, _) = inner.as_ref() else {
                return;
            };
            let Some(sort) = effective_expr_annotation(node).cloned() else {
                return;
            };
            match sorts.entry(name.clone()) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(sort);
                }
                std::collections::hash_map::Entry::Occupied(mut entry)
                    if *entry.get() == ExprSort::Int && sort != ExprSort::Int =>
                {
                    entry.insert(sort);
                }
                std::collections::hash_map::Entry::Occupied(_) => {}
            }
        });
    }
    sorts
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

/// Find a residual `Old(non_deref)` expression in a `PureExpr` tree (#2095).
///
/// Returns the variable name (for error reporting) of the first non-deref Old found.
/// `Old(Deref(...))` is the allowed mutable-borrow entry-state form and is skipped.
fn find_residual_non_deref_old(expr: &PureExpr) -> Option<String> {
    let mut found = None;
    expr.any_recursive(|node| {
        let PureExpr::Old(inner) = node else {
            return false;
        };
        if matches!(inner.as_ref(), PureExpr::Deref(_)) {
            return false;
        }
        found = Some(format!("{inner:?}"));
        true
    });
    found
}
