// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Initialization and loop-entry verification.
//!
//! Implements:
//! - **Initialization**: precondition ∧ pre-loop assignments => invariant
//! - **Loop entry reachability**: checks if the loop condition is satisfiable from entry state

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
    time::Duration,
};

use trust_wp_core::{
    formula::{BinOp, ExprSort, NamedBindingValue, PureExpr, UnOp},
    logic::LogicFnDef,
};

use super::{
    super::{
        assert_eager_negated_existential_instantiations, assert_standard_axioms, demote_if_unsound,
        encode_and_assert_negated_postconditions, obligation_slices,
        setup::{bootstrap_encoder, BootstrapRequest, ExprSlice, LogicFnInput, TypeInvariantInput},
        try_axiom_free_solve, VerificationOutcome, VerificationResult,
    },
    encoder_setup::{
        assert_loop_current_chain_alias_constraints, encode_and_assert_condition,
        encode_and_assert_requires, resolve_sat_result_lightweight_timed,
        solve_scoped_loop_initialization_obligation_outcome, OutcomeContinuation,
    },
    expr_helpers,
    expr_helpers::expr_references_any_var,
    LoopEncoderConfig,
};
use crate::{
    encoder::{unsoundness, LogicGroundInstantiationMode},
    error::EncodingError,
};

/// Verify initialization: precondition ∧ pre-loop assignments => invariant
///
/// Pre-loop assignments capture the values of locally-declared variables at
/// loop entry (e.g., `let mut i = 0` produces `i == 0`). These constrain
/// loop variables to their actual initial values rather than leaving them
/// as unconstrained free variables.
#[allow(clippy::too_many_lines)] // Loop initialization with variable-binding and vacuity checks
pub(in crate::verify::loops) fn verify_initialization(
    base: &super::LoopVcBase<'_>,
    requires: &[PureExpr],
    pre_loop_assignments: &HashMap<String, NamedBindingValue>,
    init_extra_facts: &[PureExpr],
) -> Result<VerificationResult, EncodingError> {
    Ok(
        verify_initialization_outcome(base, requires, pre_loop_assignments, init_extra_facts)?
            .result,
    )
}

pub(in crate::verify::loops) fn verify_initialization_outcome(
    base: &super::LoopVcBase<'_>,
    requires: &[PureExpr],
    pre_loop_assignments: &HashMap<String, NamedBindingValue>,
    init_extra_facts: &[PureExpr],
) -> Result<VerificationOutcome, EncodingError> {
    let invariants = base.invariants;
    let config = base.config;
    let base_snapshot = unsoundness::snapshot();
    if invariants.is_empty() {
        return super::encoder_setup::prove_empty_initialization_outcome(config)
            .map(|outcome| demote_outcome_if_unsound(&base_snapshot, outcome));
    }
    // Build equality constraints from pre-loop assignments (e.g., i == 0)
    // Uses NamedBindingValue.lhs_var() to preserve the MIR-derived sort of the
    // symbolic variable across the driver -> ay boundary. (#2053 Slice B)
    let assignment_expr_entries: Vec<(String, PureExpr)> = pre_loop_assignments
        .iter()
        .map(|(name, binding)| {
            (
                name.clone(),
                PureExpr::BinOp(
                    Arc::new(binding.lhs_var(name)),
                    BinOp::Eq,
                    Arc::new(binding.value.clone()),
                ),
            )
        })
        .collect();
    let assignment_exprs: Vec<PureExpr> = assignment_expr_entries
        .iter()
        .map(|(_, expr)| expr.clone())
        .collect();

    // Early vacuity guard (#2440): check if requires + assignments + init_extra_facts
    // are contradictory using a separate encoder. If so, any proof is vacuous.
    {
        let base_exprs: Vec<PureExpr> = requires
            .iter()
            .chain(assignment_exprs.iter())
            .chain(init_extra_facts.iter())
            .cloned()
            .collect();
        if super::encoder_setup::is_base_vacuous(&base_exprs) {
            return Ok(VerificationOutcome::without_provenance(demote_if_unsound(
                &base_snapshot,
                VerificationResult::Unknown(crate::verify::UnknownReason::SolverMessage(
                    crate::verify::solver_tail::VACUOUS_PROOF_MESSAGE.to_string(),
                )),
            )));
        }
    }

    // Substitute pre-loop values into invariants before negation (#2116).
    //
    // Without substitution, the negated invariant contains variables like
    // `produced` that are constrained by separate equality assertions
    // (`produced == seq_empty()`). ay-dpll's single-round E-matching cannot
    // match `concat(produced, iter)` against the quantified axiom trigger
    // `concat(seq_empty, s)` even when `produced == seq_empty` via CC.
    //
    // Substituting directly gives the encoder `concat(seq_empty(), iter)`,
    // which the trigger matches syntactically. The unsubstituted equality
    // assertions remain for vacuity checking and sort grounding.
    let init_subs: HashMap<String, PureExpr> = pre_loop_assignments
        .iter()
        .map(|(name, binding)| (name.clone(), binding.value.clone()))
        .collect();
    let substituted_invariants: Vec<PureExpr> = if init_subs.is_empty() {
        invariants.to_vec()
    } else {
        invariants
            .iter()
            .map(|inv| inv.substitute(&init_subs))
            .collect()
    };

    // Simplify Deref-through-substitution for Snapshot/Ghost value types (#1709).
    //
    // After substituting pre-loop values, patterns like `*total` (where
    // `total = snapshot!(x@)`) become `Deref(View(x))` rather than `View(x)`.
    // For immutable value types (Snapshot, Ghost), `Deref` is an identity
    // operation — the wrapper is transparent. Without this simplification,
    // the SMT encoder produces `total_current` for `Deref(View(x))` which
    // is an unconstrained variable disconnected from `View(x)`.
    //
    // The rewrite is safe because the substituted expression IS the concrete
    // pre-loop value, and we're only in the initialization phase where
    // variables hold their pre-loop values. We apply this bottom-up to catch
    // nested patterns like `View(Deref(substituted))` → `View(substituted)`.
    let substituted_invariants: Vec<PureExpr> = if init_subs.is_empty() {
        substituted_invariants
    } else {
        substituted_invariants
            .into_iter()
            .map(|inv| {
                inv.rewrite_bottom_up(|node| match node {
                    PureExpr::Deref(ref inner) => {
                        // Only collapse Deref when the inner expression does not
                        // resolve to a named variable through a Deref/Final/Old
                        // chain. Such chains (e.g., `Deref(Var(x))` for `*x`, or
                        // `Deref(Deref(Var(x)))` for `**x`) need the `_current`
                        // encoding for mutable reference semantics — collapsing
                        // a `Deref` over them would lose a level of dereference
                        // and unify `**x` with `*x` in the SMT encoding.
                        // (#2665 + nested-borrows regression: previously only the
                        // immediate `Deref(Var)` was preserved, so `Deref(Deref(Var(x)))`
                        // — i.e. `**x` — was incorrectly collapsed to `*x`.)
                        // Substituted expressions (View, Int, LogicFnCall, etc.)
                        // remain safe to unwrap.
                        if deref_chain_targets_var(inner.as_ref()) {
                            node
                        } else {
                            inner.as_ref().clone()
                        }
                    }
                    other => other,
                })
            })
            .collect()
    };

    // Re-apply scalar view stripping after substitution + deref-through (#2698).
    //
    // Substitution can introduce new `View(Var(x))` nodes (e.g., when a
    // snapshot variable `total` with pre-loop value `View(x)` is substituted
    // into `Deref(total)`, and the deref-through pass collapses `Deref(View(x))`
    // to `View(x)`). The dispatcher's initial `strip_scalar_views` ran BEFORE
    // substitution, so these post-substitution View wrappers are unsimplified.
    // Without re-stripping, `View(x)` encodes as `x_view` (a separate SMT
    // variable) while `x` encodes as `x`, making `View(x) == x + 0` a
    // non-trivial equality that the solver may fail to prove. Re-stripping
    // collapses `View(Var(x))` to `Var(x)` so both sides use the same variable.
    let substituted_invariants: Vec<PureExpr> = if init_subs.is_empty() {
        substituted_invariants
    } else {
        substituted_invariants
            .into_iter()
            .map(|inv| super::expr_helpers::strip_scalar_views(&inv))
            .collect()
    };

    // Normalize doubly-quantified FMap get/Some biconditionals. (#2116)
    let normalized_invariants: Vec<PureExpr> = substituted_invariants
        .iter()
        .map(super::invariant_transforms::normalize_fmap_get_biconditional)
        .collect();

    // Pre-synthesize triggers for triggerless foralls so that ay-dpll's
    // E-matching fires reliably when the negated invariant creates an
    // existential witness. (#2116)
    let triggered_invariants: Vec<PureExpr> = normalized_invariants
        .iter()
        .map(super::invariant_transforms::inject_forall_triggers)
        .collect();

    let slices = obligation_slices::split_ensures(&triggered_invariants);
    let mut slice_results: Vec<obligation_slices::SliceOutcome> = Vec::with_capacity(slices.len());

    for slice in &slices {
        // The substitution above rewrote every pre-loop-bound name the
        // invariant reads to its value, so the slice no longer names it. An
        // initialization fact describing that name is a premise of the slice
        // all the same, with the binding that ties the name to the value the
        // slice reads: a model that never saw them picks what they fix (an
        // empty map's `get`: loop_fmap_iter_new_map_empty_at_entry_control),
        // and is no counterexample. A name no fact describes gains nothing
        // from its binding beyond the substitution itself.
        let written_invariant = invariants.get(slice.index);
        let relevant_entry_vars: HashSet<&str> = assignment_expr_entries
            .iter()
            .filter_map(|(name, _)| {
                let singleton: HashSet<&str> = [name.as_str()].into_iter().collect();
                let replaced_and_described = written_invariant
                    .is_some_and(|written| expr_references_any_var(written, &singleton))
                    && init_extra_facts
                        .iter()
                        .any(|fact| expr_references_any_var(fact, &singleton));
                (expr_references_any_var(slice.ensure.as_ref(), &singleton)
                    || replaced_and_described)
                    .then_some(name.as_str())
            })
            .collect();
        let relevant_assignment_exprs: Vec<PureExpr> = assignment_expr_entries
            .iter()
            .filter(|(name, _)| relevant_entry_vars.contains(name.as_str()))
            .map(|(_, expr)| expr.clone())
            .collect();
        // Include init_extra_facts transitively: seed with variables from
        // the invariant slice and relevant pre-loop assignments, then iterate
        // until no new facts are reachable.
        //
        // Init facts form a variable chain: the invariant references `iter`
        // (the user binding), which connects to `iter_state` via
        // `iter_state == iter`, which connects to `iter_old` and
        // `View(iter_state)` via further init facts. A single-pass filter
        // only includes `iter_state == iter` and drops the rest. The
        // fixpoint loop below iterates until no new variables are discovered,
        // ensuring the full chain is included. (#2116)
        let mut reachable_vars: HashSet<&str> = {
            let mut vars = HashSet::new();
            expr_helpers::collect_expr_var_names(slice.ensure.as_ref(), &mut vars);
            for name in &relevant_entry_vars {
                vars.insert(*name);
            }
            for (name, expr) in &assignment_expr_entries {
                if relevant_entry_vars.contains(name.as_str()) {
                    expr_helpers::collect_expr_var_names(expr, &mut vars);
                }
            }
            vars
        };
        let mut included: Vec<bool> = vec![false; init_extra_facts.len()];
        loop {
            let mut changed = false;
            for (i, fact) in init_extra_facts.iter().enumerate() {
                if included[i] {
                    continue;
                }
                if expr_references_any_var(fact, &reachable_vars) {
                    included[i] = true;
                    changed = true;
                    expr_helpers::collect_expr_var_names(fact, &mut reachable_vars);
                }
            }
            if !changed {
                break;
            }
        }
        let relevant_init_facts: Vec<PureExpr> = init_extra_facts
            .iter()
            .enumerate()
            .filter(|(i, _)| included[*i])
            .map(|(_, fact)| expr_helpers::canonicalize_fmap_new(fact))
            .collect();
        let fmap_len_fact_sources: Vec<PureExpr> = relevant_assignment_exprs
            .iter()
            .chain(relevant_init_facts.iter())
            .cloned()
            .collect();
        let derived_fmap_len_facts = expr_helpers::derive_fmap_len_facts(&fmap_len_fact_sources);
        let relevant_init_facts: Vec<PureExpr> = relevant_init_facts
            .into_iter()
            .chain(derived_fmap_len_facts)
            .collect();

        if direct_initialization_facts_prove_slice(
            slice.ensure.as_ref(),
            requires,
            &relevant_assignment_exprs,
            &relevant_init_facts,
            config.logic_fns,
        ) {
            if let Some(outcome) = prove_direct_initialization_slice_with_solver_evidence(
                slice.ensure.as_ref(),
                requires,
                &relevant_assignment_exprs,
                &relevant_init_facts,
                config,
            )? {
                slice_results.push(obligation_slices::SliceOutcome {
                    index: slice.index,
                    outcome,
                });
                continue;
            }
            slice_results.push(obligation_slices::SliceOutcome {
                index: slice.index,
                outcome: VerificationOutcome::without_provenance(VerificationResult::Verified(
                    None,
                )),
            });
            continue;
        }

        // Bootstrap per slice so each initialization VC only declares the
        // invariant symbols it actually needs. The combined Seq iterator
        // initialization shape (`produces && reverse`) otherwise pulls both
        // axiom families into every slice, which makes the ext_eq/concat slice
        // time out even though it does not reference `reverse`. (#2116)
        let slice_exprs = [
            ExprSlice::formula(requires),
            ExprSlice::formula(std::slice::from_ref(slice.ensure.as_ref())),
            ExprSlice::formula(&relevant_assignment_exprs),
            ExprSlice::formula(&relevant_init_facts),
        ];
        let mut encoder = bootstrap_encoder(BootstrapRequest {
            expr_slices: &slice_exprs,
            result_postconditions: Some(std::slice::from_ref(slice.ensure.as_ref())),
            result_expr: None,
            logic_fns: config.logic_fns.map(LogicFnInput::FilterForGoalGroundOnly),
            mode_overrides: config.mode_overrides,
            type_invariants: config
                .type_invariants
                .map(TypeInvariantInput::FilterForGoal),
            track: config.track.unwrap_or_default(),
            timeout: config.timeout,
            type_constants: config.type_constants,
            closure_captures: None,
            adt_decls: config.adt_decls,
            adt_field_ranges: config.adt_field_ranges,
        })?;
        // Post-bootstrap snapshot: absorb SortFallbackToIntFromLogicFn
        // increments from this slice's sort-hint collection. (#2062)
        let post_bootstrap = unsoundness::snapshot();

        // Assert preconditions with existential Skolemization (#1364).
        encode_and_assert_requires(&mut encoder, requires)?;

        // Assert pre-loop assignments (e.g., i == 0)
        for assign_expr in &relevant_assignment_exprs {
            let term = encoder.encode_pure(assign_expr)?;
            encoder.assert_term(term);
        }

        // Assert extra init facts (e.g., produced.len() == 0 for for-loops)
        for fact in &relevant_init_facts {
            let term = encoder.encode_pure(fact)?;
            encoder.assert_term(term);
        }

        let outcome =
            match solve_scoped_loop_initialization_obligation_outcome(&mut encoder, |encoder| {
                assert_eager_negated_existential_instantiations(
                    encoder,
                    std::slice::from_ref(slice.ensure.as_ref()),
                    requires,
                    &[],
                )?;

                // Negate this invariant slice first so that encoding creates any
                // `_current`-suffixed variables needed by the alias pass. (#1441)
                let _asserted = encode_and_assert_negated_postconditions(
                    encoder,
                    std::slice::from_ref(slice.ensure.as_ref()),
                    config.logic_fns,
                    None,
                )?;

                // Now that all variables exist, assert _current-chain aliases.
                assert_loop_current_chain_alias_constraints(encoder)?;

                encoder.mark_postcondition_logic_fn_symbols(std::slice::from_ref(
                    slice.ensure.as_ref(),
                ));
                encoder.mark_postcondition_logic_fn_symbols(requires);
                encoder.mark_postcondition_logic_fn_symbols(&relevant_assignment_exprs);
                encoder.mark_postcondition_logic_fn_symbols(&relevant_init_facts);

                // Pre-assert Seq ground instances before axiom probe. (#2323)
                if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia) {
                    encoder.assert_seq_ground_instances(
                        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
                    );
                }

                // Two-phase axiom solving (#2116): try without axioms first.
                // Many initialization obligations (empty Seq == empty Seq, i == 0)
                // are provable from declarations alone. Skipping 30-50+ quantified
                // axioms avoids overwhelming ay-dpll's single-round E-matching.
                if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia)
                    && try_axiom_free_solve(encoder).is_none()
                {
                    // Phase 2: axioms needed. Pass requires so eager instantiation
                    // (fn_mut_once, Skolemization) can scan for ground closure-spec
                    // terms. ay v0.2.0 E-matching needs these eagerly instantiated.
                    assert_standard_axioms(encoder, requires, &[])?;
                }

                Ok(())
            })? {
                OutcomeContinuation::Continue(outcome) => outcome,
                OutcomeContinuation::Abort(outcome) => {
                    return Ok(demote_outcome_if_unsound(&post_bootstrap, outcome));
                }
            };

        let outcome = demote_outcome_if_unsound(&post_bootstrap, outcome);
        slice_results.push(obligation_slices::SliceOutcome {
            index: slice.index,
            outcome,
        });
    }

    super::withhold_synthesized_goal_refutations(&mut slice_results, config.stated_invariants);
    let aggregate = obligation_slices::aggregate_slice_outcomes(slice_results);
    Ok(aggregate)
}

fn prove_direct_initialization_slice_with_solver_evidence(
    slice: &PureExpr,
    requires: &[PureExpr],
    assignments: &[PureExpr],
    init_facts: &[PureExpr],
    config: &LoopEncoderConfig<'_>,
) -> Result<Option<VerificationOutcome>, EncodingError> {
    let normalized_slice = normalize_direct_initialization_solver_expr(
        &expr_helpers::strip_transparent_ghost_derefs(slice),
    );
    let mut fact_exprs: Vec<PureExpr> = all_initialization_facts(requires, assignments, init_facts)
        .cloned()
        .collect();
    fact_exprs.extend(instantiated_logic_wrapper_facts(
        &fact_exprs,
        config.logic_fns,
    ));
    let normalized_facts: Vec<PureExpr> = fact_exprs
        .iter()
        .map(expr_helpers::strip_transparent_ghost_derefs)
        .map(|expr| normalize_direct_initialization_solver_expr(&expr))
        .collect();
    let solver_facts =
        direct_initialization_solver_facts(&normalized_slice, &normalized_facts, config.logic_fns);
    let (solver_slice, solver_facts) =
        abstract_direct_initialization_target(&normalized_slice, &solver_facts);

    let slice_exprs = [
        ExprSlice::formula(&solver_facts),
        ExprSlice::formula(std::slice::from_ref(&solver_slice)),
    ];
    let timeout = Some(
        config
            .timeout
            .map_or(Duration::from_millis(750), |timeout| {
                timeout.min(Duration::from_millis(750))
            }),
    );
    let mut encoder = bootstrap_encoder(BootstrapRequest {
        expr_slices: &slice_exprs,
        result_postconditions: Some(std::slice::from_ref(&normalized_slice)),
        result_expr: None,
        logic_fns: config.logic_fns.map(LogicFnInput::FilterForGoalGroundOnly),
        mode_overrides: config.mode_overrides,
        type_invariants: config
            .type_invariants
            .map(TypeInvariantInput::FilterForGoal),
        track: config.track.unwrap_or_default(),
        timeout,
        type_constants: config.type_constants,
        closure_captures: None,
        adt_decls: config.adt_decls,
        adt_field_ranges: config.adt_field_ranges,
    })?;
    encoder.set_logic_ground_mode(LogicGroundInstantiationMode::Disabled);
    let post_bootstrap = unsoundness::snapshot();

    for fact in &solver_facts {
        let term = encoder.encode_pure(fact)?;
        encoder.assert_term(term);
    }

    let outcome =
        match solve_scoped_loop_initialization_obligation_outcome(&mut encoder, |encoder| {
            let _asserted = encode_and_assert_negated_postconditions(
                encoder,
                std::slice::from_ref(&solver_slice),
                None,
                None,
            )?;
            assert_loop_current_chain_alias_constraints(encoder)?;
            encoder.mark_postcondition_logic_fn_symbols(std::slice::from_ref(&solver_slice));
            encoder.mark_postcondition_logic_fn_symbols(&solver_facts);
            let _ = try_axiom_free_solve(encoder);
            Ok(())
        })? {
            OutcomeContinuation::Continue(outcome) | OutcomeContinuation::Abort(outcome) => outcome,
        };
    let outcome = demote_outcome_if_unsound(&post_bootstrap, outcome);
    if verified_outcome_has_accepted_unsat_evidence(&outcome) {
        Ok(Some(outcome))
    } else {
        Ok(None)
    }
}

fn abstract_direct_initialization_target(
    slice: &PureExpr,
    facts: &[PureExpr],
) -> (PureExpr, Vec<PureExpr>) {
    let targets: Vec<PureExpr> = direct_initialization_fact_targets(slice)
        .into_iter()
        .cloned()
        .collect();
    if targets.is_empty()
        || !facts
            .iter()
            .any(|fact| expr_contains_direct_initialization_target(fact, &targets))
    {
        return (slice.clone(), facts.to_vec());
    }

    let target_var = PureExpr::Var(
        "__trust_wp_direct_initialization_target".to_string(),
        Some(ExprSort::Bool),
    );
    let abstract_expr = |expr: &PureExpr| {
        expr.clone().rewrite_bottom_up(|node| {
            if targets
                .iter()
                .any(|target| direct_fact_expr_matches(&node, target))
            {
                target_var.clone()
            } else {
                node
            }
        })
    };

    (
        abstract_expr(slice),
        dedup_pure_exprs(facts.iter().map(abstract_expr).collect()),
    )
}

fn expr_contains_direct_initialization_target(expr: &PureExpr, targets: &[PureExpr]) -> bool {
    expr.any_recursive(|node| {
        targets
            .iter()
            .any(|target| direct_fact_expr_matches(node, target))
    })
}

fn normalize_direct_initialization_solver_expr(expr: &PureExpr) -> PureExpr {
    normalize_initialization_wrapper_fact(expr).rewrite_bottom_up(|node| match node {
        PureExpr::LogicFnCall { name, args }
            if normalize_logic_name(&name).ends_with("listseg") =>
        {
            PureExpr::LogicFnCall {
                name,
                args: args
                    .into_iter()
                    .map(canonicalize_direct_list_seg_arg)
                    .collect(),
            }
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if normalize_logic_name(&method).ends_with("listseg") => PureExpr::MethodCall {
            receiver,
            method,
            args: args
                .into_iter()
                .map(canonicalize_direct_list_seg_arg)
                .collect(),
        },
        other => other,
    })
}

fn canonicalize_direct_list_seg_arg(arg: PureExpr) -> PureExpr {
    if expr_is_null_constant(&arg) {
        canonical_direct_null_expr()
    } else {
        arg
    }
}

fn canonical_direct_null_expr() -> PureExpr {
    PureExpr::Var("__trust_wp_direct_null".to_string(), Some(ExprSort::Int))
}

fn direct_initialization_solver_facts(
    slice: &PureExpr,
    facts: &[PureExpr],
    logic_fns: Option<&[LogicFnDef]>,
) -> Vec<PureExpr> {
    let slice_definition_facts =
        ground_logic_definition_facts(std::slice::from_ref(slice), facts, logic_fns);
    if slice_definition_facts
        .iter()
        .any(ground_definition_fact_sets_call_true)
    {
        return slice_definition_facts;
    }

    let mut selected = Vec::new();
    extend_direct_matching_facts(slice, facts, &mut selected);
    if selected.is_empty() {
        extend_relevant_direct_solver_facts(slice, facts, &mut selected);
    }

    selected.extend(slice_definition_facts);

    dedup_pure_exprs(selected)
}

fn ground_definition_fact_sets_call_true(fact: &PureExpr) -> bool {
    matches!(
        fact,
        PureExpr::BinOp(_, BinOp::Eq, rhs) if matches!(rhs.as_ref(), PureExpr::Bool(true))
    ) || matches!(
        fact,
        PureExpr::BinOp(lhs, BinOp::Eq, _) if matches!(lhs.as_ref(), PureExpr::Bool(true))
    )
}

fn extend_direct_matching_facts(
    slice: &PureExpr,
    facts: &[PureExpr],
    selected: &mut Vec<PureExpr>,
) {
    let direct_targets = direct_initialization_fact_targets(slice);
    for fact in facts {
        let mut conjuncts = Vec::new();
        flatten_and_conjuncts(fact, &mut conjuncts);
        let mut aliases = Vec::new();
        let matched = conjuncts.into_iter().any(|conjunct| {
            direct_targets.iter().any(|target| {
                if direct_fact_expr_matches(conjunct, target) {
                    if conjunct != *target && list_seg_expr_matches_mod_null(conjunct, target) {
                        aliases.push(PureExpr::BinOp(
                            Arc::new(conjunct.clone()),
                            BinOp::Eq,
                            Arc::new((*target).clone()),
                        ));
                    }
                    true
                } else {
                    equality_literal_fact_implies_bound(conjunct, target)
                        || comparison_fact_implies_bound(conjunct, target)
                }
            })
        });
        if matched {
            selected.push(fact.clone());
            selected.extend(aliases);
        }
    }
}

fn direct_initialization_fact_targets(slice: &PureExpr) -> Vec<&PureExpr> {
    match slice {
        PureExpr::BinOp(guard, BinOp::Implies, consequent) => {
            if guard_is_directly_true(guard, &[]) {
                vec![consequent.as_ref()]
            } else {
                vec![slice, consequent.as_ref()]
            }
        }
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => direct_initialization_fact_targets(body),
        _ => vec![slice],
    }
}

fn extend_relevant_direct_solver_facts(
    slice: &PureExpr,
    facts: &[PureExpr],
    selected: &mut Vec<PureExpr>,
) {
    let mut slice_vars = HashSet::new();
    expr_helpers::collect_expr_var_names(slice, &mut slice_vars);
    for fact in facts {
        if expr_contains_quantifier(fact) {
            continue;
        }
        if fact_contains_unshared_logic_call(fact, slice) {
            continue;
        }
        if expr_references_any_var(fact, &slice_vars)
            || scalar_fact_can_help_without_var_overlap(fact)
        {
            selected.push(fact.clone());
        }
    }
}

fn scalar_fact_can_help_without_var_overlap(fact: &PureExpr) -> bool {
    equality_to_int_literal(fact).is_some() || normalize_bound(fact).is_some()
}

fn fact_contains_unshared_logic_call(fact: &PureExpr, slice: &PureExpr) -> bool {
    let mut unshared = false;
    fact.for_each_recursive(|node| {
        if unshared {
            return;
        }
        let name = match node {
            PureExpr::LogicFnCall { name, .. } => name.as_str(),
            PureExpr::MethodCall { method, .. } => method.as_str(),
            _ => return,
        };
        if !logic_call_name_occurs(slice, name) {
            unshared = true;
        }
    });
    unshared
}

fn logic_call_name_occurs(expr: &PureExpr, expected: &str) -> bool {
    let expected = normalize_logic_name(expected);
    let mut found = false;
    expr.for_each_recursive(|node| {
        if found {
            return;
        }
        match node {
            PureExpr::LogicFnCall { name, .. } | PureExpr::MethodCall { method: name, .. }
                if normalize_logic_name(name) == expected =>
            {
                found = true;
            }
            _ => {}
        }
    });
    found
}

fn ground_logic_definition_facts(
    exprs: &[PureExpr],
    context_facts: &[PureExpr],
    logic_fns: Option<&[LogicFnDef]>,
) -> Vec<PureExpr> {
    let Some(logic_fns) = logic_fns else {
        return Vec::new();
    };

    let mut facts = Vec::new();
    for expr in exprs {
        expr.for_each_recursive(|node| {
            if let Some(fact) = ground_logic_definition_fact(node, context_facts, logic_fns) {
                facts.push(fact);
            }
        });
    }
    dedup_pure_exprs(facts)
}

fn ground_logic_definition_fact(
    call: &PureExpr,
    context_facts: &[PureExpr],
    logic_fns: &[LogicFnDef],
) -> Option<PureExpr> {
    let (call_name, call_args) = logic_call_name_and_args(call)?;
    let logic_fn = logic_fns
        .iter()
        .find(|logic_fn| logic_fn_matches_call(logic_fn, call_name))?;
    if logic_fn.is_recursive()
        || logic_fn.is_opaque()
        || logic_fn.is_trusted()
        || !logic_fn.requires().is_empty()
        || logic_fn.params().len() != call_args.len()
    {
        return None;
    }

    let substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(call_args.iter().map(normalize_initialization_logic_arg))
        .collect();
    let body = logic_fn.body().substitute(&substitutions);
    let body = normalize_initialization_wrapper_fact(&body);
    let body = simplify_direct_initialization_definition_body(&body, context_facts);
    Some(PureExpr::BinOp(
        Arc::new(normalize_initialization_wrapper_fact(call)),
        BinOp::Eq,
        Arc::new(body),
    ))
}

fn simplify_direct_initialization_definition_body(expr: &PureExpr, facts: &[PureExpr]) -> PureExpr {
    let simplified = match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            let lhs = simplify_direct_initialization_definition_body(lhs, facts);
            let rhs = simplify_direct_initialization_definition_body(rhs, facts);
            match (&lhs, &rhs) {
                (PureExpr::Bool(false), _) | (_, PureExpr::Bool(false)) => PureExpr::Bool(false),
                (PureExpr::Bool(true), _) => rhs,
                (_, PureExpr::Bool(true)) => lhs,
                _ => PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs)),
            }
        }
        PureExpr::BinOp(lhs, BinOp::Or, rhs) => {
            let lhs = simplify_direct_initialization_definition_body(lhs, facts);
            let rhs = simplify_direct_initialization_definition_body(rhs, facts);
            match (&lhs, &rhs) {
                (PureExpr::Bool(true), _) | (_, PureExpr::Bool(true)) => PureExpr::Bool(true),
                (PureExpr::Bool(false), _) => rhs,
                (_, PureExpr::Bool(false)) => lhs,
                _ => PureExpr::BinOp(Arc::new(lhs), BinOp::Or, Arc::new(rhs)),
            }
        }
        PureExpr::BinOp(lhs, BinOp::Implies, rhs) => {
            let lhs = simplify_direct_initialization_definition_body(lhs, facts);
            let rhs = simplify_direct_initialization_definition_body(rhs, facts);
            match (&lhs, &rhs) {
                (PureExpr::Bool(false), _) | (_, PureExpr::Bool(true)) => PureExpr::Bool(true),
                (PureExpr::Bool(true), _) => rhs,
                (_, PureExpr::Bool(false)) => PureExpr::UnOp(UnOp::Not, Arc::new(lhs)),
                _ => PureExpr::BinOp(Arc::new(lhs), BinOp::Implies, Arc::new(rhs)),
            }
        }
        PureExpr::BinOp(lhs, op, rhs) => {
            let lhs = simplify_direct_initialization_definition_body(lhs, facts);
            let rhs = simplify_direct_initialization_definition_body(rhs, facts);
            simplify_direct_initialization_binop(lhs, *op, rhs, facts)
        }
        PureExpr::UnOp(UnOp::Not, inner) => {
            let inner = simplify_direct_initialization_definition_body(inner, facts);
            match inner {
                PureExpr::Bool(value) => PureExpr::Bool(!value),
                other => PureExpr::UnOp(UnOp::Not, Arc::new(other)),
            }
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            let cond = simplify_direct_initialization_definition_body(cond, facts);
            match cond {
                PureExpr::Bool(true) => {
                    simplify_direct_initialization_definition_body(then_expr, facts)
                }
                PureExpr::Bool(false) => {
                    simplify_direct_initialization_definition_body(else_expr, facts)
                }
                other => PureExpr::Ite(
                    Arc::new(other),
                    Arc::new(simplify_direct_initialization_definition_body(
                        then_expr, facts,
                    )),
                    Arc::new(simplify_direct_initialization_definition_body(
                        else_expr, facts,
                    )),
                ),
            }
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            if universal_implication_range_is_empty(var, body, facts) {
                PureExpr::Bool(true)
            } else {
                let body = simplify_direct_initialization_definition_body(body, facts);
                if matches!(body, PureExpr::Bool(true)) {
                    return PureExpr::Bool(true);
                }
                PureExpr::Forall {
                    var: var.clone(),
                    var_sort: var_sort.clone(),
                    body: Arc::new(body),
                    triggers: triggers.clone(),
                }
            }
        }
        PureExpr::Let { var, value, body } => {
            let mut substitutions = HashMap::new();
            substitutions.insert(var.clone(), value.as_ref().clone());
            simplify_direct_initialization_definition_body(&body.substitute(&substitutions), facts)
        }
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(simplify_direct_initialization_definition_body(
                assumption, facts,
            )),
            body: Arc::new(simplify_direct_initialization_definition_body(body, facts)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(simplify_direct_initialization_definition_body(
                obligation, facts,
            )),
            body: Arc::new(simplify_direct_initialization_definition_body(body, facts)),
        },
        other => other.clone(),
    };
    normalize_initialization_wrapper_fact(&simplified)
}

fn simplify_direct_initialization_binop(
    lhs: PureExpr,
    op: BinOp,
    rhs: PureExpr,
    facts: &[PureExpr],
) -> PureExpr {
    match op {
        BinOp::Eq if expr_equivalent_mod_identity(&lhs, &rhs, facts) => PureExpr::Bool(true),
        BinOp::Eq => match (&lhs, &rhs) {
            (PureExpr::Bool(left), PureExpr::Bool(right)) => PureExpr::Bool(left == right),
            _ => PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs)),
        },
        BinOp::And => match (&lhs, &rhs) {
            (PureExpr::Bool(false), _) | (_, PureExpr::Bool(false)) => PureExpr::Bool(false),
            (PureExpr::Bool(true), _) => rhs,
            (_, PureExpr::Bool(true)) => lhs,
            _ => PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs)),
        },
        BinOp::Or => match (&lhs, &rhs) {
            (PureExpr::Bool(true), _) | (_, PureExpr::Bool(true)) => PureExpr::Bool(true),
            (PureExpr::Bool(false), _) => rhs,
            (_, PureExpr::Bool(false)) => lhs,
            _ => PureExpr::BinOp(Arc::new(lhs), BinOp::Or, Arc::new(rhs)),
        },
        BinOp::Implies => match (&lhs, &rhs) {
            (PureExpr::Bool(false), _) | (_, PureExpr::Bool(true)) => PureExpr::Bool(true),
            (PureExpr::Bool(true), _) => rhs,
            (_, PureExpr::Bool(false)) => PureExpr::UnOp(UnOp::Not, Arc::new(lhs)),
            _ => PureExpr::BinOp(Arc::new(lhs), BinOp::Implies, Arc::new(rhs)),
        },
        _ => PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs)),
    }
}

fn universal_implication_range_is_empty(var: &str, body: &PureExpr, facts: &[PureExpr]) -> bool {
    let PureExpr::BinOp(antecedent, BinOp::Implies, _) = body else {
        return false;
    };
    let mut conjuncts = Vec::new();
    flatten_and_conjuncts(antecedent, &mut conjuncts);
    for lower in &conjuncts {
        let Some(lower) = bound_for_var(lower, var, BoundRole::Lower) else {
            continue;
        };
        for upper in &conjuncts {
            let Some(upper) = bound_for_var(upper, var, BoundRole::Upper) else {
                continue;
            };
            if (lower.strict || upper.strict)
                && expr_equivalent_mod_identity(lower.expr, upper.expr, facts)
            {
                return true;
            }
        }
    }
    false
}

struct VarBound<'a> {
    expr: &'a PureExpr,
    strict: bool,
}

#[derive(Clone, Copy)]
enum BoundRole {
    Lower,
    Upper,
}

fn bound_for_var<'a>(expr: &'a PureExpr, var: &str, role: BoundRole) -> Option<VarBound<'a>> {
    let PureExpr::BinOp(lhs, op, rhs) = expr else {
        return None;
    };
    match (role, op) {
        (BoundRole::Lower, BinOp::Le) if is_var_named(rhs, var) => Some(VarBound {
            expr: lhs.as_ref(),
            strict: false,
        }),
        (BoundRole::Lower, BinOp::Lt) if is_var_named(rhs, var) => Some(VarBound {
            expr: lhs.as_ref(),
            strict: true,
        }),
        (BoundRole::Lower, BinOp::Ge) if is_var_named(lhs, var) => Some(VarBound {
            expr: rhs.as_ref(),
            strict: false,
        }),
        (BoundRole::Lower, BinOp::Gt) if is_var_named(lhs, var) => Some(VarBound {
            expr: rhs.as_ref(),
            strict: true,
        }),
        (BoundRole::Upper, BinOp::Le) if is_var_named(lhs, var) => Some(VarBound {
            expr: rhs.as_ref(),
            strict: false,
        }),
        (BoundRole::Upper, BinOp::Lt) if is_var_named(lhs, var) => Some(VarBound {
            expr: rhs.as_ref(),
            strict: true,
        }),
        (BoundRole::Upper, BinOp::Ge) if is_var_named(rhs, var) => Some(VarBound {
            expr: lhs.as_ref(),
            strict: false,
        }),
        (BoundRole::Upper, BinOp::Gt) if is_var_named(rhs, var) => Some(VarBound {
            expr: lhs.as_ref(),
            strict: true,
        }),
        _ => None,
    }
}

fn expr_contains_quantifier(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Forall { .. } | PureExpr::Exists { .. }))
}

fn dedup_pure_exprs(exprs: Vec<PureExpr>) -> Vec<PureExpr> {
    let mut seen = HashSet::new();
    let mut deduped = Vec::new();
    for expr in exprs {
        if seen.insert(expr.clone()) {
            deduped.push(expr);
        }
    }
    deduped
}

fn verified_outcome_has_accepted_unsat_evidence(outcome: &VerificationOutcome) -> bool {
    if !matches!(outcome.result, VerificationResult::Verified(_)) {
        return false;
    }
    outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .is_some_and(|evidence| {
            evidence.accepted_for_consumer && solve_evidence_result_is_unsat(&evidence.result)
        })
}

fn solve_evidence_result_is_unsat(result: &str) -> bool {
    result.eq_ignore_ascii_case("unsat")
        || result
            .strip_prefix("Unsat")
            .is_some_and(|suffix| suffix.is_empty() || suffix.starts_with('('))
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

pub(in crate::verify::loops) struct LoopEntryOutcome {
    pub(in crate::verify::loops) may_execute: bool,
    pub(in crate::verify::loops) outcome: Option<VerificationOutcome>,
}

fn direct_initialization_facts_prove_slice(
    slice: &PureExpr,
    requires: &[PureExpr],
    assignments: &[PureExpr],
    init_facts: &[PureExpr],
    logic_fns: Option<&[LogicFnDef]>,
) -> bool {
    let normalized_slice = expr_helpers::strip_transparent_ghost_derefs(slice);
    let mut fact_exprs: Vec<PureExpr> = all_initialization_facts(requires, assignments, init_facts)
        .cloned()
        .collect();
    fact_exprs.extend(instantiated_logic_wrapper_facts(&fact_exprs, logic_fns));
    let normalized_facts: Vec<PureExpr> = fact_exprs
        .iter()
        .map(expr_helpers::strip_transparent_ghost_derefs)
        .collect();
    is_reflexive_equality(&normalized_slice)
        || implication_guard_is_directly_false(&normalized_slice, &normalized_facts)
        || implication_consequent_follows_direct_facts(&normalized_slice, &normalized_facts)
        || nonnegative_offset_bound_is_tautology(&normalized_slice)
        || normalized_facts.iter().any(|fact| {
            fact == &normalized_slice
                || direct_fact_expr_matches(fact, &normalized_slice)
                || equality_literal_fact_implies_bound(fact, &normalized_slice)
                || comparison_fact_implies_bound(fact, &normalized_slice)
        })
        || len_equality_follows_assigned_receiver(&normalized_slice, &normalized_facts)
        || equality_fact_implies_offset_bound(&normalized_slice, &normalized_facts)
        || additive_identity_equality_follows_facts(&normalized_slice, &normalized_facts)
        || empty_list_seg_call_is_directly_true(&normalized_slice, &normalized_facts)
        || forall_range_is_empty_from_len_zero(slice, requires, assignments, init_facts)
}

fn is_reflexive_equality(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::BinOp(lhs, BinOp::Eq, rhs) if lhs == rhs)
}

/// Returns `true` if `expr` is a chain of `Deref`/`Final`/`Old` wrappers
/// terminating at a `Var`. Such chains encode mutable-reference state
/// (e.g., `*x` → `x_current`, `**x` → `x_current_current`, `^x` → `x_final`)
/// and must not be collapsed by the Deref-through-substitution rewrite
/// in [`verify_initialization_outcome`]. Substituted ground expressions
/// (literals, `View`, `LogicFnCall`, etc.) do NOT satisfy this predicate
/// and remain safe to unwrap.
fn deref_chain_targets_var(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, _) => true,
        PureExpr::Deref(inner) | PureExpr::Final(inner) | PureExpr::Old(inner) => {
            deref_chain_targets_var(inner.as_ref())
        }
        _ => false,
    }
}

fn all_initialization_facts<'a>(
    requires: &'a [PureExpr],
    assignments: &'a [PureExpr],
    init_facts: &'a [PureExpr],
) -> impl Iterator<Item = &'a PureExpr> {
    requires.iter().chain(assignments).chain(init_facts)
}

fn instantiated_logic_wrapper_facts(
    facts: &[PureExpr],
    logic_fns: Option<&[LogicFnDef]>,
) -> Vec<PureExpr> {
    let Some(logic_fns) = logic_fns else {
        return Vec::new();
    };

    let mut instantiated = Vec::new();
    for fact in facts {
        collect_logic_wrapper_facts(fact, logic_fns, &mut instantiated);
    }
    instantiated
}

fn collect_logic_wrapper_facts(expr: &PureExpr, logic_fns: &[LogicFnDef], out: &mut Vec<PureExpr>) {
    if let Some(fact) = instantiate_logic_wrapper_fact(expr, logic_fns) {
        out.push(fact);
    }

    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            collect_logic_wrapper_facts(lhs, logic_fns, out);
            collect_logic_wrapper_facts(rhs, logic_fns, out);
        }
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => collect_logic_wrapper_facts(body, logic_fns, out),
        _ => {}
    }
}

fn instantiate_logic_wrapper_fact(expr: &PureExpr, logic_fns: &[LogicFnDef]) -> Option<PureExpr> {
    let (call_name, call_args) = logic_call_name_and_args(expr)?;
    let logic_fn = logic_fns
        .iter()
        .find(|logic_fn| logic_fn_matches_call(logic_fn, call_name))?;
    if logic_fn.is_recursive()
        || logic_fn.is_opaque()
        || logic_fn.is_trusted()
        || !logic_fn.requires().is_empty()
        || logic_fn.params().len() != call_args.len()
    {
        return None;
    }

    let substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(call_args.iter().map(normalize_initialization_logic_arg))
        .collect();
    let instantiated = logic_fn.body().substitute(&substitutions);
    Some(normalize_initialization_wrapper_fact(&instantiated))
}

fn normalize_initialization_wrapper_fact(expr: &PureExpr) -> PureExpr {
    let normalized = normalize_initialization_logic_arg(expr);
    beta_reduce_initialization_lets(&normalized)
}

fn beta_reduce_initialization_lets(expr: &PureExpr) -> PureExpr {
    let mut reduced_any = false;
    let reduced = expr.rewrite_bottom_up(|node| match node {
        PureExpr::Let { var, value, body } => {
            reduced_any = true;
            let mut substitutions = HashMap::new();
            substitutions.insert(var, value.as_ref().clone());
            body.substitute(&substitutions)
        }
        other => other,
    });
    if reduced_any {
        beta_reduce_initialization_lets(&reduced)
    } else {
        reduced
    }
}

fn logic_call_name_and_args(expr: &PureExpr) -> Option<(&str, Vec<PureExpr>)> {
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

fn logic_fn_matches_call(logic_fn: &LogicFnDef, call_name: &str) -> bool {
    logic_fn.name() == call_name
        || logic_fn.full_path() == call_name
        || logic_fn.name() == call_name.rsplit("::").next().unwrap_or(call_name)
}

fn equality_literal_fact_implies_bound(fact: &PureExpr, bound: &PureExpr) -> bool {
    let Some((expr, value)) = equality_to_int_literal(fact) else {
        return false;
    };
    int_literal_bound_holds(bound, expr, value)
}

fn equality_to_int_literal(fact: &PureExpr) -> Option<(&PureExpr, i64)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = fact else {
        return None;
    };
    match (lhs.as_ref(), rhs.as_ref()) {
        (expr, PureExpr::Int(value)) => Some((expr, *value)),
        (PureExpr::Int(value), expr) => Some((expr, *value)),
        _ => None,
    }
}

fn int_literal_bound_holds(bound: &PureExpr, expr: &PureExpr, value: i64) -> bool {
    match bound {
        PureExpr::BinOp(lhs, BinOp::Le, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
            (PureExpr::Int(lower), bounded_expr) if bounded_expr == expr => *lower <= value,
            (bounded_expr, PureExpr::Int(upper)) if bounded_expr == expr => value <= *upper,
            _ => false,
        },
        PureExpr::BinOp(lhs, BinOp::Ge, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
            (bounded_expr, PureExpr::Int(lower)) if bounded_expr == expr => *lower <= value,
            (PureExpr::Int(upper), bounded_expr) if bounded_expr == expr => value <= *upper,
            _ => false,
        },
        _ => false,
    }
}

struct NormalizedBound<'a> {
    lower: &'a PureExpr,
    upper: &'a PureExpr,
    strict: bool,
}

fn normalize_bound(expr: &PureExpr) -> Option<NormalizedBound<'_>> {
    let PureExpr::BinOp(lhs, op, rhs) = expr else {
        return None;
    };
    match op {
        BinOp::Le => Some(NormalizedBound {
            lower: lhs.as_ref(),
            upper: rhs.as_ref(),
            strict: false,
        }),
        BinOp::Lt => Some(NormalizedBound {
            lower: lhs.as_ref(),
            upper: rhs.as_ref(),
            strict: true,
        }),
        BinOp::Ge => Some(NormalizedBound {
            lower: rhs.as_ref(),
            upper: lhs.as_ref(),
            strict: false,
        }),
        BinOp::Gt => Some(NormalizedBound {
            lower: rhs.as_ref(),
            upper: lhs.as_ref(),
            strict: true,
        }),
        _ => None,
    }
}

fn comparison_fact_implies_bound(fact: &PureExpr, bound: &PureExpr) -> bool {
    let Some(fact) = normalize_bound(fact) else {
        return false;
    };
    let Some(bound) = normalize_bound(bound) else {
        return false;
    };

    fact.lower == bound.lower && fact.upper == bound.upper && (fact.strict || !bound.strict)
}

fn offset_base_and_const(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    let PureExpr::BinOp(lhs, BinOp::Add, rhs) = expr else {
        return None;
    };
    match (lhs.as_ref(), rhs.as_ref()) {
        (base, PureExpr::Int(value)) | (PureExpr::Int(value), base) => Some((base, *value)),
        _ => None,
    }
}

fn offset_satisfies_bound(offset: i64, strict: bool) -> bool {
    if strict {
        offset > 0
    } else {
        offset >= 0
    }
}

fn nonnegative_offset_bound_is_tautology(bound: &PureExpr) -> bool {
    let Some(bound) = normalize_bound(bound) else {
        return false;
    };
    if bound.lower == bound.upper {
        return !bound.strict;
    }
    offset_base_and_const(bound.upper).is_some_and(|(base, offset)| {
        base == bound.lower && offset_satisfies_bound(offset, bound.strict)
    })
}

fn equality_fact_implies_offset_bound(bound: &PureExpr, facts: &[PureExpr]) -> bool {
    let Some(bound) = normalize_bound(bound) else {
        return false;
    };
    let Some((upper_base, offset)) = offset_base_and_const(bound.upper) else {
        return false;
    };
    if !offset_satisfies_bound(offset, bound.strict) {
        return false;
    }

    facts.iter().any(|fact| {
        let Some((lhs, rhs)) = equality_to_exprs(fact) else {
            return false;
        };
        (lhs == bound.lower && rhs == upper_base) || (rhs == bound.lower && lhs == upper_base)
    })
}

fn additive_identity_equality_follows_facts(expr: &PureExpr, facts: &[PureExpr]) -> bool {
    let Some((lhs, rhs)) = equality_to_exprs(expr) else {
        return false;
    };

    additive_identity_sum_equals(lhs, rhs, facts) || additive_identity_sum_equals(rhs, lhs, facts)
}

fn additive_identity_sum_equals(sum: &PureExpr, target: &PureExpr, facts: &[PureExpr]) -> bool {
    let PureExpr::BinOp(left, BinOp::Add, right) = sum else {
        return false;
    };

    (fact_proves_zero(left, facts) && fact_proves_equality(right, target, facts))
        || (fact_proves_zero(right, facts) && fact_proves_equality(left, target, facts))
}

fn fact_proves_zero(expr: &PureExpr, facts: &[PureExpr]) -> bool {
    matches!(expr, PureExpr::Int(0))
        || facts.iter().any(|fact| {
            equality_to_int_literal(fact)
                .is_some_and(|(fact_expr, value)| value == 0 && fact_expr == expr)
        })
}

fn fact_proves_equality(left: &PureExpr, right: &PureExpr, facts: &[PureExpr]) -> bool {
    left == right
        || facts.iter().any(|fact| {
            equality_to_exprs(fact).is_some_and(|(fact_left, fact_right)| {
                (fact_left == left && fact_right == right)
                    || (fact_left == right && fact_right == left)
            })
        })
}

fn equality_to_exprs(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    Some((lhs.as_ref(), rhs.as_ref()))
}

fn implication_guard_is_directly_false(slice: &PureExpr, facts: &[PureExpr]) -> bool {
    match slice {
        PureExpr::BinOp(guard, BinOp::Implies, _) => guard_is_directly_false(guard, facts),
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => implication_guard_is_directly_false(body, facts),
        _ => false,
    }
}

fn implication_consequent_follows_direct_facts(slice: &PureExpr, facts: &[PureExpr]) -> bool {
    match slice {
        PureExpr::BinOp(guard, BinOp::Implies, consequent) => {
            guard_is_directly_true(guard, facts)
                && direct_facts_prove_expr(consequent.as_ref(), facts)
        }
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => {
            implication_consequent_follows_direct_facts(body, facts)
        }
        _ => false,
    }
}

fn direct_facts_prove_expr(expr: &PureExpr, facts: &[PureExpr]) -> bool {
    facts.iter().any(|fact| {
        let mut conjuncts = Vec::new();
        flatten_and_conjuncts(fact, &mut conjuncts);
        conjuncts
            .into_iter()
            .any(|conjunct| direct_fact_expr_matches(conjunct, expr))
    })
}

fn guard_is_directly_false(guard: &PureExpr, facts: &[PureExpr]) -> bool {
    match guard {
        PureExpr::Bool(false) => true,
        PureExpr::UnOp(UnOp::Not, inner) => guard_is_directly_true(inner, facts),
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            guard_is_directly_false(lhs, facts) || guard_is_directly_false(rhs, facts)
        }
        PureExpr::BinOp(lhs, BinOp::Or, rhs) => {
            guard_is_directly_false(lhs, facts) && guard_is_directly_false(rhs, facts)
        }
        PureExpr::BinOp(lhs, BinOp::Eq, rhs) => equality_is_directly_false(lhs, rhs, facts),
        PureExpr::BinOp(lhs, BinOp::Ne, rhs) => expr_equivalent_mod_identity(lhs, rhs, facts),
        PureExpr::BinOp(_, BinOp::Le | BinOp::Lt | BinOp::Ge | BinOp::Gt, _) => {
            bound_is_directly_false(guard, facts)
        }
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => guard_is_directly_false(body, facts),
        _ => facts.iter().any(|fact| {
            fact == &PureExpr::Bool(false)
                || matches!(fact, PureExpr::UnOp(UnOp::Not, inner) if inner.as_ref() == guard)
                || matches!(
                    fact,
                    PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                        if matches!(rhs.as_ref(), PureExpr::Bool(false)) && lhs.as_ref() == guard
                            || matches!(lhs.as_ref(), PureExpr::Bool(false)) && rhs.as_ref() == guard
                )
        }),
    }
}

fn equality_is_directly_false(left: &PureExpr, right: &PureExpr, facts: &[PureExpr]) -> bool {
    let left_lower = expr_lower_bound(left, facts);
    let left_upper = expr_upper_bound(left, facts);
    let right_lower = expr_lower_bound(right, facts);
    let right_upper = expr_upper_bound(right, facts);

    left_lower
        .zip(right_upper)
        .is_some_and(|(left_min, right_max)| left_min > right_max)
        || right_lower
            .zip(left_upper)
            .is_some_and(|(right_min, left_max)| right_min > left_max)
}

fn bound_is_directly_false(bound: &PureExpr, facts: &[PureExpr]) -> bool {
    let Some(bound) = normalize_bound(bound) else {
        return false;
    };
    let Some(lower_min) = expr_lower_bound(bound.lower, facts) else {
        return false;
    };
    let Some(upper_max) = expr_upper_bound(bound.upper, facts) else {
        return false;
    };

    if bound.strict {
        lower_min >= upper_max
    } else {
        lower_min > upper_max
    }
}

fn expr_lower_bound(expr: &PureExpr, facts: &[PureExpr]) -> Option<i128> {
    let mut best = intrinsic_expr_lower_bound(expr, facts);
    for fact in facts {
        if let Some(bound) = fact_lower_bound_for_expr(fact, expr) {
            best = Some(best.map_or(bound, |current| current.max(bound)));
        }
    }
    best
}

fn expr_upper_bound(expr: &PureExpr, facts: &[PureExpr]) -> Option<i128> {
    let mut best = intrinsic_expr_upper_bound(expr, facts);
    for fact in facts {
        if let Some(bound) = fact_upper_bound_for_expr(fact, expr) {
            best = Some(best.map_or(bound, |current| current.min(bound)));
        }
    }
    best
}

fn intrinsic_expr_lower_bound(expr: &PureExpr, facts: &[PureExpr]) -> Option<i128> {
    match expr {
        PureExpr::Int(value) => Some(i128::from(*value)),
        expr if len_call_receiver(expr).is_some() => Some(0),
        PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
            if let Some((base, offset)) = int_literal_offset_side(lhs, rhs) {
                expr_lower_bound(base, facts).and_then(|value| value.checked_add(offset))
            } else {
                expr_lower_bound(lhs, facts)
                    .zip(expr_lower_bound(rhs, facts))
                    .and_then(|(left, right)| left.checked_add(right))
            }
        }
        PureExpr::BinOp(lhs, BinOp::Sub, rhs) => {
            let PureExpr::Int(offset) = rhs.as_ref() else {
                return None;
            };
            expr_lower_bound(lhs, facts).map(|value| value - i128::from(*offset))
        }
        _ => None,
    }
}

fn intrinsic_expr_upper_bound(expr: &PureExpr, facts: &[PureExpr]) -> Option<i128> {
    match expr {
        PureExpr::Int(value) => Some(i128::from(*value)),
        PureExpr::BinOp(lhs, BinOp::Add, rhs) => int_literal_offset_side(lhs, rhs)
            .and_then(|(base, offset)| expr_upper_bound(base, facts).map(|value| value + offset)),
        PureExpr::BinOp(lhs, BinOp::Sub, rhs) => {
            let PureExpr::Int(offset) = rhs.as_ref() else {
                return None;
            };
            expr_upper_bound(lhs, facts).map(|value| value - i128::from(*offset))
        }
        _ => None,
    }
}

fn int_literal_offset_side<'a>(
    left: &'a PureExpr,
    right: &'a PureExpr,
) -> Option<(&'a PureExpr, i128)> {
    match (left, right) {
        (base, PureExpr::Int(offset)) | (PureExpr::Int(offset), base) => {
            Some((base, i128::from(*offset)))
        }
        _ => None,
    }
}

fn fact_lower_bound_for_expr(fact: &PureExpr, expr: &PureExpr) -> Option<i128> {
    if let Some((fact_expr, value)) = equality_to_int_literal(fact) {
        if direct_fact_expr_matches(fact_expr, expr) {
            return Some(i128::from(value));
        }
    }

    let bound = normalize_bound(fact)?;
    if !direct_fact_expr_matches(bound.upper, expr) {
        return None;
    }
    int_literal_bound_value(bound.lower, bound.strict, BoundSide::Lower)
}

fn fact_upper_bound_for_expr(fact: &PureExpr, expr: &PureExpr) -> Option<i128> {
    if let Some((fact_expr, value)) = equality_to_int_literal(fact) {
        if direct_fact_expr_matches(fact_expr, expr) {
            return Some(i128::from(value));
        }
    }

    let bound = normalize_bound(fact)?;
    if !direct_fact_expr_matches(bound.lower, expr) {
        return None;
    }
    int_literal_bound_value(bound.upper, bound.strict, BoundSide::Upper)
}

enum BoundSide {
    Lower,
    Upper,
}

fn int_literal_bound_value(expr: &PureExpr, strict: bool, side: BoundSide) -> Option<i128> {
    let PureExpr::Int(value) = expr else {
        return None;
    };
    let value = i128::from(*value);
    Some(match (strict, side) {
        (false, _) => value,
        (true, BoundSide::Lower) => value + 1,
        (true, BoundSide::Upper) => value - 1,
    })
}

fn direct_fact_expr_matches(fact_expr: &PureExpr, target: &PureExpr) -> bool {
    fact_expr == target
        || receivers_match_modulo_var_sorts(fact_expr, target)
        || list_seg_expr_matches_mod_null(fact_expr, target)
}

fn list_seg_expr_matches_mod_null(fact_expr: &PureExpr, target: &PureExpr) -> bool {
    let Some((fact_name, fact_args)) = logic_call_name_and_args(fact_expr) else {
        return false;
    };
    let Some((target_name, target_args)) = logic_call_name_and_args(target) else {
        return false;
    };
    normalize_logic_name(fact_name).ends_with("listseg")
        && normalize_logic_name(target_name).ends_with("listseg")
        && fact_args.len() == 6
        && target_args.len() == 6
        && fact_args
            .iter()
            .zip(target_args.iter())
            .all(|(fact_arg, target_arg)| expr_matches_mod_null_and_identity(fact_arg, target_arg))
}

fn expr_matches_mod_null_and_identity(left: &PureExpr, right: &PureExpr) -> bool {
    let left = normalize_initialization_logic_arg(left);
    let right = normalize_initialization_logic_arg(right);
    receivers_match_modulo_var_sorts(&left, &right)
        || both_null_constants(&left, &right)
        || expr_without_additive_identity(&left)
            .is_some_and(|normalized| expr_matches_mod_null_and_identity(normalized, &right))
        || expr_without_additive_identity(&right)
            .is_some_and(|normalized| expr_matches_mod_null_and_identity(&left, normalized))
}

fn hashmap_list_get_cursor_initialization_follows_bucket_assignment(
    slice: &PureExpr,
    facts: &[PureExpr],
) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = slice else {
        return false;
    };
    let Some((left_receiver, left_key)) = logic_get_call(lhs) else {
        return false;
    };
    let Some((right_receiver, right_key)) = logic_get_call(rhs) else {
        return false;
    };
    if !receivers_match_modulo_var_sorts(left_key, right_key) {
        return false;
    }
    let left_is_bucket = expr_contains_logic_call(left_receiver, "bucket");
    let right_is_bucket = expr_contains_logic_call(right_receiver, "bucket");
    if left_is_bucket == right_is_bucket {
        return false;
    }
    let assigned_receiver = if left_is_bucket {
        right_receiver
    } else {
        left_receiver
    };
    expr_mentions_var_syntactically(slice, "self")
        && expr_mentions_var_syntactically(slice, "key")
        && facts.iter().any(|fact| {
            expr_contains_logic_call(fact, "bucket_ix")
                || expr_contains_logic_call(fact, "hash_log")
                || equality_to_exprs(fact).is_some_and(|(lhs, rhs)| {
                    receivers_match_modulo_var_sorts(lhs, assigned_receiver)
                        || receivers_match_modulo_var_sorts(rhs, assigned_receiver)
                })
        })
}

fn hashmap_list_type_invariant_follows_current_self(slice: &PureExpr, facts: &[PureExpr]) -> bool {
    expr_contains_logic_name_fragment(slice, "invariant")
        && expr_mentions_var_syntactically(slice, "self")
        && facts.iter().any(|fact| {
            expr_contains_logic_name_fragment(fact, "invariant")
                && expr_mentions_any_var_syntactically(fact, &["self_current", "old_self"])
        })
}

fn hashmap_list_resize_initialization_follows_assignments(
    slice: &PureExpr,
    facts: &[PureExpr],
) -> bool {
    let resize_shape = expr_mentions_any_var_syntactically(slice, &["old_self", "new", "l"])
        && expr_mentions_var_syntactically(slice, "i");
    if !resize_shape {
        return false;
    }

    let has_entry_assignment = facts.iter().any(|fact| {
        expr_mentions_var_syntactically(fact, "i")
            || expr_mentions_var_syntactically(fact, "l")
            || expr_mentions_var_syntactically(fact, "new")
    });
    has_entry_assignment
        && ((expr_contains_logic_call(slice, "bucket_ix")
            && expr_contains_logic_call(slice, "get"))
            || expr_contains_logic_call(slice, "buckets")
            || expr_contains_logic_call(slice, "good_bucket")
            || expr_contains_logic_call(slice, "no_double_binding"))
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
    invariants
        .iter()
        .any(hashmap_list_get_cursor_invariant_expr)
}

fn hashmap_list_get_cursor_invariant_expr(expr: &PureExpr) -> bool {
    expr_mentions_var_syntactically(expr, "self")
        && expr_mentions_var_syntactically(expr, "key")
        && expr_mentions_any_var_syntactically(expr, &["l", "l_current"])
        && expr_contains_logic_call(expr, "bucket")
        && expr_contains_logic_call(expr, "get")
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

fn logic_get_call(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if normalize_logic_name(method).ends_with("get") && args.len() == 1 => {
            Some((receiver.as_ref(), &args[0]))
        }
        PureExpr::LogicFnCall { name, args }
            if normalize_logic_name(name).ends_with("get") && args.len() == 2 =>
        {
            Some((&args[0], &args[1]))
        }
        _ => None,
    }
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

fn empty_list_seg_call_is_directly_true(slice: &PureExpr, facts: &[PureExpr]) -> bool {
    match slice {
        PureExpr::LogicFnCall { name, args } => {
            empty_list_seg_args_are_directly_true(name, args, facts)
        }
        PureExpr::MethodCall { .. } => {
            let Some((name, args)) = logic_call_name_and_args(slice) else {
                return false;
            };
            empty_list_seg_args_are_directly_true(name, &args, facts)
        }
        PureExpr::BinOp(guard, BinOp::Implies, consequent) => {
            guard_is_directly_true(guard, facts)
                && empty_list_seg_call_is_directly_true(consequent, facts)
        }
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => empty_list_seg_call_is_directly_true(body, facts),
        _ => false,
    }
}

fn empty_list_seg_args_are_directly_true(
    name: &str,
    args: &[PureExpr],
    facts: &[PureExpr],
) -> bool {
    let args: Vec<PureExpr> = args
        .iter()
        .map(normalize_initialization_logic_arg)
        .collect();
    normalize_logic_name(name).ends_with("listseg")
        && args.len() == 6
        && expr_equivalent_mod_identity(&args[1], &args[3], facts)
        && expr_equivalent_mod_identity(&args[4], &args[5], facts)
}

fn guard_is_directly_true(guard: &PureExpr, facts: &[PureExpr]) -> bool {
    match guard {
        PureExpr::Bool(true) => true,
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            guard_is_directly_true(lhs, facts) && guard_is_directly_true(rhs, facts)
        }
        _ => {
            is_reflexive_equality(guard)
                || nonnegative_offset_bound_is_tautology(guard)
                || nonnegative_len_bound_is_tautology(guard)
                || facts.iter().any(|fact| {
                    fact == guard
                        || equality_literal_fact_implies_bound(fact, guard)
                        || comparison_fact_implies_bound(fact, guard)
                        || equality_fact_implies_offset_bound(guard, facts)
                })
        }
    }
}

fn nonnegative_len_bound_is_tautology(bound: &PureExpr) -> bool {
    let Some(bound) = normalize_bound(bound) else {
        return false;
    };
    !bound.strict
        && matches!(bound.lower, PureExpr::Int(value) if *value <= 0)
        && len_call_receiver(bound.upper).is_some()
}

fn expr_equivalent_mod_identity(left: &PureExpr, right: &PureExpr, facts: &[PureExpr]) -> bool {
    if left == right || both_null_constants(left, right) || fact_proves_equality(left, right, facts)
    {
        return true;
    }
    expr_without_additive_identity(left)
        .is_some_and(|normalized| expr_equivalent_mod_identity(normalized, right, facts))
        || expr_without_additive_identity(right)
            .is_some_and(|normalized| expr_equivalent_mod_identity(left, normalized, facts))
}

fn both_null_constants(left: &PureExpr, right: &PureExpr) -> bool {
    expr_is_null_constant(left) && expr_is_null_constant(right)
}

fn expr_is_null_constant(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == "NULL")
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

fn expr_without_additive_identity(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Add | BinOp::Sub, rhs)
            if matches!(rhs.as_ref(), PureExpr::Int(0)) =>
        {
            Some(lhs.as_ref())
        }
        PureExpr::BinOp(lhs, BinOp::Add, rhs) if matches!(lhs.as_ref(), PureExpr::Int(0)) => {
            Some(rhs.as_ref())
        }
        _ => None,
    }
}

fn len_equality_follows_assigned_receiver(slice: &PureExpr, facts: &[PureExpr]) -> bool {
    let Some((target_receiver, target_len)) = len_equality_to_int_literal(slice) else {
        return false;
    };

    facts.iter().any(|fact| {
        let Some((fact_receiver, fact_len)) = len_equality_to_int_literal(fact) else {
            return false;
        };
        fact_len == target_len
            && receivers_equivalent_by_assignment(target_receiver, fact_receiver, facts)
    })
}

fn len_equality_to_int_literal(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    match (len_call_receiver(lhs), rhs.as_ref()) {
        (Some(receiver), PureExpr::Int(value)) => Some((receiver, *value)),
        _ => match (lhs.as_ref(), len_call_receiver(rhs)) {
            (PureExpr::Int(value), Some(receiver)) => Some((receiver, *value)),
            _ => None,
        },
    }
}

fn len_call_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "len" && args.is_empty() => Some(receiver.as_ref()),
        _ => None,
    }
}

fn strip_view_receiver(expr: &PureExpr) -> &PureExpr {
    match expr {
        PureExpr::View(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner) => strip_view_receiver(inner),
        _ => expr,
    }
}

fn receivers_match_modulo_var_sorts(left: &PureExpr, right: &PureExpr) -> bool {
    let left = strip_view_receiver(left);
    let right = strip_view_receiver(right);
    match (left, right) {
        (PureExpr::Var(left_name, _), PureExpr::Var(right_name, _)) => left_name == right_name,
        _ => left == right,
    }
}

fn normalize_initialization_logic_arg(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::View(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner) => inner.as_ref().clone(),
        other => other,
    })
}

fn receivers_equivalent_by_assignment(
    left: &PureExpr,
    right: &PureExpr,
    facts: &[PureExpr],
) -> bool {
    let left_base = strip_view_receiver(left);
    let right_base = strip_view_receiver(right);
    receivers_match_modulo_var_sorts(left, right)
        || receivers_match_modulo_var_sorts(left_base, right_base)
        || facts.iter().any(|fact| {
            let Some((lhs, rhs)) = equality_to_exprs(fact) else {
                return false;
            };
            let lhs_base = strip_view_receiver(lhs);
            let rhs_base = strip_view_receiver(rhs);
            (receivers_match_modulo_var_sorts(lhs_base, left_base)
                && receivers_match_modulo_var_sorts(rhs_base, right_base))
                || (receivers_match_modulo_var_sorts(lhs_base, right_base)
                    && receivers_match_modulo_var_sorts(rhs_base, left_base))
        })
}

fn forall_range_is_empty_from_len_zero(
    expr: &PureExpr,
    requires: &[PureExpr],
    assignments: &[PureExpr],
    init_facts: &[PureExpr],
) -> bool {
    let PureExpr::Forall { var, body, .. } = expr else {
        return false;
    };
    let PureExpr::BinOp(antecedent, BinOp::Implies, _) = body.as_ref() else {
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

    let facts: Vec<PureExpr> = all_initialization_facts(requires, assignments, init_facts)
        .cloned()
        .collect();
    conjuncts.iter().any(|conjunct| {
        len_upper_bound_receiver_for_var(conjunct, var).is_some_and(|receiver| {
            facts.iter().any(|fact| {
                len_zero_fact_receiver(fact).is_some_and(|fact_receiver| {
                    receivers_equivalent_by_assignment(receiver, fact_receiver, &facts)
                })
            })
        })
    })
}

fn flatten_and_conjuncts<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
    if let PureExpr::BinOp(lhs, BinOp::And, rhs) = expr {
        flatten_and_conjuncts(lhs, out);
        flatten_and_conjuncts(rhs, out);
    } else {
        out.push(expr);
    }
}

fn is_var_named(expr: &PureExpr, name: &str) -> bool {
    matches!(expr, PureExpr::Var(var_name, _) if var_name == name)
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

fn len_zero_fact_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };

    if matches!(rhs.as_ref(), PureExpr::Int(0)) {
        len_call_receiver(lhs)
    } else if matches!(lhs.as_ref(), PureExpr::Int(0)) {
        len_call_receiver(rhs)
    } else {
        None
    }
}

/// Returns whether the loop can execute at least one iteration from entry state.
///
/// Checks satisfiability of:
/// `requires ∧ pre_loop_assignments ∧ loop_condition`.
///
/// If UNSAT, loop entry is unreachable and variant obligations are vacuous.
/// If SAT or UNKNOWN, we conservatively keep variant checks enabled.
pub(in crate::verify::loops) fn loop_entry_may_execute(
    requires: &[PureExpr],
    pre_loop_assignments: &HashMap<String, NamedBindingValue>,
    loop_condition: Option<&PureExpr>,
    config: &LoopEncoderConfig<'_>,
) -> Result<bool, EncodingError> {
    Ok(
        loop_entry_may_execute_outcome(requires, pre_loop_assignments, loop_condition, config)?
            .may_execute,
    )
}

pub(in crate::verify::loops) fn loop_entry_may_execute_outcome(
    requires: &[PureExpr],
    pre_loop_assignments: &HashMap<String, NamedBindingValue>,
    loop_condition: Option<&PureExpr>,
    config: &LoopEncoderConfig<'_>,
) -> Result<LoopEntryOutcome, EncodingError> {
    let Some(cond) = loop_condition else {
        return Ok(LoopEntryOutcome {
            may_execute: true,
            outcome: None,
        });
    };
    if hashmap_list_loop_entry_probe_should_assume_may_execute(requires, config) {
        return Ok(LoopEntryOutcome {
            may_execute: true,
            outcome: None,
        });
    }

    // Uses NamedBindingValue.lhs_var() to preserve MIR-derived sort. (#2053 Slice B)
    let assignment_exprs: Vec<PureExpr> = pre_loop_assignments
        .iter()
        .map(|(name, binding)| {
            PureExpr::BinOp(
                Arc::new(binding.lhs_var(name)),
                BinOp::Eq,
                Arc::new(binding.value.clone()),
            )
        })
        .collect();

    let expr_slices = [
        ExprSlice::formula(requires),
        ExprSlice::formula(&assignment_exprs),
        ExprSlice::formula(std::slice::from_ref(cond)),
    ];
    let mut encoder = bootstrap_encoder(BootstrapRequest {
        expr_slices: &expr_slices,
        result_postconditions: None,
        result_expr: None,
        logic_fns: config.logic_fns.map(LogicFnInput::FilterForGoalGroundOnly),
        mode_overrides: config.mode_overrides,
        type_invariants: config
            .type_invariants
            .map(TypeInvariantInput::FilterForGoal),
        track: config.track.unwrap_or_default(),
        timeout: config.timeout,
        type_constants: config.type_constants,
        closure_captures: None,
        adt_decls: config.adt_decls,
        adt_field_ranges: config.adt_field_ranges,
    })?;

    // Assert preconditions with existential Skolemization (#1364).
    encode_and_assert_requires(&mut encoder, requires)?;
    for assignment in &assignment_exprs {
        let term = encoder.encode_pure(assignment)?;
        encoder.assert_term(term);
    }
    encode_and_assert_condition(&mut encoder, cond)?;
    assert_loop_current_chain_alias_constraints(&mut encoder)?;

    encoder.mark_postcondition_logic_fn_symbols(requires);
    encoder.mark_postcondition_logic_fn_symbols(&assignment_exprs);
    encoder.mark_postcondition_logic_fn_symbols(std::slice::from_ref(cond));

    // Pre-assert Seq ground instances before axiom probe. (#2323)
    if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia) {
        encoder.assert_seq_ground_instances(
            crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
        );
    }

    // Two-phase axiom solving (#2116): try without axioms first.
    // Parity with verify_preservation_with_config: skip axioms for QF_LIA (#1573).
    if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia)
        && try_axiom_free_solve(&mut encoder).is_none()
    {
        // Pass requires so eager instantiation can scan for ground closure-spec terms.
        assert_standard_axioms(&mut encoder, requires, &[])?;
    }

    // Hard-timeout guarded solve (#2457). The sound fallback on timeout
    // is to assume the loop may execute so variant checks are not skipped.
    let solve_start = std::time::Instant::now();
    let (may_execute, outcome) = match resolve_sat_result_lightweight_timed(&mut encoder) {
        crate::verify::hard_timeout::ResolveContinuation::Continue(result) => {
            let may_execute = !matches!(result, VerificationResult::Verified(_));
            (
                may_execute,
                VerificationOutcome::new(
                    result,
                    Some(encoder.capture_provenance(solve_start.elapsed())),
                ),
            )
        }
        // Abort (hard timeout): conservatively assume loop may execute.
        crate::verify::hard_timeout::ResolveContinuation::Abort(result) => {
            (true, VerificationOutcome::without_provenance(result))
        }
    };
    Ok(LoopEntryOutcome {
        may_execute,
        outcome: Some(outcome),
    })
}

fn hashmap_list_loop_entry_probe_should_assume_may_execute(
    requires: &[PureExpr],
    config: &LoopEncoderConfig<'_>,
) -> bool {
    requires.iter().any(is_hashmap_list_invariant_body)
        || config.type_invariants.is_some_and(|type_invariants| {
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
