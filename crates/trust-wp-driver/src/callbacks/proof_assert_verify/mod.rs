// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof assertion verification helpers.
//!
//! Contains `ProofAssertSetup`, `PreparedAssertion`, `build_proof_assert_setup`,
//! and `prepare_proof_assert`. The inline verification loop in `verification.rs`
//! calls these helpers per-function (Phase 4, #1572).

mod mapping_closure;
mod setup;

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

pub(super) use mapping_closure::{
    inline_bool_mapping_closure_calls, instantiate_mapping_closure_ground,
    instantiate_mapping_closure_ground_from_expr, retain_relevant_mapping_closure_foralls,
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
pub(super) use setup::build_proof_assert_setup;
use tracing::debug;
use trust_wp_core::{
    closure::ClosureCaptureInfo,
    contract_parser::parse_contract_body,
    formula::{BinOp, PureExpr},
    logic::LogicMode,
};
use trust_wp_driver::StdSpec;

pub(super) use super::proof_assert_snapshot_facts::{
    collect_deref_snapshot_aliases, derive_snapshot_deref_alias_substitutions,
    substitute_assertion_final_carriers, substitute_snapshot_facts,
};
use super::{
    super::contracts::FunctionContract,
    contract_rewrite::rewrite_logic_method_calls_expr,
    helpers::contains_mutating_call_effect,
    iterator_spec_rewrite::rewrite_iterator_spec_expr,
    logic_fn_scope::normalize_logic_fn_names,
    parsing::get_arg_names_from_def_id,
    proof_assert_extract::{
        apply_constructor_equality_substitutions,
        apply_constructor_equality_substitutions_to_facts, apply_type_and_field_rewrites,
        collapse_idempotent_views, constructor_equality_to_tester_selector_facts,
        get_arg_names_for_proof_assert_body, normalize_old_constructor_equality_facts,
        normalize_scalar_proof_assert_boundary, normalize_seq_final_fact_views,
        normalize_view_fn_calls, preserve_transparent_adapter_view_witness,
        reduce_concrete_constructor_method_calls, reduce_concrete_matches,
        simplify_proof_assert_expr, synthesize_constructor_equalities,
        synthesize_ground_equality_substitution_facts,
    },
    proof_assert_leading_calls::collect_leading_proof_assert_assumptions,
    proof_assert_snapshot::AssertionSnapshot,
    proof_assert_wiring::apply_closure_wiring,
    type_invariants::build_type_invariant_clauses,
};

/// Shared setup used to prepare individual `proof_assert` checks.
pub(super) struct ProofAssertSetup<'a> {
    fn_preconditions: HashMap<LocalDefId, Vec<PureExpr>>,
    const_item_substitutions: HashMap<String, PureExpr>,
    contract_by_local: HashMap<LocalDefId, &'a FunctionContract>,
    logic_fn_path_map: HashMap<String, String>,
    logic_method_names: HashSet<String>,
    pub(super) user_specs: HashMap<DefId, StdSpec>,
}

/// Fully prepared proof assertion ready for solver dispatch.
pub(super) struct PreparedAssertion {
    pub(super) preconditions: Vec<PureExpr>,
    pub(super) ensures: Vec<PureExpr>,
    pub(super) return_expr: Option<PureExpr>,
    pub(super) mode_overrides: Option<Vec<LogicMode>>,
    pub(super) closure_capture_infos: Vec<ClosureCaptureInfo>,
    pub(super) has_mutating_call_effect: bool,
    pub(super) is_contractless: bool,
    /// Whether the containing function carries an explicit user-authored
    /// `#[requires(false)]`. Such a function is provably uncallable, so a
    /// vacuous `proof_assert!` inside it is vacuously discharged by Creusot
    /// semantics and must be accepted rather than counted as an error. Keyed to
    /// the PRECONDITION position only (does NOT credit `#[ensures(false)]`).
    pub(super) containing_requires_false: bool,
    pub(super) fn_path: String,
    pub(super) loc: String,
    pub(super) expr_text: String,
}

pub(super) fn rewrite_iterator_spec_proof_assert_clauses(
    preconditions: &mut [PureExpr],
    ensures: &mut [PureExpr],
) {
    for expr in preconditions {
        *expr = rewrite_iterator_spec_expr(expr);
    }
    for expr in ensures {
        *expr = rewrite_iterator_spec_expr(expr);
    }
}

pub(super) fn substitute_assertion_names(
    assertion: &PureExpr,
    substitutions: &HashMap<String, PureExpr>,
    names: &HashSet<String>,
) -> PureExpr {
    if substitutions.is_empty() || names.is_empty() {
        return assertion.clone();
    }

    let filter: HashSet<&str> = names.iter().map(String::as_str).collect();
    assertion.substitute_filtered(&filter, substitutions)
}

pub(super) fn preserve_transparent_adapter_views(expr: PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(preserve_transparent_adapter_view_witness)
}

fn is_stale_mutation_alias_fact(expr: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    is_self_final_alias(lhs, rhs) || is_self_final_alias(rhs, lhs)
}

/// Detect an assumed fact whose substituted form contains a literal-vs-literal
/// FALSE equality (e.g. `42 == 43`, or `guard ==> (42 == 43)`).
///
/// Such facts are substitution-corrupt: the cutoff-time name substitution map
/// keys on SOURCE names, so when a binding is SHADOWED (two `let x` bindings,
/// or an `if let Some(x)` pattern followed by a later `let (x, ..)`), a fact
/// recorded against the FIRST binding (`*x == 43`) gets rewritten with the
/// SECOND binding's value (`42`), manufacturing `42 == 43`. Asserting it (even
/// guarded) collapses the base premises to UNSAT on the guard's path and trips
/// the vacuity guard (ghost/ghost_map). Dropping an assumption is always
/// fail-closed: it can only lose provability, never soundness.
fn is_substitution_falsified_fact(expr: &PureExpr) -> bool {
    fn contains_positive_literal_false(expr: &PureExpr) -> bool {
        match expr {
            PureExpr::Bool(false) => true,
            PureExpr::BinOp(lhs, BinOp::Eq, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                (PureExpr::Int(a), PureExpr::Int(b)) => a != b,
                (PureExpr::Bool(a), PureExpr::Bool(b)) => a != b,
                _ => false,
            },
            PureExpr::BinOp(lhs, BinOp::Ne, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                (PureExpr::Int(a), PureExpr::Int(b)) => a == b,
                (PureExpr::Bool(a), PureExpr::Bool(b)) => a == b,
                _ => false,
            },
            // A conjunction is false when either side is; an implication is
            // corrupt when its CONSEQUENT is a literal false (the manufactured
            // `guard ==> (42 == 43)` shape reduces to `!guard`, a path-negation
            // fact the extraction never legitimately emits through this
            // channel).
            PureExpr::BinOp(lhs, BinOp::And, rhs) => {
                contains_positive_literal_false(lhs) || contains_positive_literal_false(rhs)
            }
            PureExpr::BinOp(_, BinOp::Implies, rhs) => contains_positive_literal_false(rhs),
            _ => false,
        }
    }
    contains_positive_literal_false(expr)
}

fn is_stale_closure_capture_env_fact(expr: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    is_stale_double_final_capture_alias(lhs, rhs) || is_stale_double_final_capture_alias(rhs, lhs)
}

fn is_stale_double_final_capture_alias(capture_candidate: &PureExpr, rhs: &PureExpr) -> bool {
    let PureExpr::Var(_, _) = capture_candidate else {
        return false;
    };
    let PureExpr::LogicFnCall { name, args } = rhs else {
        return false;
    };
    if name != "__trust_wp_tuple1" {
        return false;
    }
    args.iter().any(contains_nested_final)
}

fn contains_nested_final(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Final(inner) => {
            matches!(inner.as_ref(), PureExpr::Final(_)) || contains_nested_final(inner)
        }
        PureExpr::BinOp(lhs, _, rhs) => contains_nested_final(lhs) || contains_nested_final(rhs),
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::View(inner) => contains_nested_final(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_nested_final(cond)
                || contains_nested_final(then_expr)
                || contains_nested_final(else_expr)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            triggers.iter().flatten().any(contains_nested_final) || contains_nested_final(body)
        }
        PureExpr::Match { scrutinee, arms } => {
            contains_nested_final(scrutinee)
                || arms.iter().any(|arm| contains_nested_final(&arm.body))
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            contains_nested_final(receiver) || args.iter().any(contains_nested_final)
        }
        PureExpr::Closure { body, .. } => contains_nested_final(body),
        PureExpr::Let { value, body, .. } => {
            contains_nested_final(value) || contains_nested_final(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_nested_final(assumption) || contains_nested_final(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_nested_final(obligation) || contains_nested_final(body)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

fn is_self_final_alias(pre: &PureExpr, post: &PureExpr) -> bool {
    let PureExpr::Var(pre_name, _) = pre else {
        return false;
    };
    let PureExpr::Final(inner) = post else {
        return false;
    };
    matches!(inner.as_ref(), PureExpr::Var(post_name, _) if post_name == pre_name)
}

fn derive_has_mutating_call_effect(
    snapshot_has_mutating_call_effect: bool,
    leading_has_mutating_call_effect: bool,
    call_effect_expr: Option<&PureExpr>,
) -> bool {
    snapshot_has_mutating_call_effect
        || leading_has_mutating_call_effect
        || call_effect_expr.is_some_and(contains_mutating_call_effect)
}

/// Prepare a single `proof_assert` for verification.
///
/// Returns:
/// - `Ok(Some(..))` when preparation succeeds,
/// - `Ok(None)` when the assertion is trusted and intentionally skipped,
/// - `Err(())` when preparation fails and should count as an error.
pub(super) fn prepare_proof_assert(
    tcx: TyCtxt<'_>,
    snapshot: &AssertionSnapshot,
    setup: &ProofAssertSetup<'_>,
    ctx: &super::verification_context::ProofAssertContext<'_>,
    local_crate_name: &str,
) -> Result<Option<PreparedAssertion>, ()> {
    let pa = &snapshot.assertion;
    let fn_path_local = tcx.def_path_str(pa.containing_fn);
    let fn_path = format!("{local_crate_name}::{fn_path_local}");
    let loc = tcx.sess.source_map().span_to_diagnostic_string(pa.span);

    if pa.trusted {
        if ctx.verbose {
            eprintln!("trust-wp: proof_assert in {fn_path} trusted (skipped)");
        }
        return Ok(None);
    }

    let Some(expr_text) = pa.expr_text.as_deref() else {
        if ctx.verbose {
            eprintln!("trust-wp: proof_assert in {fn_path} has no expression text");
        }
        return Err(());
    };

    // Parse the assertion expression.
    // Use parse_contract_body to support multi-statement proof_assert! blocks
    // (Creusot pattern: `lemma_call(); assertion_expr`). Leading statements
    // are parsed and discarded; the trailing expression is the assertion.
    let mut assertion = match parse_contract_body(expr_text) {
        Ok(expr) => expr,
        Err(e) => {
            crate::result_protocol_state::record_parse_error();
            eprintln!("trust-wp: error: failed to parse proof_assert '{expr_text}': {e}");
            return Err(());
        }
    };

    // Normalize `view(expr)` → View(expr) and `final_value(expr)` → Final(expr).
    // When proof_assert! is inside ghost!, the ghost macro's preprocess_view_syntax
    // transforms `expr@` to `view(expr)` at the token level, causing the contract
    // parser to produce LogicFnCall instead of View. (#2209)
    assertion = normalize_view_fn_calls(assertion);
    assertion = collapse_idempotent_views(assertion);

    // Normalize module-qualified logic function names in the assertion.
    // The contract parser preserves paths like `x::transparent()`, but
    // logic functions are registered by short name (`transparent`). Without
    // normalization, the SMT encoder creates a free placeholder function
    // instead of finding the registered axiomatized function. (#746)
    assertion = normalize_logic_fn_names(assertion, &setup.logic_fn_path_map);
    assertion = rewrite_logic_method_calls_expr(&assertion, &setup.logic_method_names);
    // Apply sound tautology simplifications before SMT encoding. This avoids
    // quantifier-unknown outcomes for formulas that are trivially true by
    // propositional/first-order identities (for example `forall<x> p ==> p`).
    assertion = simplify_proof_assert_expr(assertion);
    assertion = crate::assoc_const_paths::normalize_local_assoc_const_paths(
        tcx,
        pa.containing_fn.to_def_id(),
        &assertion,
    );

    if !snapshot.assoc_const_substitutions.is_empty() {
        assertion = assertion.substitute(&snapshot.assoc_const_substitutions);
    }

    // Substitute named const items (e.g., `TUP` -> `__trust_wp_tuple2(42, 24)`).
    // Includes tuple beta-reduction so `TUP.0` simplifies to `42`. (#1588)
    if !setup.const_item_substitutions.is_empty() {
        assertion = assertion.substitute(&setup.const_item_substitutions);
    }

    // For proof_assert inside closures, inherit contracts from the typeck
    // root owner (the enclosing function item) instead of the closure body.
    let owner_local = tcx
        .typeck_root_def_id(pa.containing_fn.to_def_id())
        .expect_local();

    // Get preconditions for the containing function (if any)
    let fn_precond_vec = setup
        .fn_preconditions
        .get(&pa.containing_fn)
        .or_else(|| setup.fn_preconditions.get(&owner_local))
        .cloned()
        .unwrap_or_default();
    let fn_precond_count = fn_precond_vec.len();
    let mut preconditions = fn_precond_vec;
    let (leading_call_assumptions, leading_has_mutating_call_effect) =
        collect_leading_proof_assert_assumptions(
            tcx,
            pa,
            ctx.logic_fn_defs,
            &setup.user_specs,
            &setup.logic_method_names,
        );
    let has_mutating_call_effect = derive_has_mutating_call_effect(
        snapshot.has_mutating_call_effect,
        leading_has_mutating_call_effect,
        snapshot.call_effect_expr.as_ref(),
    );
    if ctx.verbose && !leading_call_assumptions.is_empty() {
        debug!(
            "trust-wp:   (proof_assert: {} leading call assumption(s) injected)",
            leading_call_assumptions.len()
        );
    }
    preconditions.extend(leading_call_assumptions);

    let body_arg_names = get_arg_names_for_proof_assert_body(tcx, pa.containing_fn);
    let containing_contract = setup
        .contract_by_local
        .get(&pa.containing_fn)
        .or_else(|| setup.contract_by_local.get(&owner_local));
    // Whether the containing function carries an explicit user-authored
    // `#[requires(false)]`. Keyed to the PRECONDITION position only via the raw
    // source clause text, so `#[ensures(false)]` is not credited here.
    let containing_requires_false = containing_contract
        .is_some_and(|contract| super::reporting::user_authored_requires_false(contract));
    let containing_def_id =
        containing_contract.map_or_else(|| owner_local.to_def_id(), |contract| contract.def_id);
    let contract_arg_names =
        get_arg_names_from_def_id(tcx, containing_def_id).unwrap_or_else(|| {
            let path = tcx.def_path_str(containing_def_id);
            debug!(
                "trust-wp: warning: no parameter names for `{path}` ({containing_def_id:?}), \
                 using positional fallback \u{2014} named contract parameters will not be substituted"
            );
            Vec::new()
        });
    // Rewrite type invariant methods + struct field access in assertion and preconditions.
    apply_type_and_field_rewrites(
        tcx,
        containing_def_id,
        &contract_arg_names,
        ctx.type_invariant_defs,
        ctx.verbose,
        &mut assertion,
        &mut preconditions,
    );
    if !snapshot.post_loop_assumptions.is_empty() {
        let mut post_loop_assumptions = snapshot.post_loop_assumptions.clone();
        for assumption in &mut post_loop_assumptions {
            *assumption = normalize_logic_fn_names(assumption.clone(), &setup.logic_fn_path_map);
            *assumption = rewrite_logic_method_calls_expr(assumption, &setup.logic_method_names);
        }
        let mut dummy_assertion = PureExpr::Bool(true);
        apply_type_and_field_rewrites(
            tcx,
            containing_def_id,
            &contract_arg_names,
            ctx.type_invariant_defs,
            ctx.verbose,
            &mut dummy_assertion,
            &mut post_loop_assumptions,
        );
        preconditions.extend(post_loop_assumptions);
    }

    // Inject type-invariant preconditions for the containing function's
    // parameters. Normal contract verification gets these through
    // `enrich_effective_clauses`, but proof_assert was missing this step,
    // causing inv(x) and container element invariant assertions to fail
    // due to under-constrained VCs. (#2244)
    //
    // Scope the injection to only parameters whose names appear as free
    // variables in the rewritten assertion. Injecting invariants for all
    // parameters over-constrains the VC for local proof_assert obligations
    // that only reference a subset of the function's arguments. (#2339)
    let invariant_arg_names = if contract_arg_names.is_empty() {
        body_arg_names.clone()
    } else {
        contract_arg_names.clone()
    };
    let assertion_free_vars = assertion.free_vars();
    let mut type_invariant_relevance_vars = assertion_free_vars.clone();
    for obligation in &snapshot.call_obligations {
        type_invariant_relevance_vars.extend(obligation.free_vars());
    }
    let relevant_invariant_arg_names: Vec<String> = invariant_arg_names
        .into_iter()
        .filter(|name| type_invariant_relevance_vars.contains(name))
        .collect();
    let (inv_requires, _) = build_type_invariant_clauses(
        tcx,
        containing_def_id,
        &relevant_invariant_arg_names,
        ctx.type_invariant_defs,
    );
    if !inv_requires.is_empty() {
        if ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: {} type invariant precondition(s) injected)",
                inv_requires.len()
            );
        }
        preconditions.extend(inv_requires);
    }

    if ctx.verbose {
        eprintln!("trust-wp: verifying proof_assert in {fn_path} ({fn_precond_count} contract preconditions)");
        debug!(
            "trust-wp: verifying proof_assert in {fn_path} ({fn_precond_count} contract preconditions)"
        );
        debug!("  assertion: {assertion}");
    }

    let mut local_substitutions = snapshot.substitutions.clone();
    let mut assumed_facts = snapshot.assumed_facts.clone();
    let before_assumed_facts = assumed_facts.len();
    assumed_facts.retain(|fact| {
        !(has_mutating_call_effect && is_stale_mutation_alias_fact(fact))
            && !is_stale_closure_capture_env_fact(fact)
            && !is_substitution_falsified_fact(fact)
    });
    let filtered_assumed_facts = before_assumed_facts - assumed_facts.len();
    if filtered_assumed_facts > 0 && ctx.verbose {
        debug!(
            "trust-wp:   (proof_assert: filtered {} stale assumed fact(s))",
            filtered_assumed_facts,
        );
    }
    let mut call_obligations = snapshot.call_obligations.clone();
    derive_assertion_final_alias_substitutions(
        &mut local_substitutions,
        &assumed_facts,
        &assertion_free_vars,
    );
    if !local_substitutions.is_empty() {
        assertion =
            substitute_assertion_names(&assertion, &local_substitutions, &assertion_free_vars);
        assertion = preserve_transparent_adapter_views(assertion);
        assertion = collapse_idempotent_views(assertion);
        // Applying a program-point substitution such as `*a -> call_N` (the
        // post-call deref read) introduces a fresh call-result var that is
        // bound to a reference's prophecy by an assumed fact (`call_N == ^a`).
        // The earlier final-alias pass ran over the ORIGINAL free vars (`a`,
        // `a_p`) and never saw `call_N`. Re-derive final aliases over the
        // now-present vars and rewrite, so the goal expresses the post-call
        // read directly as `^a` — matching the callee's postcondition carrier
        // (`^a > *a`) syntactically and closing the proof. (#682)
        let introduced_free_vars = assertion.free_vars();
        let mut final_alias_substitutions: HashMap<String, PureExpr> = HashMap::new();
        derive_assertion_final_alias_substitutions(
            &mut final_alias_substitutions,
            &assumed_facts,
            &introduced_free_vars,
        );
        if !final_alias_substitutions.is_empty() {
            assertion = substitute_assertion_names(
                &assertion,
                &final_alias_substitutions,
                &introduced_free_vars,
            );
            assertion = preserve_transparent_adapter_views(assertion);
            assertion = collapse_idempotent_views(assertion);
        }
        if ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: applied {} program-point substitution(s))",
                local_substitutions.len()
            );
            debug!("trust-wp:     assertion_after_sub: {assertion}");
        }
        let deref_aliases = collect_deref_snapshot_aliases(&assertion, &assumed_facts);
        if !deref_aliases.is_empty() {
            let deref_alias_names: HashSet<String> = deref_aliases.keys().cloned().collect();
            derive_snapshot_deref_alias_substitutions(&mut local_substitutions, &deref_aliases);
            assertion =
                substitute_assertion_names(&assertion, &local_substitutions, &deref_alias_names);
            assertion = preserve_transparent_adapter_views(assertion);
            assertion = collapse_idempotent_views(assertion);
            assumed_facts = substitute_snapshot_facts(&assumed_facts, &local_substitutions);
            call_obligations = substitute_snapshot_facts(&call_obligations, &local_substitutions);
            if ctx.verbose {
                debug!("trust-wp:     assertion_after_deref_alias: {assertion}");
            }
        }
        let precise_final_rewritten =
            substitute_precise_final_update_carriers(&assertion, &assumed_facts);
        let final_carrier_rewritten =
            substitute_assertion_final_carriers(&precise_final_rewritten, &assumed_facts);
        if final_carrier_rewritten != assertion {
            assertion = preserve_transparent_adapter_views(final_carrier_rewritten);
            assertion = collapse_idempotent_views(assertion);
            if ctx.verbose {
                debug!("trust-wp:     assertion_after_final_fact_alias: {assertion}");
            }
        }
        let rewritten_call_obligations: Vec<PureExpr> = call_obligations
            .iter()
            .map(|obligation| substitute_precise_final_update_carriers(obligation, &assumed_facts))
            .map(|obligation| substitute_assertion_final_carriers(&obligation, &assumed_facts))
            .map(collapse_idempotent_views)
            .collect();
        if rewritten_call_obligations != call_obligations {
            call_obligations = rewritten_call_obligations;
            if ctx.verbose {
                debug!(
                    "trust-wp:     call_obligations_after_final_fact_alias: {call_obligations:?}"
                );
            }
        }
        if !has_mutating_call_effect {
            filter_consumed_final_update_facts(&mut assumed_facts, &assertion, &call_obligations);
        }
    }
    if !snapshot.mapping_closures.is_empty() {
        assertion = inline_bool_mapping_closure_calls(&assertion, &snapshot.mapping_closures);
        assertion = collapse_idempotent_views(assertion);
        if ctx.verbose {
            debug!("trust-wp:     assertion_after_bool_inline: {assertion}");
        }
    }
    // Direct ground instantiation: for each assumed fact matching
    // `mapping.get(arg)` where `mapping` has a MappingClosureInfo,
    // substitute `arg` into the closure body and add as a precondition.
    // This bypasses sort interop issues between mapping_get (Int) and
    // Bool-valued closure bodies like `(x + 1) == 42`. (#2245)
    let ground_instances =
        instantiate_mapping_closure_ground(&assumed_facts, &snapshot.mapping_closures);
    if !ground_instances.is_empty() {
        if ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: {} mapping closure ground instance(s))",
                ground_instances.len(),
            );
            for (i, gi) in ground_instances.iter().enumerate() {
                debug!("trust-wp:     ground_instance[{i}]: {gi:?}");
            }
        }
        preconditions.extend(ground_instances);
    }

    if ctx.verbose && (!assumed_facts.is_empty() || !call_obligations.is_empty()) {
        debug!(
            "trust-wp:   (proof_assert: {} assumed fact(s), {} call obligation(s))",
            assumed_facts.len(),
            call_obligations.len(),
        );
        for (i, fact) in assumed_facts.iter().enumerate() {
            debug!("trust-wp:     assumed_fact[{i}]: {fact}");
        }
    }
    // Second pass: ground-instantiate mapping closures from the assertion
    // expression (post-substitution). The first pass only scanned snapshot
    // assumed facts. The assertion itself may contain `mapping.index_logic(arg)`
    // terms that provide ground instances the solver needs. (#2245)
    if !snapshot.mapping_closures.is_empty() {
        let assertion_ground =
            instantiate_mapping_closure_ground_from_expr(&assertion, &snapshot.mapping_closures);
        if !assertion_ground.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} assertion-derived ground instance(s))",
                    assertion_ground.len(),
                );
                for (i, gi) in assertion_ground.iter().enumerate() {
                    debug!("trust-wp:     assertion_ground[{i}]: {gi:?}");
                }
            }
            preconditions.extend(assertion_ground);
        }
    }

    // Static match elimination: reduce match expressions with concrete
    // constructor scrutinees (e.g., `match *None() { Some(v) => ..., None => ... }`)
    // before SMT encoding. Match-style postconditions from specs like ok_or
    // produce these patterns as assumed facts, and the ay encoder cannot
    // statically evaluate them. (#2675)
    {
        let mut match_reduced_count = 0usize;
        for fact in &mut assumed_facts {
            // `reduce_concrete_matches` resolves matches on concrete constructor
            // scrutinees; `simplify_identity_matches` additionally collapses an
            // *identity* match on a SYMBOLIC scrutinee (e.g. the body binding
            // `y == match x { -1 => -1, 127 => 127, _ => x }` ⇒ `y == x`). Without
            // it, each such match lowers to a discriminant case-split that the
            // solver multiplies across independent body matches, exploding search
            // (4 sequential identity matches: timeout vs ~0s for one). SOUND: an
            // identity match equals its scrutinee on every input. (#negative_int_pats)
            let reduced = reduce_concrete_matches(fact.clone()).simplify_identity_matches();
            if reduced != *fact {
                match_reduced_count += 1;
                *fact = reduced;
            }
        }
        let reduced_assertion =
            reduce_concrete_matches(assertion.clone()).simplify_identity_matches();
        if reduced_assertion != assertion {
            match_reduced_count += 1;
            assertion = reduced_assertion;
        }
        if match_reduced_count > 0 && ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: {} concrete match(es) statically reduced)",
                match_reduced_count,
            );
        }
    }

    // Static evaluation of constructor method calls in assumed facts.
    // Implication-style postconditions from specs like ok_or produce assumed
    // facts like `None().is_some() ==> (call_3 == Ok(old(None()).unwrap()))`.
    // The antecedent `None().is_some()` is statically false, making the
    // implication vacuously true (useless). Similarly, `None().is_none()`
    // is statically true, so `None().is_none() ==> X` simplifies to `X`.
    //
    // Without this reduction, the solver must reason about `is_some`/`is_none`
    // on concrete constructors, which requires additional axiom instantiation
    // that may not trigger. This pass evaluates these calls at the expression
    // level before encoding. (#2675)
    {
        let mut ctor_method_reduced_count = 0usize;
        for fact in &mut assumed_facts {
            let reduced = reduce_concrete_constructor_method_calls(fact.clone());
            if reduced != *fact {
                ctor_method_reduced_count += 1;
                *fact = reduced;
            }
        }
        {
            let reduced = reduce_concrete_constructor_method_calls(assertion.clone());
            if reduced != assertion {
                ctor_method_reduced_count += 1;
                assertion = reduced;
            }
        }
        if ctor_method_reduced_count > 0 && ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: {} constructor method call(s) statically reduced)",
                ctor_method_reduced_count,
            );
        }
    }

    // Synthesize constructor equalities from tester+selector assumed fact
    // pairs (e.g., `x.is_err() ∧ x.unwrap_err() == v` → `x == Err(v)`).
    // These are direct consequences of ADT datatype theory axioms that
    // the solver cannot derive without explicit constructor-tester-selector
    // axiom instantiation. (#2675)
    {
        let synthesized = synthesize_constructor_equalities(&assumed_facts);
        if !synthesized.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} constructor equality/ies synthesized)",
                    synthesized.len(),
                );
            }
            assumed_facts.extend(synthesized);
        }
        let normalized_old_facts: Vec<PureExpr> = assumed_facts
            .iter()
            .flat_map(normalize_old_constructor_equality_facts)
            .collect();
        if !normalized_old_facts.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} old-wrapped constructor equality/ies normalized)",
                    normalized_old_facts.len(),
                );
            }
            assumed_facts.extend(normalized_old_facts);
        }
        let ctor_tester_selector_facts: Vec<PureExpr> = assumed_facts
            .iter()
            .flat_map(constructor_equality_to_tester_selector_facts)
            .collect();
        if !ctor_tester_selector_facts.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} constructor tester/selector fact(s) synthesized)",
                    ctor_tester_selector_facts.len(),
                );
            }
            assumed_facts.extend(ctor_tester_selector_facts);
        }
    }

    // Apply constructor equality substitutions: when assumed facts contain
    // `var == Constructor(...)`, substitute var in the assertion and re-run
    // concrete match reduction. This resolves match expressions on variables
    // that are known to be specific constructors. (#2675)
    {
        let reduced = apply_constructor_equality_substitutions(assertion.clone(), &assumed_facts);
        if reduced != assertion {
            if ctx.verbose {
                debug!("trust-wp:   (proof_assert: assertion reduced via constructor equality substitution)");
                debug!("trust-wp:     assertion_after_ctor_eq: {reduced}");
            }
            assertion = reduced;
        }

        let (reduced_facts, reduced_count) =
            apply_constructor_equality_substitutions_to_facts(&assumed_facts);
        if reduced_count > 0 {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} assumed fact(s) reduced via constructor equality substitution)",
                    reduced_count,
                );
            }
            assumed_facts = reduced_facts;
        }

        let mut equality_sources = preconditions.clone();
        equality_sources.extend(assumed_facts.iter().cloned());
        let ground_instances =
            synthesize_ground_equality_substitution_facts(&equality_sources, &assumed_facts);
        if !ground_instances.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} ground equality substitution fact(s) synthesized)",
                    ground_instances.len(),
                );
            }
            assumed_facts.extend(ground_instances);
        }
    }
    {
        let mut equality_sources = preconditions.clone();
        equality_sources.extend(assumed_facts.iter().cloned());
        let transitive_disequalities =
            synthesize_transitive_disequalities(&equality_sources, &equality_sources);
        if !transitive_disequalities.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} transitive disequality fact(s) synthesized)",
                    transitive_disequalities.len(),
                );
            }
            assumed_facts.extend(transitive_disequalities);
        }
    }

    let filtered_mapping_foralls = retain_relevant_mapping_closure_foralls(
        &mut assumed_facts,
        &snapshot.mapping_closures,
        &assertion,
        &preconditions,
        &call_obligations,
    );
    if filtered_mapping_foralls > 0 && ctx.verbose {
        debug!(
            "trust-wp:   (proof_assert: filtered {} irrelevant mapping closure forall assumption(s))",
            filtered_mapping_foralls
        );
    }

    let filtered_len_facts = filter_len_only_irrelevant_facts(&assertion, &mut assumed_facts);
    if filtered_len_facts > 0 && ctx.verbose {
        debug!(
            "trust-wp:   (proof_assert: filtered {} non-length fact(s) from length-only assertion)",
            filtered_len_facts
        );
    }

    // Assertion slicing: filter assumed_facts to only those transitively
    // relevant to the assertion's free variables. Ghost-heavy tests (e.g.,
    // ghost_vec with 50+ accumulated postconditions) spend most solver time
    // on irrelevant preconditions. This performs cone-of-influence reduction
    // to keep only facts that share variables with the assertion (transitively).
    // Skip slicing when assumed_facts is small (threshold: 20) to avoid
    // overhead on simple assertions where all facts are likely relevant.
    if assumed_facts.len() > 20 {
        let mut relevant_vars: HashSet<String> = assertion.free_vars();
        // Pre-compute free vars for each assumed fact
        let fact_vars: Vec<HashSet<String>> = assumed_facts.iter().map(|f| f.free_vars()).collect();
        // Fixed-point expansion: keep adding facts whose vars overlap with
        // the relevant set until no new facts are added
        let mut relevant_indices: HashSet<usize> = HashSet::new();
        loop {
            let prev_count = relevant_indices.len();
            for (i, fv) in fact_vars.iter().enumerate() {
                if !relevant_indices.contains(&i) && !fv.is_disjoint(&relevant_vars) {
                    relevant_indices.insert(i);
                    relevant_vars.extend(fv.iter().cloned());
                }
            }
            if relevant_indices.len() == prev_count {
                break;
            }
        }
        let original_count = assumed_facts.len();
        if relevant_indices.len() < original_count {
            let sliced: Vec<PureExpr> = assumed_facts
                .into_iter()
                .enumerate()
                .filter(|(i, _)| relevant_indices.contains(i))
                .map(|(_, f)| f)
                .collect();
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: assertion slicing reduced {} → {} assumed facts)",
                    original_count,
                    sliced.len(),
                );
            }
            assumed_facts = sliced;
        }
    }

    // Filter out trivially-true assumed facts (Bool(true)) that result from
    // boolean constant folding in reduce_concrete_constructor_method_calls.
    // These add noise to the solver without providing information. (#2671)
    {
        let before = assumed_facts.len();
        assumed_facts.retain(|f| !matches!(f, PureExpr::Bool(true)));
        let filtered = before - assumed_facts.len();
        if filtered > 0 && ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: filtered {} trivially-true assumed fact(s))",
                filtered,
            );
        }
    }

    // Phase 8: Closure wiring, obligation filtering, and enrichment passes.
    //
    // Call postconditions are part of the proof_assert premises. Add them
    // before closure wiring so existential enrichment can see closure
    // postcondition facts synthesized from preceding calls.
    preconditions.extend(assumed_facts.iter().cloned());
    let wiring_ctx = super::proof_assert_wiring::ClosureWiringContext {
        tcx,
        containing_fn: pa.containing_fn,
        owner_local,
        user_specs: &setup.user_specs,
        const_item_substitutions: &setup.const_item_substitutions,
        logic_fn_defs: ctx.logic_fn_defs,
        type_invariant_defs: ctx.type_invariant_defs,
        verbose: ctx.verbose,
        body_arg_names: &body_arg_names,
        fn_path: &fn_path,
    };
    let wiring = apply_closure_wiring(
        &wiring_ctx,
        &mut preconditions,
        assertion,
        &call_obligations,
    );
    let mut ensures = wiring.ensures;
    if !snapshot.assoc_const_substitutions.is_empty() {
        preconditions = preconditions
            .into_iter()
            .map(|expr| expr.substitute(&snapshot.assoc_const_substitutions))
            .collect();
        ensures = ensures
            .into_iter()
            .map(|expr| expr.substitute(&snapshot.assoc_const_substitutions))
            .collect();
    }
    rewrite_iterator_spec_proof_assert_clauses(&mut preconditions, &mut ensures);
    preconditions = preconditions
        .into_iter()
        .map(normalize_seq_final_fact_views)
        .map(collapse_idempotent_views)
        .collect();
    ensures = ensures
        .into_iter()
        .map(normalize_seq_final_fact_views)
        .map(collapse_idempotent_views)
        .collect();
    // Proof assertions are an explicit proof-authority boundary. Keep even a
    // syntactic `true` or a goal already present in the premises: the strict
    // lane must solve and replay that exact authored obligation. Deleting it
    // here turns an authored assertion into an empty obligation set, which can
    // aggregate to `Verified` without any per-slice certificate.
    let mut return_expr = snapshot.return_expr.clone();
    if !snapshot.assoc_const_substitutions.is_empty() {
        return_expr = return_expr.map(|expr| expr.substitute(&snapshot.assoc_const_substitutions));
    }
    return_expr = return_expr.map(preserve_transparent_adapter_views);
    assumed_facts = assumed_facts
        .into_iter()
        .map(preserve_transparent_adapter_views)
        .collect();
    call_obligations = call_obligations
        .into_iter()
        .map(preserve_transparent_adapter_views)
        .collect();
    normalize_scalar_proof_assert_boundary(&mut preconditions, &mut ensures, &mut return_expr);
    preconditions = preconditions
        .into_iter()
        .map(preserve_transparent_adapter_views)
        .collect();
    ensures = ensures
        .into_iter()
        .map(preserve_transparent_adapter_views)
        .collect();
    return_expr = return_expr.map(preserve_transparent_adapter_views);

    Ok(Some(PreparedAssertion {
        preconditions,
        ensures,
        return_expr,
        mode_overrides: wiring.mode_overrides,
        closure_capture_infos: wiring.closure_capture_infos,
        has_mutating_call_effect,
        is_contractless: false,
        containing_requires_false,
        fn_path,
        loc,
        expr_text: expr_text.to_string(),
    }))
}

pub(super) fn filter_len_only_irrelevant_facts(
    assertion: &PureExpr,
    assumed_facts: &mut Vec<PureExpr>,
) -> usize {
    if assumed_facts.is_empty() || !is_len_only_assertion(assertion) {
        return 0;
    }

    let mut relevant_len_receivers = collect_len_receiver_names(assertion);
    if relevant_len_receivers.is_empty() {
        return 0;
    }
    let mut relevant_scalars = assertion.free_vars();
    for receiver in &relevant_len_receivers {
        relevant_scalars.remove(receiver);
    }

    let mut retained = vec![false; assumed_facts.len()];
    loop {
        let mut changed = false;
        for (idx, fact) in assumed_facts.iter().enumerate() {
            if retained[idx] || contains_non_len_method_or_quantifier(fact) {
                continue;
            }

            let fact_len_receivers = collect_len_receiver_names(fact);
            let keep = if fact_len_receivers.is_empty() {
                let vars = fact.free_vars();
                !vars.is_disjoint(&relevant_scalars)
            } else {
                !fact_len_receivers.is_disjoint(&relevant_len_receivers)
            };
            if !keep {
                continue;
            }

            retained[idx] = true;
            changed = true;
            relevant_len_receivers.extend(fact_len_receivers);
            let mut vars = fact.free_vars();
            for receiver in &relevant_len_receivers {
                vars.remove(receiver);
            }
            relevant_scalars.extend(vars);
        }
        if !changed {
            break;
        }
    }

    let before = assumed_facts.len();
    *assumed_facts = assumed_facts
        .iter()
        .cloned()
        .zip(retained)
        .filter_map(|(fact, keep)| keep.then_some(fact))
        .collect();
    before - assumed_facts.len()
}

fn is_len_only_assertion(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => true,
        PureExpr::BinOp(left, _, right) => {
            is_len_only_assertion(left) && is_len_only_assertion(right)
        }
        PureExpr::UnOp(_, operand)
        | PureExpr::Old(operand)
        | PureExpr::Deref(operand)
        | PureExpr::Final(operand)
        | PureExpr::View(operand) => is_len_only_assertion(operand),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            is_len_only_assertion(cond)
                && is_len_only_assertion(then_expr)
                && is_len_only_assertion(else_expr)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            matches!(method.as_str(), "len" | "len_logic")
                && args.is_empty()
                && is_len_receiver_expr(receiver)
        }
        _ => false,
    }
}

fn is_len_receiver_expr(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, _) => true,
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => is_len_receiver_expr(inner),
        _ => false,
    }
}

fn len_receiver_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => len_receiver_name(inner),
        _ => None,
    }
}

fn collect_len_receiver_names(expr: &PureExpr) -> HashSet<String> {
    let mut receivers = HashSet::new();
    collect_len_receiver_names_into(expr, &mut receivers);
    receivers
}

fn collect_len_receiver_names_into(expr: &PureExpr, receivers: &mut HashSet<String>) {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if matches!(method.as_str(), "len" | "len_logic") && args.is_empty() {
                if let Some(name) = len_receiver_name(receiver) {
                    receivers.insert(name.to_string());
                }
            }
            collect_len_receiver_names_into(receiver, receivers);
            for arg in args {
                collect_len_receiver_names_into(arg, receivers);
            }
        }
        PureExpr::BinOp(left, _, right) => {
            collect_len_receiver_names_into(left, receivers);
            collect_len_receiver_names_into(right, receivers);
        }
        PureExpr::UnOp(_, operand)
        | PureExpr::Old(operand)
        | PureExpr::Deref(operand)
        | PureExpr::Final(operand)
        | PureExpr::View(operand) => collect_len_receiver_names_into(operand, receivers),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_len_receiver_names_into(cond, receivers);
            collect_len_receiver_names_into(then_expr, receivers);
            collect_len_receiver_names_into(else_expr, receivers);
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                collect_len_receiver_names_into(arg, receivers);
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_len_receiver_names_into(scrutinee, receivers);
            for arm in arms {
                collect_len_receiver_names_into(&arm.body, receivers);
            }
        }
        PureExpr::Let { value, body, .. } => {
            collect_len_receiver_names_into(value, receivers);
            collect_len_receiver_names_into(body, receivers);
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_len_receiver_names_into(assumption, receivers);
            collect_len_receiver_names_into(body, receivers);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_len_receiver_names_into(obligation, receivers);
            collect_len_receiver_names_into(body, receivers);
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            collect_len_receiver_names_into(body, receivers);
            for trigger in triggers {
                for trigger_expr in trigger {
                    collect_len_receiver_names_into(trigger_expr, receivers);
                }
            }
        }
        PureExpr::Closure { body, .. } => collect_len_receiver_names_into(body, receivers),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
        _ => {}
    }
}

fn contains_non_len_method_or_quantifier(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            !(matches!(method.as_str(), "len" | "len_logic") && args.is_empty())
                || contains_non_len_method_or_quantifier(receiver)
                || args.iter().any(contains_non_len_method_or_quantifier)
        }
        PureExpr::Forall { .. } | PureExpr::Exists { .. } | PureExpr::Closure { .. } => true,
        PureExpr::LogicFnCall { .. } | PureExpr::Match { .. } => true,
        PureExpr::BinOp(left, _, right) => {
            contains_non_len_method_or_quantifier(left)
                || contains_non_len_method_or_quantifier(right)
        }
        PureExpr::UnOp(_, operand)
        | PureExpr::Old(operand)
        | PureExpr::Deref(operand)
        | PureExpr::Final(operand)
        | PureExpr::View(operand) => contains_non_len_method_or_quantifier(operand),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_non_len_method_or_quantifier(cond)
                || contains_non_len_method_or_quantifier(then_expr)
                || contains_non_len_method_or_quantifier(else_expr)
        }
        PureExpr::Let { value, body, .. } => {
            contains_non_len_method_or_quantifier(value)
                || contains_non_len_method_or_quantifier(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_non_len_method_or_quantifier(assumption)
                || contains_non_len_method_or_quantifier(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_non_len_method_or_quantifier(obligation)
                || contains_non_len_method_or_quantifier(body)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
        _ => false,
    }
}

fn synthesize_transitive_disequalities(
    sources: &[PureExpr],
    existing: &[PureExpr],
) -> Vec<PureExpr> {
    const MAX_SYNTHESIZED_DISEQUALITIES: usize = 128;

    let mut classes: Vec<Vec<PureExpr>> = Vec::new();
    let mut disequalities: Vec<(&PureExpr, &PureExpr)> = Vec::new();
    for fact in sources {
        if let Some((left, right)) = equality_operands(fact) {
            merge_expr_classes(&mut classes, left, right);
        } else if let Some((left, right)) = disequality_operands(fact) {
            disequalities.push((left, right));
        }
    }

    let mut synthesized = Vec::new();
    for (left, right) in disequalities {
        let left_members = expr_class_members(&classes, left);
        let right_members = expr_class_members(&classes, right);
        for left_member in &left_members {
            for right_member in &right_members {
                if left_member == right_member {
                    continue;
                }
                let fact = PureExpr::BinOp(
                    Arc::new(left_member.clone()),
                    BinOp::Ne,
                    Arc::new(right_member.clone()),
                );
                let reverse = PureExpr::BinOp(
                    Arc::new(right_member.clone()),
                    BinOp::Ne,
                    Arc::new(left_member.clone()),
                );
                if existing.contains(&fact)
                    || existing.contains(&reverse)
                    || synthesized.contains(&fact)
                    || synthesized.contains(&reverse)
                {
                    continue;
                }
                synthesized.push(fact);
                if synthesized.len() >= MAX_SYNTHESIZED_DISEQUALITIES {
                    return synthesized;
                }
            }
        }
    }
    synthesized
}

fn equality_operands(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    Some((left, right))
}

fn disequality_operands(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Ne, right) = expr else {
        return None;
    };
    Some((left, right))
}

fn merge_expr_classes(classes: &mut Vec<Vec<PureExpr>>, left: &PureExpr, right: &PureExpr) {
    if left == right {
        return;
    }
    match (
        expr_class_index(classes, left),
        expr_class_index(classes, right),
    ) {
        (Some(left_idx), Some(right_idx)) if left_idx == right_idx => {}
        (Some(left_idx), Some(right_idx)) => {
            let (keep_idx, remove_idx) = if left_idx < right_idx {
                (left_idx, right_idx)
            } else {
                (right_idx, left_idx)
            };
            let removed = classes.remove(remove_idx);
            for expr in removed {
                if !classes[keep_idx].contains(&expr) {
                    classes[keep_idx].push(expr);
                }
            }
        }
        (Some(idx), None) => {
            if !classes[idx].contains(right) {
                classes[idx].push(right.clone());
            }
        }
        (None, Some(idx)) => {
            if !classes[idx].contains(left) {
                classes[idx].push(left.clone());
            }
        }
        (None, None) => classes.push(vec![left.clone(), right.clone()]),
    }
}

fn derive_assertion_final_alias_substitutions(
    substitutions: &mut HashMap<String, PureExpr>,
    facts: &[PureExpr],
    assertion_free_vars: &HashSet<String>,
) {
    if assertion_free_vars.is_empty() {
        return;
    }
    for fact in facts {
        let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
            continue;
        };
        derive_assertion_final_alias_substitution_from_side(
            substitutions,
            left,
            right,
            assertion_free_vars,
        );
        derive_assertion_final_alias_substitution_from_side(
            substitutions,
            right,
            left,
            assertion_free_vars,
        );
    }
}

fn derive_assertion_final_alias_substitution_from_side(
    substitutions: &mut HashMap<String, PureExpr>,
    alias_side: &PureExpr,
    final_side: &PureExpr,
    assertion_free_vars: &HashSet<String>,
) {
    let PureExpr::Var(name, _) = alias_side else {
        return;
    };
    if !assertion_free_vars.contains(name) || substitutions.contains_key(name) {
        return;
    }
    if is_bare_final_carrier(final_side) {
        substitutions.insert(name.clone(), final_side.clone());
    }
}

fn is_bare_final_carrier(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(_, _))
    )
}

fn expr_class_index(classes: &[Vec<PureExpr>], expr: &PureExpr) -> Option<usize> {
    classes
        .iter()
        .position(|class| class.iter().any(|member| member == expr))
}

fn expr_class_members(classes: &[Vec<PureExpr>], expr: &PureExpr) -> Vec<PureExpr> {
    expr_class_index(classes, expr)
        .map(|idx| classes[idx].clone())
        .unwrap_or_else(|| vec![expr.clone()])
}

pub(super) fn substitute_precise_final_update_carriers(
    expr: &PureExpr,
    facts: &[PureExpr],
) -> PureExpr {
    let aliases = collect_precise_final_update_aliases(facts);
    if aliases.is_empty() {
        return expr.clone();
    }
    rewrite_precise_final_update_expr(expr, &aliases, 0)
}

fn collect_precise_final_update_aliases(facts: &[PureExpr]) -> HashMap<PureExpr, PureExpr> {
    let mut aliases = HashMap::new();
    for fact in facts {
        let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
            continue;
        };
        collect_precise_final_update_alias_from_side(left, right, &mut aliases);
        collect_precise_final_update_alias_from_side(right, left, &mut aliases);
    }
    aliases
}

fn collect_precise_final_update_alias_from_side(
    final_side: &PureExpr,
    other_side: &PureExpr,
    aliases: &mut HashMap<PureExpr, PureExpr>,
) {
    let Some((name, depth)) = final_base_and_depth(final_side) else {
        return;
    };
    if depth == 0 {
        return;
    }
    if matches!(
        final_base_and_depth(other_side),
        Some((other_name, other_depth)) if other_name == name && other_depth < depth
    ) {
        return;
    }
    if final_update_alias_is_plain_var(other_side) {
        return;
    }
    aliases
        .entry(final_side.clone())
        .or_insert_with(|| other_side.clone());
}

fn final_update_alias_is_plain_var(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(_, _))
}

fn rewrite_precise_final_update_expr(
    expr: &PureExpr,
    aliases: &HashMap<PureExpr, PureExpr>,
    depth: usize,
) -> PureExpr {
    if depth > 16 {
        return expr.clone();
    }
    if let Some(alias) = aliases.get(expr) {
        return rewrite_precise_final_update_expr(alias, aliases, depth + 1);
    }
    match expr {
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(rewrite_precise_final_update_expr(left, aliases, depth)),
            *op,
            Arc::new(rewrite_precise_final_update_expr(right, aliases, depth)),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(rewrite_precise_final_update_expr(inner, aliases, depth)),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(rewrite_precise_final_update_expr(cond, aliases, depth)),
            Arc::new(rewrite_precise_final_update_expr(then_expr, aliases, depth)),
            Arc::new(rewrite_precise_final_update_expr(else_expr, aliases, depth)),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(rewrite_precise_final_update_expr(
            inner, aliases, depth,
        ))),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(rewrite_precise_final_update_expr(
            inner, aliases, depth,
        ))),
        PureExpr::Final(inner) => {
            let rewritten = PureExpr::Final(Arc::new(rewrite_precise_final_update_expr(
                inner, aliases, depth,
            )));
            aliases.get(&rewritten).map_or(rewritten, |alias| {
                rewrite_precise_final_update_expr(alias, aliases, depth + 1)
            })
        }
        PureExpr::View(inner) => PureExpr::View(Arc::new(rewrite_precise_final_update_expr(
            inner, aliases, depth,
        ))),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(rewrite_precise_final_update_expr(receiver, aliases, depth)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_precise_final_update_expr(arg, aliases, depth))
                .collect(),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let bound_names = HashSet::from([var.as_str()]);
            let scoped_aliases = precise_aliases_without_bound_names(aliases, &bound_names);
            PureExpr::Forall {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(rewrite_precise_final_update_expr(
                    body,
                    &scoped_aliases,
                    depth,
                )),
                triggers: triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|part| {
                                rewrite_precise_final_update_expr(part, &scoped_aliases, depth)
                            })
                            .collect()
                    })
                    .collect(),
            }
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let bound_names = HashSet::from([var.as_str()]);
            let scoped_aliases = precise_aliases_without_bound_names(aliases, &bound_names);
            PureExpr::Exists {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(rewrite_precise_final_update_expr(
                    body,
                    &scoped_aliases,
                    depth,
                )),
                triggers: triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|part| {
                                rewrite_precise_final_update_expr(part, &scoped_aliases, depth)
                            })
                            .collect()
                    })
                    .collect(),
            }
        }
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(rewrite_precise_final_update_expr(scrutinee, aliases, depth)),
            arms: arms
                .iter()
                .map(|arm| {
                    let bound_names: HashSet<&str> =
                        arm.pattern.bound_names().into_iter().collect();
                    let scoped_aliases = precise_aliases_without_bound_names(aliases, &bound_names);
                    trust_wp_core::formula::MatchArm {
                        pattern: arm.pattern.clone(),
                        body: rewrite_precise_final_update_expr(&arm.body, &scoped_aliases, depth),
                    }
                })
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_precise_final_update_expr(arg, aliases, depth))
                .collect(),
        },
        PureExpr::Let { var, value, body } => {
            let bound_names = HashSet::from([var.as_str()]);
            let scoped_aliases = precise_aliases_without_bound_names(aliases, &bound_names);
            PureExpr::Let {
                var: var.clone(),
                value: Arc::new(rewrite_precise_final_update_expr(value, aliases, depth)),
                body: Arc::new(rewrite_precise_final_update_expr(
                    body,
                    &scoped_aliases,
                    depth,
                )),
            }
        }
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(rewrite_precise_final_update_expr(
                assumption, aliases, depth,
            )),
            body: Arc::new(rewrite_precise_final_update_expr(body, aliases, depth)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(rewrite_precise_final_update_expr(
                obligation, aliases, depth,
            )),
            body: Arc::new(rewrite_precise_final_update_expr(body, aliases, depth)),
        },
        PureExpr::Closure { params, body } => {
            let bound_names: HashSet<&str> = params.iter().map(|(name, _)| name.as_str()).collect();
            let scoped_aliases = precise_aliases_without_bound_names(aliases, &bound_names);
            PureExpr::Closure {
                params: params.clone(),
                body: Arc::new(rewrite_precise_final_update_expr(
                    body,
                    &scoped_aliases,
                    depth,
                )),
            }
        }
        _ => expr.clone(),
    }
}

fn precise_aliases_without_bound_names(
    aliases: &HashMap<PureExpr, PureExpr>,
    bound_names: &HashSet<&str>,
) -> HashMap<PureExpr, PureExpr> {
    if bound_names.is_empty() {
        return aliases.clone();
    }
    aliases
        .iter()
        .filter(|(from, to)| {
            !expr_references_any_name(from, bound_names)
                && !expr_references_any_name(to, bound_names)
        })
        .map(|(from, to)| (from.clone(), to.clone()))
        .collect()
}

fn expr_references_any_name(expr: &PureExpr, names: &HashSet<&str>) -> bool {
    expr.free_vars()
        .iter()
        .any(|name| names.contains(name.as_str()))
}

fn filter_consumed_final_update_facts(
    facts: &mut Vec<PureExpr>,
    assertion: &PureExpr,
    call_obligations: &[PureExpr],
) {
    let mut referenced_final_roots = HashSet::new();
    collect_final_root_names(assertion, &mut referenced_final_roots);
    for obligation in call_obligations {
        collect_final_root_names(obligation, &mut referenced_final_roots);
    }
    facts.retain(|fact| {
        non_alias_final_update_fact_base(fact).is_none_or(|name| {
            referenced_final_roots.contains(&name) || is_concrete_final_update_fact(fact)
        })
    });
}

fn is_concrete_final_update_fact(fact: &PureExpr) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
        return false;
    };
    is_concrete_final_update_side(left, right) || is_concrete_final_update_side(right, left)
}

fn is_concrete_final_update_side(final_side: &PureExpr, other_side: &PureExpr) -> bool {
    if final_base_and_depth(final_side).is_none_or(|(_, depth)| depth == 0) {
        return false;
    }
    matches!(
        other_side,
        PureExpr::MethodCall { .. } | PureExpr::LogicFnCall { .. } | PureExpr::View(_)
    )
}

fn collect_final_root_names(expr: &PureExpr, roots: &mut HashSet<String>) {
    expr.for_each_recursive(|node| {
        if let PureExpr::Final(inner) = node {
            if let Some((name, _)) = final_base_and_depth(inner) {
                roots.insert(name);
            }
        }
    });
}

fn non_alias_final_update_fact_base(fact: &PureExpr) -> Option<String> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
        return None;
    };
    non_alias_final_update_side(left, right).or_else(|| non_alias_final_update_side(right, left))
}

fn non_alias_final_update_side(final_side: &PureExpr, other_side: &PureExpr) -> Option<String> {
    let (name, depth) = final_base_and_depth(final_side)?;
    if depth == 0 {
        return None;
    }
    if matches!(
        final_base_and_depth(other_side),
        Some((other_name, other_depth)) if other_name == name && other_depth < depth
    ) {
        return None;
    }
    Some(name)
}

fn final_base_and_depth(expr: &PureExpr) -> Option<(String, usize)> {
    match expr {
        PureExpr::Var(name, _) => Some((name.clone(), 0)),
        PureExpr::Final(inner) => {
            let (name, depth) = final_base_and_depth(inner)?;
            Some((name, depth + 1))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::PureExpr;

    use super::derive_has_mutating_call_effect;

    #[test]
    fn wrapped_postcondition_mut_recovers_mutating_provenance() {
        let wrapped_mutating_effect = PureExpr::LetAssume {
            assumption: Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
                method: "postcondition_mut".to_string(),
                args: vec![
                    PureExpr::Var("arg".to_string(), None),
                    PureExpr::Var("state".to_string(), None),
                    PureExpr::Var("result".to_string(), None),
                ],
            }),
            body: Arc::new(PureExpr::Bool(true)),
        };
        let wrapped_non_mutating_effect = PureExpr::LetAssume {
            assumption: Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
                method: "postcondition".to_string(),
                args: vec![
                    PureExpr::Var("arg".to_string(), None),
                    PureExpr::Var("result".to_string(), None),
                ],
            }),
            body: Arc::new(PureExpr::Bool(true)),
        };

        assert!(
            derive_has_mutating_call_effect(false, false, Some(&wrapped_mutating_effect)),
            "wrapped postcondition_mut call effect should recover mutating provenance"
        );
        assert!(
            !derive_has_mutating_call_effect(false, false, Some(&wrapped_non_mutating_effect)),
            "non-mutating wrapped call effect should not be treated as mutating"
        );
    }
}
