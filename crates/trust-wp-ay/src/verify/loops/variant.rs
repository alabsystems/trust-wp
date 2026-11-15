// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variant verification for loops (termination proofs).
//!
//! Implements:
//! - **Variant non-negative**: invariant ∧ condition => variant >= 0
//! - **Variant decrease**: invariant ∧ condition => variant' < variant

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::{
    super::{
        assert_standard_axioms, demote_if_unsound, try_axiom_free_solve, VerificationOutcome,
        VerificationResult,
    },
    encoder_setup::{
        assert_condition_facts, assert_loop_current_chain_alias_constraints,
        collect_loop_sort_plan, encode_and_assert_condition,
        resolve_sat_result_lightweight_outcome_timed, setup_loop_encoder,
    },
    prime_substitutions::build_prime_substitutions,
    LoopVcBase,
};
use crate::{
    encoder::{sort_context::DerivedKind, unsoundness},
    error::EncodingError,
};

/// Verify variant non-negative: invariant ∧ condition => variant >= 0
///
/// This verification condition ensures the variant cannot be negative
/// when the loop continues executing.
#[allow(clippy::unnecessary_wraps)] // Consistent API with verify_initialization/preservation/postcondition
#[allow(clippy::too_many_lines)] // Loop variant VC with vacuity guard and prime substitution
pub(in crate::verify::loops) fn verify_variant_nonneg(
    base: &LoopVcBase<'_>,
    variant: &PureExpr,
) -> Result<VerificationResult, EncodingError> {
    Ok(verify_variant_nonneg_outcome(base, variant)?.result)
}

pub(in crate::verify::loops) fn verify_variant_nonneg_outcome(
    base: &LoopVcBase<'_>,
    variant: &PureExpr,
) -> Result<VerificationOutcome, EncodingError> {
    let invariants = base.invariants;
    let loop_condition = base.loop_condition;
    let condition_is_body_break = base.condition_is_body_break;
    let modified_vars = base.modified_vars;
    let effects = base.effects;
    let config = base.config;
    let variant_stripped = strip_variant_datatype_sort(variant);
    let variant_slice = [variant_stripped.clone()];
    let effect_values: Vec<PureExpr> = effects.direct.values().cloned().collect();
    let deref_effect_values: Vec<PureExpr> = effects.deref.values().cloned().collect();
    let double_deref_effect_values: Vec<PureExpr> =
        effects.double_deref.values().cloned().collect();
    let mut encoder = setup_loop_encoder(
        invariants,
        loop_condition,
        &[
            &variant_slice,
            &effect_values,
            &deref_effect_values,
            &double_deref_effect_values,
        ],
        config,
    )?;
    // Post-bootstrap snapshot: absorb SortFallbackToIntFromLogicFn increments
    // from sort hint collection during bootstrap. (#2062)
    let post_bootstrap = unsoundness::snapshot();
    let sort_plan = collect_loop_sort_plan(&mut encoder, modified_vars, effects.direct);
    sort_plan.apply(&mut encoder)?;
    if !config.transition_facts.is_empty() {
        encoder.register_sort_hints(&config.transition_facts);
        encoder.register_formula_sort_hints(&config.transition_facts);
    }

    // Encode the non-negativity check:
    // invariant ∧ condition ∧ ¬(variant >= 0) should be UNSAT

    // 1. Assert invariants
    for inv in invariants {
        let inv_term = encoder.encode_pure(inv)?;
        encoder.assert_term(inv_term);
    }

    let mut prime_substitutions = HashMap::new();
    if condition_is_body_break && loop_condition.is_some() {
        prime_substitutions =
            build_prime_substitutions(&mut encoder, &sort_plan, modified_vars, effects)?;
    }

    // Compute effective continuation condition once — body-break loops use the
    // primed condition so both the VC assertion and the vacuity probe see the
    // same formula. (#2621)
    let effective_condition: Option<PureExpr> = loop_condition.map(|cond| {
        if condition_is_body_break {
            let modified_set: HashSet<&str> = modified_vars.iter().copied().collect();
            cond.substitute_filtered(&modified_set, &prime_substitutions)
        } else {
            cond.clone()
        }
    });

    // 2. Assert loop condition if present
    if let Some(ref eff_cond) = effective_condition {
        encode_and_assert_condition(&mut encoder, eff_cond)?;
    }
    assert_condition_facts(&mut encoder, config)?;

    let variant_stripped = strip_variant_datatype_sort(variant);

    // Early vacuity guard (#2440, #2621): check if invariants + effective
    // condition + effect constraints are contradictory using a separate encoder.
    // For body-break loops, the primed condition references fresh variable names
    // (e.g. i_prime) that are unconstrained without the effect equalities
    // (e.g. i_prime == i + 2), so include both to match the actual VC base.
    let mut base_exprs: Vec<PureExpr> = invariants.to_vec();
    if let Some(ref eff_cond) = effective_condition {
        base_exprs.push(eff_cond.clone());
    }
    base_exprs.extend(config.condition_facts.iter().cloned());
    if condition_is_body_break {
        for (var, effect_expr) in effects.direct {
            let prime_name = DerivedKind::Prime.format_name(var);
            base_exprs.push(PureExpr::BinOp(
                Arc::new(PureExpr::Var(prime_name, None)),
                BinOp::Eq,
                Arc::new(effect_expr.clone()),
            ));
        }
    }
    if super::encoder_setup::is_base_vacuous(&base_exprs) {
        return Ok(VerificationOutcome::without_provenance(demote_if_unsound(
            &post_bootstrap,
            VerificationResult::Unknown(crate::verify::UnknownReason::SolverMessage(
                crate::verify::solver_tail::VACUOUS_PROOF_MESSAGE.to_string(),
            )),
        )));
    }
    if variant_nonnegative_from_simple_bounds(&variant_stripped, &base_exprs) {
        return super::encoder_setup::prove_structural_loop_goal_outcome(
            config,
            "__trust_wp_loop_variant_nonneg_structural",
        )
        .map(|outcome| demote_outcome_if_unsound(&post_bootstrap, outcome));
    }

    // 3. Assert negation of (variant >= 0), i.e., variant < 0.
    // Rewrite `variant < 0` to `variant + 1 <= 0` (integer-equivalent) to
    // avoid strict-subtraction instability in QF_LIA on SAT-shaped nonneg VCs.
    // This keeps semantics for unbounded Int while reducing timeout regressions.
    //
    // Strip Datatype sort annotations from the variant expression before encoding.
    // Custom struct-typed variants (e.g., `x: CustomVariant` from WellFounded impls)
    // carry ExprSort::Datatype annotations that cause the ay encoder to declare the
    // variable as an uninterpreted sort. This breaks arithmetic operations
    // (add, le) which require Int operands. Stripping the annotation lets the
    // encoder infer Int sort for the variant variable. (#2665, #2696)
    let variant_term_raw = encoder.encode_pure(&variant_stripped)?;
    // Coerce variant term to Int sort as a fallback for any remaining
    // non-Int encodings (e.g., complex expressions, not just Var). (#2696)
    let variant_term = coerce_variant_to_int(&mut encoder, variant_term_raw);
    let zero = encoder.solver_mut().int_const(0);
    let one = encoder.solver_mut().int_const(1);
    let variant_plus_one = encoder.solver_mut().add(variant_term, one);
    let neg_nonneg = encoder.solver_mut().le(variant_plus_one, zero);

    assert_loop_current_chain_alias_constraints(&mut encoder)?;

    // Assert negated goal before axioms so two-phase probe can fire (#2116).
    // SMT assertion order does not affect semantics (conjunction).
    encoder.with_goal_assertions(|encoder| encoder.assert_term(neg_nonneg));

    // Pre-assert Seq ground instances before axiom probe. (#2323)
    if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia) {
        encoder.assert_seq_ground_instances(
            crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
        );
    }

    // Two-phase axiom solving (#2116): try without axioms first.
    // Pure QF_LIA variant VCs do not use these axioms. (#739, #1573)
    if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia)
        && try_axiom_free_solve(&mut encoder).is_none()
    {
        // Pass invariants so eager instantiation can scan for ground closure-spec terms.
        assert_standard_axioms(&mut encoder, invariants, &[])?;
    }

    // Check satisfiability — hard-timeout guarded (#2457). Variant VCs only
    // need the verdict, not a full counterexample model. (#1573)
    let nonneg_result = resolve_sat_result_lightweight_outcome_timed(&mut encoder);

    Ok(demote_outcome_if_unsound(&post_bootstrap, nonneg_result))
}

/// Verify variant decrease: invariant ∧ condition => variant' < variant
///
/// This verification condition ensures the variant strictly decreases
/// with each loop iteration, proving termination.
#[allow(clippy::unnecessary_wraps)] // Consistent API with verify_initialization/preservation/postcondition
#[allow(clippy::too_many_lines)] // Loop variant VC with vacuity guard and prime substitution
pub(in crate::verify::loops) fn verify_variant_decrease(
    base: &LoopVcBase<'_>,
    variant: &PureExpr,
) -> Result<VerificationResult, EncodingError> {
    Ok(verify_variant_decrease_outcome(base, variant)?.result)
}

pub(in crate::verify::loops) fn verify_variant_decrease_outcome(
    base: &LoopVcBase<'_>,
    variant: &PureExpr,
) -> Result<VerificationOutcome, EncodingError> {
    let invariants = base.invariants;
    let loop_condition = base.loop_condition;
    let condition_is_body_break = base.condition_is_body_break;
    let modified_vars = base.modified_vars;
    let effects = base.effects;
    let config = base.config;
    let variant_stripped = strip_variant_datatype_sort(variant);
    let variant_slice = [variant_stripped.clone()];
    let effect_values: Vec<PureExpr> = effects.direct.values().cloned().collect();
    let deref_effect_values: Vec<PureExpr> = effects.deref.values().cloned().collect();
    let double_deref_effect_values: Vec<PureExpr> =
        effects.double_deref.values().cloned().collect();
    let mut encoder = setup_loop_encoder(
        invariants,
        loop_condition,
        &[
            &variant_slice,
            &effect_values,
            &deref_effect_values,
            &double_deref_effect_values,
        ],
        config,
    )?;
    // Post-bootstrap snapshot: absorb SortFallbackToIntFromLogicFn increments
    // from sort hint collection during bootstrap. (#2062)
    let post_bootstrap = unsoundness::snapshot();
    let sort_plan = collect_loop_sort_plan(&mut encoder, modified_vars, effects.direct);
    sort_plan.apply(&mut encoder)?;
    if !config.transition_facts.is_empty() {
        encoder.register_sort_hints(&config.transition_facts);
        encoder.register_formula_sort_hints(&config.transition_facts);
    }

    // Encode the decrease check:
    // invariant ∧ condition ∧ ¬(variant' < variant) should be UNSAT

    // 1. Assert invariants
    for inv in invariants {
        let inv_term = encoder.encode_pure(inv)?;
        encoder.assert_term(inv_term);
    }

    // 2. Introduce proxy variables for body effects and variant values
    let prime_substitutions =
        build_prime_substitutions(&mut encoder, &sort_plan, modified_vars, effects)?;

    // Compute effective continuation condition once — body-break loops use the
    // primed condition so both the VC assertion and the vacuity probe see the
    // same formula. (#2621)
    let effective_condition: Option<PureExpr> = loop_condition.map(|cond| {
        if condition_is_body_break {
            let modified_set: HashSet<&str> = modified_vars.iter().copied().collect();
            cond.substitute_filtered(&modified_set, &prime_substitutions)
        } else {
            cond.clone()
        }
    });

    // 3. Assert loop condition if present.
    if let Some(ref eff_cond) = effective_condition {
        encode_and_assert_condition(&mut encoder, eff_cond)?;
    }
    assert_condition_facts(&mut encoder, config)?;

    for fact in &config.transition_facts {
        let fact_term = encoder.encode_pure(fact)?;
        encoder.assert_term(fact_term);
    }

    // Early vacuity guard (#2440, #2621): check if invariants + effective
    // condition + transition facts + effect constraints are contradictory.
    // For body-break loops, the primed condition references fresh variable
    // names that need the effect equalities to be constrained.
    {
        let mut base_exprs: Vec<PureExpr> = invariants.to_vec();
        if let Some(ref eff_cond) = effective_condition {
            base_exprs.push(eff_cond.clone());
        }
        base_exprs.extend(config.transition_facts.iter().cloned());
        base_exprs.extend(config.condition_facts.iter().cloned());
        if condition_is_body_break {
            for (var, effect_expr) in effects.direct {
                let prime_name = DerivedKind::Prime.format_name(var);
                base_exprs.push(PureExpr::BinOp(
                    Arc::new(PureExpr::Var(prime_name, None)),
                    BinOp::Eq,
                    Arc::new(effect_expr.clone()),
                ));
            }
        }
        if super::encoder_setup::is_base_vacuous(&base_exprs) {
            return Ok(VerificationOutcome::without_provenance(demote_if_unsound(
                &post_bootstrap,
                VerificationResult::Unknown(crate::verify::UnknownReason::SolverMessage(
                    crate::verify::solver_tail::VACUOUS_PROOF_MESSAGE.to_string(),
                )),
            )));
        }
    }

    // 4. Proxy for variant value
    //
    // Strip Datatype sort annotations from the variant expression before encoding,
    // same as in verify_variant_nonneg. (#2665, #2696)
    let variant_term_raw = encoder.encode_pure(&variant_stripped)?;
    // Coerce variant term to Int sort as a fallback for any remaining
    // non-Int encodings (e.g., complex expressions, not just Var). (#2696)
    let variant_term = coerce_variant_to_int(&mut encoder, variant_term_raw);
    let variant_val = encoder.get_or_declare_var("__variant_val", ay_dpll::api::Sort::Int)?;
    let eq_v = encoder.eq_term(variant_val, variant_term);
    encoder.assert_term(eq_v);

    // Proxy for primed variant value (using proxy variable substitution)
    let modified_set: HashSet<&str> = modified_vars.iter().copied().collect();
    let variant_primed_stripped = strip_variant_datatype_sort(
        &variant.substitute_filtered(&modified_set, &prime_substitutions),
    );
    // Register sort hints for the primed variant so primed variable names
    // inherit correct sorts from their base variable context. (#835)
    encoder.register_sort_hints(std::slice::from_ref(&variant_primed_stripped));
    let variant_primed_term_raw = encoder.encode_pure(&variant_primed_stripped)?;
    // Coerce primed variant term to Int sort as a fallback. (#2696)
    let variant_primed_term = coerce_variant_to_int(&mut encoder, variant_primed_term_raw);
    let variant_primed_val =
        encoder.get_or_declare_var("__variant_primed_val", ay_dpll::api::Sort::Int)?;
    let eq_vp = encoder.eq_term(variant_primed_val, variant_primed_term);
    encoder.assert_term(eq_vp);

    // 5. Assert negation of (variant_primed < variant).
    // ¬(a < b) ↔ a >= b
    let not_decrease = encoder.solver_mut().ge(variant_primed_val, variant_val);

    assert_loop_current_chain_alias_constraints(&mut encoder)?;

    // Assert negated goal before axioms so two-phase probe can fire (#2116).
    // SMT assertion order does not affect semantics (conjunction).
    encoder.with_goal_assertions(|encoder| encoder.assert_term(not_decrease));

    // Pre-assert Seq ground instances before axiom probe. (#2323)
    if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia) {
        encoder.assert_seq_ground_instances(
            crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
        );
    }

    // Two-phase axiom solving (#2116): try without axioms first.
    // Pure QF_LIA variant VCs do not use these axioms. (#739, #1573)
    if !matches!(encoder.logic(), ay_dpll::api::Logic::QfLia)
        && try_axiom_free_solve(&mut encoder).is_none()
    {
        // Pass invariants so eager instantiation can scan for ground closure-spec terms.
        assert_standard_axioms(&mut encoder, invariants, &[])?;
    }

    // Check satisfiability — hard-timeout guarded (#2457). Variant VCs only
    // need the verdict, not a full counterexample model. (#1573)
    let decrease_result = resolve_sat_result_lightweight_outcome_timed(&mut encoder);

    Ok(demote_outcome_if_unsound(&post_bootstrap, decrease_result))
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

/// Recursively strip `ExprSort::Datatype` annotations from a variant expression.
///
/// When a loop `#[variant(x)]` references a struct-typed variable (e.g.,
/// `x: CustomVariant`), MIR type enrichment annotates it with
/// `ExprSort::Datatype(...)`. The ay encoder would then declare `x` as an
/// uninterpreted sort, breaking all integer arithmetic on the variant
/// (non-negativity checks, decrease checks). Stripping the Datatype
/// annotation lets the encoder fall back to Int sort inference for the
/// variable and its field accessors. (#2665)
///
/// This recursively strips Datatype annotations from ALL Var nodes in the
/// expression tree. For compound variant expressions (e.g., `tuple_get_0(x)`
/// or arithmetic on struct fields), inner Var nodes may carry Datatype
/// annotations that would cause the encoder to declare them as uninterpreted
/// sorts. Recursive stripping ensures the full expression encodes with
/// correct Int sorts throughout. (#2665)
fn strip_variant_datatype_sort(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::Var(name, Some(trust_wp_core::formula::ExprSort::Datatype(_))) => {
            PureExpr::Var(name.clone(), None)
        }
        PureExpr::BinOp(lhs, op, rhs) => {
            let new_lhs = strip_variant_datatype_sort(lhs);
            let new_rhs = strip_variant_datatype_sort(rhs);
            PureExpr::BinOp(Arc::new(new_lhs), *op, Arc::new(new_rhs))
        }
        PureExpr::UnOp(op, inner) => {
            let new_inner = strip_variant_datatype_sort(inner);
            PureExpr::UnOp(*op, Arc::new(new_inner))
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            let new_cond = strip_variant_datatype_sort(cond);
            let new_then = strip_variant_datatype_sort(then_expr);
            let new_else = strip_variant_datatype_sort(else_expr);
            PureExpr::Ite(Arc::new(new_cond), Arc::new(new_then), Arc::new(new_else))
        }
        PureExpr::LogicFnCall { name, args } => {
            let new_args: Vec<PureExpr> = args.iter().map(strip_variant_datatype_sort).collect();
            PureExpr::LogicFnCall {
                name: name.clone(),
                args: new_args,
            }
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_receiver = strip_variant_datatype_sort(receiver);
            let new_args: Vec<PureExpr> = args.iter().map(strip_variant_datatype_sort).collect();
            PureExpr::MethodCall {
                receiver: Arc::new(new_receiver),
                method: method.clone(),
                args: new_args,
            }
        }
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(strip_variant_datatype_sort(inner))),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(strip_variant_datatype_sort(inner))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(strip_variant_datatype_sort(inner))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(strip_variant_datatype_sort(inner))),
        other => other.clone(),
    }
}

fn variant_nonnegative_from_simple_bounds(variant: &PureExpr, facts: &[PureExpr]) -> bool {
    match variant {
        PureExpr::Int(value) => *value >= 0,
        PureExpr::Var(name, sort) if is_int_like_sort(sort.as_ref()) => facts
            .iter()
            .any(|fact| fact_makes_var_nonnegative(fact, name)),
        PureExpr::BinOp(left, BinOp::Add, right) => {
            variant_nonnegative_from_simple_bounds(left, facts)
                && variant_nonnegative_from_simple_bounds(right, facts)
        }
        PureExpr::Ite(_, then_expr, else_expr) => {
            variant_nonnegative_from_simple_bounds(then_expr, facts)
                && variant_nonnegative_from_simple_bounds(else_expr, facts)
        }
        _ => false,
    }
}

fn is_int_like_sort(sort: Option<&ExprSort>) -> bool {
    matches!(sort, None | Some(ExprSort::Int))
}

fn fact_makes_var_nonnegative(fact: &PureExpr, var_name: &str) -> bool {
    match fact {
        PureExpr::BinOp(left, BinOp::And, right) => {
            fact_makes_var_nonnegative(left, var_name)
                || fact_makes_var_nonnegative(right, var_name)
        }
        PureExpr::BinOp(left, BinOp::Ge, right) => {
            int_like_var_name(left).is_some_and(|name| name == var_name)
                && int_literal(right).is_some_and(|value| value >= 0)
        }
        PureExpr::BinOp(left, BinOp::Gt, right) => {
            int_like_var_name(left).is_some_and(|name| name == var_name)
                && int_literal(right).is_some_and(|value| value >= -1)
        }
        PureExpr::BinOp(left, BinOp::Le, right) => {
            int_literal(left).is_some_and(|value| value >= 0)
                && int_like_var_name(right).is_some_and(|name| name == var_name)
        }
        PureExpr::BinOp(left, BinOp::Lt, right) => {
            int_literal(left).is_some_and(|value| value >= -1)
                && int_like_var_name(right).is_some_and(|name| name == var_name)
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            (int_like_var_name(left).is_some_and(|name| name == var_name)
                && int_literal(right).is_some_and(|value| value >= 0))
                || (int_literal(left).is_some_and(|value| value >= 0)
                    && int_like_var_name(right).is_some_and(|name| name == var_name))
        }
        _ => false,
    }
}

fn int_like_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, sort) if is_int_like_sort(sort.as_ref()) => Some(name),
        _ => None,
    }
}

fn int_literal(expr: &PureExpr) -> Option<i64> {
    match expr {
        PureExpr::Int(value) => Some(*value),
        _ => None,
    }
}

/// Coerce a variant term to Int sort if it is not already Int.
///
/// Custom `#[variant]` expressions may encode to non-Int sorts (e.g.,
/// `Uninterpreted("CustomVariant")` from `WellFounded` impls). Variant
/// arithmetic (add, le, ge, eq) requires Int operands. When the term is
/// already Int, it is returned unchanged. Otherwise, a fresh unconstrained
/// Int constant is used as a conservative bridge — the solver will not
/// derive false conclusions about the value, and the variant check becomes
/// Unknown rather than panicking with a sort mismatch. (#2696)
///
/// Bool terms are converted losslessly via `ite(b, 1, 0)`.
fn coerce_variant_to_int(
    encoder: &mut crate::encoder::AYEncoder,
    term: ay_dpll::api::Term,
) -> ay_dpll::api::Term {
    use std::sync::atomic::{AtomicU64, Ordering};
    let sort = encoder.solver_mut().get_sort(term);
    if sort == ay_dpll::api::Sort::Int {
        return term;
    }
    if sort == ay_dpll::api::Sort::Bool {
        let one = encoder.solver_mut().int_const(1);
        let zero = encoder.solver_mut().int_const(0);
        return encoder.solver_mut().ite(term, one, zero);
    }
    // Non-Int, non-Bool: fresh unconstrained Int constant. Conservative —
    // the variant check will be Unknown rather than panicking.
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
    encoder.solver_mut().declare_const(
        &format!("__trust_wp_variant_coerce_{id}"),
        ay_dpll::api::Sort::Int,
    )
}

#[cfg(test)]
mod tests {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    use super::*;

    fn datatype_sort(name: &str) -> ExprSort {
        ExprSort::Datatype(intern_sort_name(name))
    }

    #[test]
    fn test_strip_variant_datatype_sort_removes_datatype() {
        let expr = PureExpr::Var("x".to_string(), Some(datatype_sort("Foo")));
        let stripped = strip_variant_datatype_sort(&expr);
        assert_eq!(stripped, PureExpr::Var("x".to_string(), None));
    }

    #[test]
    fn test_strip_variant_datatype_sort_preserves_int_sort() {
        let expr = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
        let stripped = strip_variant_datatype_sort(&expr);
        assert_eq!(
            stripped,
            PureExpr::Var("x".to_string(), Some(ExprSort::Int))
        );
    }

    #[test]
    fn test_strip_variant_datatype_sort_preserves_no_sort() {
        let expr = PureExpr::Var("x".to_string(), None);
        let stripped = strip_variant_datatype_sort(&expr);
        assert_eq!(stripped, PureExpr::Var("x".to_string(), None));
    }

    #[test]
    fn test_strip_variant_datatype_sort_recursive_in_binop() {
        let x_dt = PureExpr::Var("x".to_string(), Some(datatype_sort("Foo")));
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("n".to_string(), None)),
            BinOp::Sub,
            Arc::new(x_dt),
        );
        let stripped = strip_variant_datatype_sort(&expr);
        match stripped {
            PureExpr::BinOp(lhs, BinOp::Sub, rhs) => {
                assert_eq!(*lhs, PureExpr::Var("n".to_string(), None));
                assert_eq!(*rhs, PureExpr::Var("x".to_string(), None));
            }
            other => panic!("expected BinOp, got {other:?}"),
        }
    }

    #[test]
    fn test_strip_variant_datatype_sort_recursive_in_logic_fn_call() {
        let x_dt = PureExpr::Var("x".to_string(), Some(datatype_sort("Bar")));
        let expr = PureExpr::LogicFnCall {
            name: "tuple_get_0".to_string(),
            args: vec![x_dt],
        };
        let stripped = strip_variant_datatype_sort(&expr);
        match stripped {
            PureExpr::LogicFnCall { name, args } => {
                assert_eq!(name, "tuple_get_0");
                assert_eq!(args.len(), 1);
                assert_eq!(args[0], PureExpr::Var("x".to_string(), None));
            }
            other => panic!("expected LogicFnCall, got {other:?}"),
        }
    }

    #[test]
    fn test_strip_variant_datatype_sort_leaves_non_datatype_sorts() {
        // Seq sort should be preserved
        let expr = PureExpr::Var("v".to_string(), Some(ExprSort::Seq));
        let stripped = strip_variant_datatype_sort(&expr);
        assert_eq!(
            stripped,
            PureExpr::Var("v".to_string(), Some(ExprSort::Seq))
        );
    }

    #[test]
    fn test_strip_variant_datatype_sort_recursive_in_ite() {
        let x_dt = PureExpr::Var("x".to_string(), Some(datatype_sort("Foo")));
        let expr = PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(x_dt),
            Arc::new(PureExpr::Int(0)),
        );
        let stripped = strip_variant_datatype_sort(&expr);
        match stripped {
            PureExpr::Ite(_, then_branch, _) => {
                assert_eq!(*then_branch, PureExpr::Var("x".to_string(), None));
            }
            other => panic!("expected Ite, got {other:?}"),
        }
    }

    #[test]
    fn test_variant_nonnegative_from_simple_bounds_proves_sum() {
        let facts = vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("a".to_string(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::Int(0)),
                BinOp::Le,
                Arc::new(PureExpr::Var("b".to_string(), None)),
            ),
        ];
        let variant = PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("b".to_string(), None)),
        );

        assert!(variant_nonnegative_from_simple_bounds(&variant, &facts));
    }

    #[test]
    fn test_variant_nonnegative_from_simple_bounds_rejects_missing_bound() {
        let facts = vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )];
        let variant = PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("b".to_string(), None)),
        );

        assert!(!variant_nonnegative_from_simple_bounds(&variant, &facts));
    }
}
