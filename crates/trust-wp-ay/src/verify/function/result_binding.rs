// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Result-body binding for function verification.
//!
//! Encodes `result = body` with Bool sort dispatch, Datatype wrapping
//! (Option/Result), SeqValue propagation, and ITE rebinding.
//! Extracted from `verify/function/mod.rs` per #2328.

use std::{
    collections::HashMap,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
    },
};

use ay_dpll::api::{DatatypeConstructor, DatatypeSort, Sort, Term};
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_arity},
    BinOp, ExprSort, MatchArm, Pattern, PureExpr,
};

/// Monotonic counter for generating unique bridge constant names. (#2699)
static RESULT_DT_BRIDGE_COUNTER: AtomicU64 = AtomicU64::new(0);

use tracing::debug;

use super::super::{
    detect_body_constructor_name, expr_contains_result_var, option_datatype_from_constructor_expr,
    result_collection_sort_from_postcondition_with_context,
    result_is_bool_by_postcondition_with_context, result_match_datatype_from_postcondition,
    shared_constraints::infer_result_sort,
};
use crate::{
    encoder::{
        extract_inner_var_annotation,
        match_enc::{datatype_constructor_matches, short_constructor_name, MatchDatatypeKind},
        sort_context::ay_sort_to_expr_sort,
        unsoundness, AYEncoder,
    },
    error::EncodingError,
};

/// Assert `result = body` in the encoder, handling Bool sort, Datatype
/// wrapping (Option/Result), SeqValue propagation, and ITE rebinding.
///
/// No-op when `return_expr` is None and no postcondition references `result`.
/// When `return_expr` is None but postconditions reference `result`, fires an
/// unsoundness counter so `demote_if_unsound` can downgrade. (#2348)
pub(super) fn assert_result_body_binding(
    encoder: &mut AYEncoder,
    return_expr: Option<&PureExpr>,
    ensures: &[PureExpr],
    requires: &[PureExpr],
) -> Result<(), EncodingError> {
    let result_symbol_referenced_in_requires = requires.iter().any(expr_contains_result_var);
    let result_symbol_referenced_in_ensures = ensures.iter().any(expr_contains_result_var);
    let result_symbol_referenced =
        result_symbol_referenced_in_requires || result_symbol_referenced_in_ensures;

    if let Some(result_expr) = return_expr {
        if result_symbol_referenced {
            assert_result_equals_body(encoder, result_expr, ensures, requires)?;
        } else {
            // Even when postconditions do not mention `result`, encoding the
            // body is still semantically relevant: proof-style bodies use
            // LetAssume/LetObligation for recursive lemma calls and path-local
            // obligations, and those side effects are asserted during
            // encode_pure. Skipping body encoding drops those facts entirely.
            // (#994)
            let _ = encoder.encode_pure(result_expr)?;

            // Path condition propagation for proof_assert (#1457):
            // When the return_expr contains LetAssume wrappers (from
            // if-branch conditions, let-binding facts, pattern-match
            // guards), the Bool-body LetAssume encoding produces an
            // implication whose result is discarded above. The
            // assumption is NOT separately asserted, so postconditions
            // cannot use it. Fix: walk the return_expr, extract top-level
            // LetAssume assumptions, encode them, and assert them
            // directly so they become available as solver facts for
            // postcondition verification.
            super::super::shared_constraints::assert_body_let_assume_path_conditions(
                encoder,
                result_expr,
            )?;
        }
    } else if result_symbol_referenced {
        predeclare_unconstrained_result_datatype(encoder, requires, ensures)?;
        if result_symbol_referenced_in_ensures && !result_symbol_referenced_in_requires {
            // return_expr is None but postconditions reference `result` and no
            // requirement constrains it — the SMT variable will be a free
            // value. The solver can pick any value satisfying postconditions,
            // producing false positives. Fire the unsoundness counter so
            // demote_if_unsound can downgrade. (#2348, #2663)
            unsoundness::increment(unsoundness::UnsoundnessCategory::UnconstrainedResultVar);
        }
    }

    Ok(())
}

/// Whether result binding should be delayed from the shared function base into
/// each obligation slice for a match-like return body.
///
/// This intentionally recognizes only the narrow Option-returning implication
/// shapes that benefit from pruning: each match arm returns `Some(...)` or
/// `None`, and at least one implication antecedent structurally selects a match
/// arm while the consequent either tests `result.is_some()`/`result.is_none()`
/// or directly equates `result` with an Option-shaped value. The driver lowers
/// Rust matches to discriminator `Ite` trees, so the same delay is also enabled
/// for slices whose discriminator branch rewrites exactly to the expected
/// result expression.
// The slice-local path can be staged independently from its function/obligation
// call sites. Keep the allowance on the two entrypoints so a clean tree without
// those call sites does not report the whole private helper chain as dead code.
#[allow(dead_code)]
pub(in crate::verify) fn should_use_slice_local_match_result_binding(
    return_expr: Option<&PureExpr>,
    ensures: &[PureExpr],
) -> bool {
    let Some(return_expr) = return_expr else {
        return false;
    };

    if ensures.iter().any(|ensure| {
        super::super::postcondition::result_match_over_option_ite_is_directly_valid(
            ensure,
            Some(return_expr),
        )
    }) {
        return true;
    }

    match return_expr {
        PureExpr::Match { scrutinee, arms } => {
            if arms.is_empty() || !arms.iter().all(|arm| expr_is_option_constructor(&arm.body)) {
                return false;
            }

            ensures.iter().any(|ensure| {
                implication_consequent_can_use_slice_local_result_binding(ensure)
                    && selected_match_arm_for_implication(ensure, scrutinee, arms).is_some()
            })
        }
        _ => ensures.iter().any(|ensure| {
            rewritten_selected_discriminant_ite_body_for_result_equality(ensure, return_expr)
                .is_some()
                || selected_discriminant_ite_body_for_result_predicate(ensure, return_expr)
                    .is_some()
        }),
    }
}

pub(in crate::verify) fn result_match_postcondition_directly_valid(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> bool {
    let Some(return_expr) = return_expr.map(strip_let_assume) else {
        return false;
    };

    if let PureExpr::Match { scrutinee, arms } = return_expr {
        let Some(arm_index) = selected_match_arm_for_implication(ensure, scrutinee, arms) else {
            return false;
        };
        let Some(arm) = arms.get(arm_index) else {
            return false;
        };
        if rewritten_selected_arm_body_for_result_equality(ensure, scrutinee, arm).is_some() {
            return true;
        }
        return result_option_tester_from_implication(ensure)
            .is_some_and(|tester| option_body_matches_result_tester(&arm.body, tester));
    }

    if rewritten_selected_discriminant_ite_body_for_result_equality(ensure, return_expr).is_some() {
        return true;
    }
    if let Some(selected_body) =
        selected_discriminant_ite_body_for_result_predicate(ensure, return_expr)
    {
        return result_option_tester_from_implication(ensure)
            .is_some_and(|tester| option_body_matches_result_tester(&selected_body, tester));
    }
    false
}

fn result_option_tester_from_implication(ensure: &PureExpr) -> Option<&str> {
    let (_, quantifier_body) = collect_forall_skolem_substitutions(ensure);
    let (_, consequent) = implication_parts_without_quantifiers(quantifier_body)?;
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = consequent
    else {
        return None;
    };
    (args.is_empty()
        && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "result")
        && matches!(method.as_str(), "is_some" | "is_none"))
    .then_some(method.as_str())
}

fn option_body_matches_result_tester(body: &PureExpr, tester: &str) -> bool {
    match (
        short_option_constructor_of_expr(strip_let_assume(body)),
        tester,
    ) {
        (Some("Some"), "is_some") | (Some("None"), "is_none") => true,
        _ => false,
    }
}

fn short_option_constructor_of_expr(expr: &PureExpr) -> Option<&'static str> {
    match expr {
        PureExpr::LogicFnCall { name, args } => match short_constructor_name(name) {
            "Some" => Some("Some"),
            "None" if args.is_empty() => Some("None"),
            _ => None,
        },
        PureExpr::Var(name, _) if zero_arg_constructor_name(name).is_some() => Some("None"),
        _ => None,
    }
}

/// Assert the result binding for a single obligation slice after the shared
/// full-match binding has been intentionally skipped.
#[allow(dead_code)]
pub(in crate::verify) fn assert_slice_local_match_result_body_binding(
    encoder: &mut AYEncoder,
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    all_ensures: &[PureExpr],
    requires: &[PureExpr],
) -> Result<(), EncodingError> {
    let Some(return_expr) = return_expr else {
        return assert_result_body_binding(encoder, return_expr, all_ensures, requires);
    };

    if super::super::postcondition::result_match_over_option_ite_is_directly_valid(
        ensure,
        Some(return_expr),
    ) {
        // The matching postcondition is proven structurally by the return
        // branches. Skip the mixed Seq+datatype result binding, but still let
        // top-level LetAssume path conditions from the body enter the base
        // context before the normal negated-postcondition tail handles the
        // false negation and fresh-base vacuity guard.
        super::super::shared_constraints::assert_body_let_assume_path_conditions(
            encoder,
            return_expr,
        )?;
        return Ok(());
    }

    if let PureExpr::Match { scrutinee, arms } = return_expr {
        if let Some(arm_index) = selected_match_arm_for_implication(ensure, scrutinee, arms) {
            debug!("  slice-local result binding: selected match arm {arm_index} for {ensure:?}");
            return assert_result_equals_selected_match_arm(
                encoder,
                ensure,
                scrutinee,
                arms,
                arm_index,
                all_ensures,
            );
        }

        debug!("  slice-local result binding: no selected arm, falling back to full match");
        return assert_result_body_binding(encoder, Some(return_expr), all_ensures, requires);
    }

    if let Some(rewritten_body) =
        rewritten_selected_discriminant_ite_body_for_result_equality(ensure, return_expr)
    {
        debug!(
            "  slice-local result binding: using discriminator-ITE selected \
             body {rewritten_body:?}"
        );
        return assert_result_equals_slice_body_expr(encoder, &rewritten_body, all_ensures);
    }

    if let Some(selected_body) =
        selected_discriminant_ite_body_for_result_predicate(ensure, return_expr)
    {
        debug!(
            "  slice-local result binding: using discriminator-ITE selected \
             predicate body {selected_body:?}"
        );
        return assert_result_equals_slice_body_expr(encoder, &selected_body, all_ensures);
    }

    debug!("  slice-local result binding: no selected discriminator branch, falling back");
    assert_result_body_binding(encoder, Some(return_expr), all_ensures, requires)
}

fn assert_result_equals_selected_match_arm(
    encoder: &mut AYEncoder,
    ensure: &PureExpr,
    scrutinee: &PureExpr,
    arms: &[MatchArm],
    arm_index: usize,
    ensures: &[PureExpr],
) -> Result<(), EncodingError> {
    if let Some(arm) = arms.get(arm_index) {
        if let Some(rewritten_body) =
            rewritten_selected_arm_body_for_result_equality(ensure, scrutinee, arm)
        {
            debug!(
                "  slice-local result binding: using guard-substituted selected \
                 arm body {rewritten_body:?}"
            );
            return assert_result_equals_slice_body_expr(encoder, &rewritten_body, ensures);
        }
    }

    let body_term = encoder.encode_selected_match_arm_body(scrutinee, arms, arm_index, None)?;
    assert_result_equals_slice_body_term(encoder, body_term, arms.get(arm_index), ensures)
}

fn assert_result_equals_slice_body_expr(
    encoder: &mut AYEncoder,
    body_expr: &PureExpr,
    ensures: &[PureExpr],
) -> Result<(), EncodingError> {
    let body_term = match encode_slice_body_for_declared_result(encoder, body_expr)? {
        Some(term) => term,
        None => encoder.encode_pure(body_expr)?,
    };
    let body_sort = encoder.solver().get_sort(body_term);
    let result_var = encoder.get_or_declare_var("result", body_sort.clone())?;
    let eq = encoder.eq_or_iff(result_var, body_term, &body_sort);
    encoder.assert_term(eq);

    encoder.propagate_seq_value(body_term, result_var);
    encoder.propagate_body_view_seq_value_to_result(body_expr);
    if should_rebind_scalar_result_var_body(encoder, body_expr, ensures) {
        encoder.rebind_var_with_authenticated_witness("result", body_term, body_sort, result_var);
        encoder.record_var_expr_alias("result", body_expr.clone());
    }
    Ok(())
}

fn assert_result_equals_slice_body_term(
    encoder: &mut AYEncoder,
    mut body_term: Term,
    arm: Option<&MatchArm>,
    ensures: &[PureExpr],
) -> Result<(), EncodingError> {
    if let Some(arm) = arm {
        if let Some(contextual_term) = encode_slice_body_for_declared_result(encoder, &arm.body)? {
            body_term = contextual_term;
        }
    }
    let body_sort = encoder.solver().get_sort(body_term);
    let result_var = encoder.get_or_declare_var("result", body_sort.clone())?;
    let eq = encoder.eq_or_iff(result_var, body_term, &body_sort);
    encoder.assert_term(eq);

    encoder.propagate_seq_value(body_term, result_var);
    if let Some(arm) = arm {
        encoder.propagate_body_view_seq_value_to_result(&arm.body);
        if should_rebind_scalar_result_var_body(encoder, &arm.body, ensures) {
            encoder
                .rebind_var_with_authenticated_witness("result", body_term, body_sort, result_var);
            encoder.record_var_expr_alias("result", arm.body.clone());
        }
    }
    Ok(())
}

fn encode_slice_body_for_declared_result(
    encoder: &mut AYEncoder,
    body_expr: &PureExpr,
) -> Result<Option<Term>, EncodingError> {
    let Some(Sort::Datatype(dt)) = encoder.var_sort("result").cloned() else {
        return Ok(None);
    };
    try_encode_result_constructor_term(encoder, &dt, body_expr)
}

fn rewritten_selected_arm_body_for_result_equality(
    ensure: &PureExpr,
    scrutinee: &PureExpr,
    arm: &MatchArm,
) -> Option<PureExpr> {
    let (forall_substitutions, quantifier_body) = collect_forall_skolem_substitutions(ensure);
    let (antecedent, consequent) = implication_parts_without_quantifiers(quantifier_body)?;
    let expected_result = result_equality_other_side(consequent)?;
    let candidate = constructor_equality_candidate_for_scrutinee(antecedent, scrutinee)?;

    let mut pattern_substitutions = HashMap::new();
    collect_pattern_value_substitutions(
        &arm.pattern,
        candidate,
        &forall_substitutions,
        &mut pattern_substitutions,
    )?;

    let rewritten_body = arm.body.substitute(&pattern_substitutions);
    let expected_result = expected_result.substitute(&forall_substitutions);
    result_binding_expr_equiv(&rewritten_body, &expected_result).then_some(expected_result)
}

fn rewritten_selected_discriminant_ite_body_for_result_equality(
    ensure: &PureExpr,
    return_expr: &PureExpr,
) -> Option<PureExpr> {
    let (forall_substitutions, quantifier_body) = collect_forall_skolem_substitutions(ensure);
    let (antecedent, consequent) = implication_parts_without_quantifiers(quantifier_body)?;
    let expected_result = result_equality_other_side(consequent)?;
    if let Some(candidate) = constructor_equality_candidate_for_self(antecedent) {
        return rewritten_selected_discriminant_ite_body_for_candidate(
            return_expr,
            expected_result,
            candidate,
            &forall_substitutions,
        );
    }

    let (candidate, bound_vars) = constructor_equality_candidate_in_exists_antecedent(antecedent)?;
    if expr_contains_any_var(expected_result, &bound_vars) {
        return None;
    }
    let selection = constructor_selection_from_expr(candidate)?;
    let selected_body = selected_discriminant_ite_body(return_expr, &selection)?;
    let expected_result = expected_result.substitute(&forall_substitutions);
    result_binding_expr_equiv(selected_body, &expected_result).then_some(expected_result)
}

fn rewritten_selected_discriminant_ite_body_for_candidate(
    return_expr: &PureExpr,
    expected_result: &PureExpr,
    candidate: &PureExpr,
    forall_substitutions: &HashMap<String, PureExpr>,
) -> Option<PureExpr> {
    let selection = constructor_selection_from_expr(candidate)?;
    let selected_body = selected_discriminant_ite_body(return_expr, &selection)?;
    let mut substitutions = HashMap::new();
    collect_driver_scrutinee_substitutions(candidate, forall_substitutions, &mut substitutions)?;
    let rewritten_body = selected_body.substitute(&substitutions);
    let expected_result = expected_result.substitute(&forall_substitutions);
    result_binding_expr_equiv(&rewritten_body, &expected_result).then_some(expected_result)
}

fn selected_discriminant_ite_body_for_result_predicate(
    ensure: &PureExpr,
    return_expr: &PureExpr,
) -> Option<PureExpr> {
    let (_, quantifier_body) = collect_forall_skolem_substitutions(ensure);
    let (antecedent, consequent) = implication_parts_without_quantifiers(quantifier_body)?;
    if result_equality_other_side(consequent).is_some() || !expr_contains_result_var(consequent) {
        return None;
    }

    let candidate = constructor_equality_candidate_in_antecedent(antecedent)?;
    let selection = constructor_selection_from_expr(candidate)?;
    let selected_body = selected_discriminant_ite_body(return_expr, &selection)?;
    Some(selected_body.clone())
}

fn constructor_equality_candidate_in_antecedent(antecedent: &PureExpr) -> Option<&PureExpr> {
    match antecedent {
        PureExpr::Exists { body, .. } => constructor_equality_candidate_in_antecedent(body),
        _ => constructor_equality_candidate_for_self(antecedent),
    }
}

fn constructor_equality_candidate_for_self(antecedent: &PureExpr) -> Option<&PureExpr> {
    let mut conjuncts = Vec::new();
    collect_top_level_conjuncts(antecedent, &mut conjuncts);
    for conjunct in conjuncts {
        let PureExpr::BinOp(left, BinOp::Eq, right) = conjunct else {
            continue;
        };
        if is_var_named(left, "self") && constructor_selection_from_expr(right).is_some() {
            return Some(right.as_ref());
        }
        if is_var_named(right, "self") && constructor_selection_from_expr(left).is_some() {
            return Some(left.as_ref());
        }
    }
    None
}

fn constructor_equality_candidate_in_exists_antecedent(
    antecedent: &PureExpr,
) -> Option<(&PureExpr, Vec<String>)> {
    let PureExpr::Exists { var, body, .. } = antecedent else {
        return None;
    };

    if let Some(candidate) = constructor_equality_candidate_for_self(body) {
        return Some((candidate, vec![var.clone()]));
    }

    let (candidate, mut bound_vars) = constructor_equality_candidate_in_exists_antecedent(body)?;
    bound_vars.push(var.clone());
    Some((candidate, bound_vars))
}

fn expr_contains_any_var(expr: &PureExpr, vars: &[String]) -> bool {
    expr.any_recursive(|node| match node {
        PureExpr::Var(name, _) => vars.iter().any(|var| var == name),
        _ => false,
    })
}

fn selected_discriminant_ite_body<'a>(
    return_expr: &'a PureExpr,
    selection: &ConstructorSelection,
) -> Option<&'a PureExpr> {
    let PureExpr::Ite(cond, then_expr, else_expr) = strip_let_assume(return_expr) else {
        return None;
    };
    let outer_value = discriminant_equality_value(cond, "self")?;
    let outer_branch =
        select_result_discriminant_branch(then_expr, else_expr, outer_value, selection.outer_ctor)?;

    if selection.outer_ctor != "Ok" {
        return Some(strip_let_assume(outer_branch));
    }

    let Some(inner_ctor) = selection.inner_ctor else {
        return Some(strip_let_assume(outer_branch));
    };
    let PureExpr::Ite(inner_cond, inner_then, inner_else) = strip_let_assume(outer_branch) else {
        return None;
    };
    let inner_value = discriminant_equality_value(inner_cond, "self.0")?;
    let inner_branch =
        select_option_discriminant_branch(inner_then, inner_else, inner_value, inner_ctor)?;
    Some(strip_let_assume(inner_branch))
}

fn strip_let_assume(expr: &PureExpr) -> &PureExpr {
    let mut current = expr;
    while let PureExpr::LetAssume { body, .. } = current {
        current = body;
    }
    current
}

fn select_result_discriminant_branch<'a>(
    then_expr: &'a PureExpr,
    else_expr: &'a PureExpr,
    value: i64,
    ctor: &str,
) -> Option<&'a PureExpr> {
    match (value, ctor) {
        (0, "Ok") | (1, "Err") => Some(then_expr),
        (0, "Err") | (1, "Ok") => Some(else_expr),
        _ => None,
    }
}

fn select_option_discriminant_branch<'a>(
    then_expr: &'a PureExpr,
    else_expr: &'a PureExpr,
    value: i64,
    ctor: &str,
) -> Option<&'a PureExpr> {
    match (value, ctor) {
        (0, "None") | (1, "Some") => Some(then_expr),
        (0, "Some") | (1, "None") => Some(else_expr),
        _ => None,
    }
}

fn discriminant_equality_value(cond: &PureExpr, receiver_name: &str) -> Option<i64> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = cond else {
        return None;
    };
    match (left.as_ref(), right.as_ref()) {
        (method, PureExpr::Int(value)) if is_discriminant_call_on(method, receiver_name) => {
            Some(*value)
        }
        (PureExpr::Int(value), method) if is_discriminant_call_on(method, receiver_name) => {
            Some(*value)
        }
        _ => None,
    }
}

fn discriminant_equality_receiver_and_value(cond: &PureExpr) -> Option<(&PureExpr, i64)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = cond else {
        return None;
    };
    match (left.as_ref(), right.as_ref()) {
        (method, PureExpr::Int(value)) => discriminant_call_receiver(method).map(|r| (r, *value)),
        (PureExpr::Int(value), method) => discriminant_call_receiver(method).map(|r| (r, *value)),
        _ => None,
    }
}

fn discriminant_call_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "discriminant" && args.is_empty() => Some(receiver),
        _ => None,
    }
}

fn is_discriminant_call_on(expr: &PureExpr, receiver_name: &str) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "discriminant" && args.is_empty() && is_var_named(receiver, receiver_name)
    )
}

fn collect_driver_scrutinee_substitutions(
    value: &PureExpr,
    forall_substitutions: &HashMap<String, PureExpr>,
    out: &mut HashMap<String, PureExpr>,
) -> Option<()> {
    let PureExpr::LogicFnCall { name, args } = value else {
        return None;
    };
    match short_constructor_name(name) {
        "Err" => {
            let payload = args.first()?;
            out.insert(
                "self.0".to_string(),
                payload.substitute(forall_substitutions),
            );
            Some(())
        }
        "Ok" => {
            let payload = args.first()?;
            out.insert(
                "self.0".to_string(),
                payload.substitute(forall_substitutions),
            );
            if let PureExpr::LogicFnCall { name, args } = payload {
                if short_constructor_name(name) == "Some" {
                    let Some(inner) = args.first() else {
                        return None;
                    };
                    out.insert(
                        "self.0.0".to_string(),
                        inner.substitute(forall_substitutions),
                    );
                }
            }
            Some(())
        }
        _ => None,
    }
}

fn result_binding_expr_equiv(left: &PureExpr, right: &PureExpr) -> bool {
    normalize_option_constructor_expr(left) == normalize_option_constructor_expr(right)
}

fn normalize_option_constructor_expr(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::LogicFnCall { name, args } if short_constructor_name(name) == "Some" => {
            PureExpr::LogicFnCall {
                name: "Some".to_string(),
                args: args.iter().map(normalize_option_constructor_expr).collect(),
            }
        }
        PureExpr::LogicFnCall { name, args }
            if args.is_empty() && short_constructor_name(name) == "None" =>
        {
            PureExpr::Var("None".to_string(), None)
        }
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args.iter().map(normalize_option_constructor_expr).collect(),
        },
        PureExpr::Var(name, _) if zero_arg_constructor_name(name).is_some() => {
            PureExpr::Var(short_constructor_name(name).to_string(), None)
        }
        _ => expr.clone(),
    }
}

fn collect_forall_skolem_substitutions(
    ensure: &PureExpr,
) -> (HashMap<String, PureExpr>, &PureExpr) {
    let mut substitutions = HashMap::new();
    let mut current = ensure;
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
    (substitutions, current)
}

fn implication_parts_without_quantifiers(ensure: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    match ensure {
        PureExpr::BinOp(antecedent, BinOp::Implies, consequent) => Some((antecedent, consequent)),
        _ => None,
    }
}

fn result_equality_other_side(consequent: &PureExpr) -> Option<&PureExpr> {
    match consequent {
        PureExpr::BinOp(left, BinOp::Eq, right) if is_result_var(left.as_ref()) => {
            Some(right.as_ref())
        }
        PureExpr::BinOp(left, BinOp::Eq, right) if is_result_var(right.as_ref()) => {
            Some(left.as_ref())
        }
        _ => None,
    }
}

fn constructor_equality_candidate_for_scrutinee<'a>(
    antecedent: &'a PureExpr,
    scrutinee: &PureExpr,
) -> Option<&'a PureExpr> {
    let mut conjuncts = Vec::new();
    collect_top_level_conjuncts(antecedent, &mut conjuncts);
    for conjunct in conjuncts {
        let PureExpr::BinOp(left, BinOp::Eq, right) = conjunct else {
            continue;
        };
        if same_expr_for_selection(left, scrutinee)
            && constructor_selection_from_expr(right).is_some()
        {
            return Some(right.as_ref());
        }
        if same_expr_for_selection(right, scrutinee)
            && constructor_selection_from_expr(left).is_some()
        {
            return Some(left.as_ref());
        }
    }
    None
}

fn collect_pattern_value_substitutions(
    pattern: &Pattern,
    value: &PureExpr,
    forall_substitutions: &HashMap<String, PureExpr>,
    out: &mut HashMap<String, PureExpr>,
) -> Option<()> {
    match pattern {
        Pattern::Binding(name) => {
            out.insert(name.clone(), value.substitute(forall_substitutions));
            Some(())
        }
        Pattern::Alias { alias, pattern } => {
            out.insert(alias.clone(), value.substitute(forall_substitutions));
            collect_pattern_value_substitutions(pattern, value, forall_substitutions, out)
        }
        Pattern::Constructor { name, inner } => {
            if !constructor_pattern_matches_value(name, value) {
                return None;
            }
            let Some(inner_pattern) = inner.as_deref() else {
                return Some(());
            };
            let inner_value = constructor_value_first_arg(value)?;
            collect_pattern_value_substitutions(
                inner_pattern,
                inner_value,
                forall_substitutions,
                out,
            )
        }
        Pattern::Tuple(elements) => {
            let PureExpr::LogicFnCall { args, .. } = value else {
                return None;
            };
            if elements.len() != args.len() {
                return None;
            }
            for (pattern, value) in elements.iter().zip(args) {
                collect_pattern_value_substitutions(pattern, value, forall_substitutions, out)?;
            }
            Some(())
        }
        Pattern::Wildcard => Some(()),
        Pattern::Literal(literal) if literal == value => Some(()),
        Pattern::Literal(_) => None,
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

fn constructor_pattern_matches_value(pattern_ctor: &str, value: &PureExpr) -> bool {
    match value {
        PureExpr::LogicFnCall { name, .. } => {
            short_constructor_name(pattern_ctor) == short_constructor_name(name)
        }
        PureExpr::Var(name, _) => {
            short_constructor_name(pattern_ctor) == short_constructor_name(name)
        }
        _ => false,
    }
}

fn constructor_value_first_arg(value: &PureExpr) -> Option<&PureExpr> {
    match value {
        PureExpr::LogicFnCall { args, .. } => args.first(),
        _ => None,
    }
}

fn predeclare_unconstrained_result_datatype(
    encoder: &mut AYEncoder,
    requires: &[PureExpr],
    ensures: &[PureExpr],
) -> Result<(), EncodingError> {
    let Some(dt_kind) = result_match_datatype_from_postcondition(ensures)
        .or_else(|| result_match_datatype_from_postcondition(requires))
    else {
        return Ok(());
    };
    let dt = dt_kind.datatype();
    encoder.ensure_datatype_declared(&dt);
    let _ = encoder.get_or_declare_var("result", Sort::Datatype(dt))?;
    Ok(())
}

fn merge_result_datatype_kind_with_body(
    postcondition_kind: Option<MatchDatatypeKind>,
    body_kind: Option<MatchDatatypeKind>,
) -> Option<MatchDatatypeKind> {
    match (postcondition_kind, body_kind) {
        (Some(MatchDatatypeKind::OptionInt), Some(MatchDatatypeKind::OptionPayload(payload))) => {
            Some(MatchDatatypeKind::OptionPayload(payload))
        }
        (Some(MatchDatatypeKind::OptionPayload(payload)), Some(MatchDatatypeKind::OptionInt)) => {
            Some(MatchDatatypeKind::OptionPayload(payload))
        }
        (
            None,
            Some(kind @ (MatchDatatypeKind::OptionInt | MatchDatatypeKind::OptionPayload(_))),
        ) => Some(kind),
        (Some(kind), _) => Some(kind),
        (None, Some(kind)) => Some(kind),
        (None, None) => None,
    }
}

/// Core result-body binding: encode `result = body` with sort-aware dispatch.
///
/// Handles three cases:
/// 1. Bool sort — propagates Bool through temporaries, uses `iff` for equality
/// 2. Datatype sort — wraps body in Option/Result constructor, declares result as Datatype
/// 3. Scalar sort — standard equality with SeqValue propagation and ITE rebinding
fn assert_result_equals_body(
    encoder: &mut AYEncoder,
    result_expr: &PureExpr,
    ensures: &[PureExpr],
    requires: &[PureExpr],
) -> Result<(), EncodingError> {
    let simplified_result_expr = reconstructing_match_scrutinee(result_expr);
    let result_expr = simplified_result_expr.as_ref().unwrap_or(result_expr);

    // If postconditions force `result` to Bool (e.g., `result == true`),
    // propagate that sort through temporary return aliases like `_call_0`
    // before encoding `result = return_expr`.
    //
    // Exception (#1055): if postconditions use `result` in a match with
    // Option/Result constructors, `result` needs Datatype sort — don't
    // force Bool even if `infer_expr_sort(body)` returns Bool.
    let result_datatype_kind = merge_result_datatype_kind_with_body(
        result_match_datatype_from_postcondition(ensures),
        option_datatype_from_constructor_expr(result_expr),
    );
    // Context-aware inference for result sort detection. (#1965)
    //
    // Do not probe constructor-shaped datatype bodies before declaring their
    // synthetic datatype. That analytical probe can hit the Int fallback for
    // user constructors and falsely demote an otherwise sound datatype proof.
    let inferred_result_is_bool = if result_datatype_kind.is_none() {
        let snap = unsoundness::snapshot();
        let is_bool = encoder.infer_expr_sort_with_context(result_expr, None) == Sort::Bool;
        unsoundness::restore(&snap);
        is_bool
    } else {
        false
    };
    // result_is_bool_by_postcondition_with_context probes postconditions using
    // encoder sort state plus a structural Bool oracle. Bracket with snapshot
    // save/restore so this analytical pass does not pollute the demotion
    // baseline if it touches conservative fallback lanes. (#994, #2624)
    let analytical_snap = unsoundness::snapshot();
    let postcondition_says_bool = result_is_bool_by_postcondition_with_context(encoder, ensures);
    unsoundness::restore(&analytical_snap);
    let result_is_bool = result_datatype_kind.is_none()
        && (encoder.is_bool_var("result") || postcondition_says_bool || inferred_result_is_bool);
    if result_is_bool {
        if let PureExpr::Var(alias, _) = result_expr {
            encoder.mark_bool_var(alias);
        }
    }
    if let Some(dt_kind) = result_datatype_kind {
        assert_result_datatype_binding(encoder, result_expr, &dt_kind, requires)?;
    } else if assert_result_declared_datatype_binding(encoder, result_expr)? {
        // The result variable was already declared with a registered struct
        // datatype (for example by a typed postcondition or invariant method),
        // while MIR lowered the return body to __trust_wp_tupleN(...).
        // The datatype binding above materialized the native constructor.
    } else {
        assert_result_scalar_binding(encoder, result_expr, result_is_bool, ensures)?;
    }
    Ok(())
}

fn assert_result_declared_datatype_binding(
    encoder: &mut AYEncoder,
    result_expr: &PureExpr,
) -> Result<bool, EncodingError> {
    let Some(Sort::Datatype(dt)) = encoder.var_sort("result").cloned() else {
        return Ok(false);
    };
    let Some(body_term) = try_encode_result_constructor_term(encoder, &dt, result_expr)? else {
        return Ok(false);
    };
    let result_var = encoder.get_or_declare_var("result", Sort::Datatype(dt.clone()))?;
    let eq = encoder.eq_term(result_var, body_term);
    encoder.assert_term(eq);
    if should_rebind_result_var(result_expr) {
        encoder.rebind_var_with_authenticated_witness(
            "result",
            body_term,
            Sort::Datatype(dt),
            result_var,
        );
        encoder.record_var_expr_alias("result", result_expr.clone());
    }
    Ok(true)
}

fn reconstructing_match_scrutinee(result_expr: &PureExpr) -> Option<PureExpr> {
    let PureExpr::Match { scrutinee, arms } = result_expr else {
        return None;
    };
    if arms.is_empty() || !arms.iter().all(match_arm_reconstructs_payload) {
        return None;
    }
    Some(scrutinee.as_ref().clone())
}

fn match_arm_reconstructs_payload(arm: &MatchArm) -> bool {
    let Pattern::Constructor { name, inner } = &arm.pattern else {
        return false;
    };
    let PureExpr::LogicFnCall {
        name: body_name,
        args,
    } = &arm.body
    else {
        return false;
    };
    if short_constructor_name(name) != short_constructor_name(body_name) {
        return false;
    }
    let Some(pattern_args) = pattern_payload_bindings(inner.as_deref()) else {
        return false;
    };
    args.len() == pattern_args.len()
        && args
            .iter()
            .zip(pattern_args)
            .all(|(arg, binding)| matches!(arg, PureExpr::Var(name, _) if name == binding))
}

fn pattern_payload_bindings(pattern: Option<&Pattern>) -> Option<Vec<&str>> {
    match pattern {
        None => Some(Vec::new()),
        Some(Pattern::Binding(name)) => Some(vec![name.as_str()]),
        Some(Pattern::Tuple(elements)) => {
            let mut bindings = Vec::with_capacity(elements.len());
            for element in elements {
                let Pattern::Binding(name) = element else {
                    return None;
                };
                bindings.push(name.as_str());
            }
            Some(bindings)
        }
        _ => None,
    }
}

/// Whether a result expression's variable name indicates it should be rebound
/// (i.e., is a `call_` or `_call_` alias rather than the literal `result` var).
/// Non-Var expressions always need rebinding.
///
/// Shared between function and mut_borrow verification paths. (#2654)
pub(in crate::verify) fn should_rebind_result_var(result_expr: &PureExpr) -> bool {
    match result_expr {
        PureExpr::Var(name, _) => is_call_result_alias(name),
        _ => true,
    }
}

fn should_rebind_scalar_result_var_body(
    encoder: &AYEncoder,
    result_expr: &PureExpr,
    ensures: &[PureExpr],
) -> bool {
    if matches!(
        result_expr,
        PureExpr::Ite(..) | PureExpr::LetAssume { .. } | PureExpr::LetObligation { .. }
    ) && postcondition_wraps_result_in_constructor(encoder, ensures)
    {
        return false;
    }
    should_rebind_result_var(result_expr)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ResultTemporalComponent {
    Current,
    Final,
}

impl ResultTemporalComponent {
    fn result_name(self) -> &'static str {
        match self {
            Self::Current => "result_current",
            Self::Final => "result_final",
        }
    }

    fn wrap_expr(self, expr: PureExpr) -> PureExpr {
        match self {
            Self::Current => PureExpr::Deref(Arc::new(expr)),
            Self::Final => PureExpr::Final(Arc::new(expr)),
        }
    }
}

fn bind_result_temporal_components_for_mut_ref_body(
    encoder: &mut AYEncoder,
    result_expr: &PureExpr,
    result_sort: &Sort,
    ensures: &[PureExpr],
) -> Result<(), EncodingError> {
    if !matches!(ay_sort_to_expr_sort(result_sort), Some(ExprSort::MutRef(_))) {
        return Ok(());
    }

    for component in [
        ResultTemporalComponent::Current,
        ResultTemporalComponent::Final,
    ] {
        if ensures
            .iter()
            .any(|ensure| expr_references_result_temporal_component(ensure, component))
        {
            bind_result_temporal_component(encoder, result_expr, component)?;
        }
    }
    Ok(())
}

fn bind_result_temporal_component(
    encoder: &mut AYEncoder,
    result_expr: &PureExpr,
    component: ResultTemporalComponent,
) -> Result<(), EncodingError> {
    let component_expr = temporal_component_of_result_expr(result_expr, component);
    let component_term = encoder.encode_pure(&component_expr)?;
    let component_sort = encoder.solver().get_sort(component_term);
    let result_component_name = component.result_name();
    if let Some(existing) = encoder.var_term(result_component_name) {
        if encoder.solver().get_sort(existing) == component_sort {
            let eq = encoder.eq_or_iff(existing, component_term, &component_sort);
            encoder.assert_term(eq);
        }
    }
    encoder.rebind_var(result_component_name, component_term, component_sort);
    encoder.record_var_expr_alias(result_component_name, component_expr);
    Ok(())
}

fn temporal_component_of_result_expr(
    result_expr: &PureExpr,
    component: ResultTemporalComponent,
) -> PureExpr {
    match result_expr {
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::clone(value),
            body: Arc::new(temporal_component_of_result_expr(body, component)),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::clone(assumption),
            body: Arc::new(temporal_component_of_result_expr(body, component)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::clone(obligation),
            body: Arc::new(temporal_component_of_result_expr(body, component)),
        },
        _ => component.wrap_expr(result_expr.clone()),
    }
}

fn expr_references_result_temporal_component(
    expr: &PureExpr,
    component: ResultTemporalComponent,
) -> bool {
    match expr {
        PureExpr::Deref(inner) if component == ResultTemporalComponent::Current => {
            is_result_var(inner)
                || expr_references_result_temporal_component(inner.as_ref(), component)
        }
        PureExpr::Final(inner) if component == ResultTemporalComponent::Final => {
            is_result_var(inner)
                || expr_references_result_temporal_component(inner.as_ref(), component)
        }
        PureExpr::View(inner) if component == ResultTemporalComponent::Current => {
            is_result_var(inner)
                || expr_references_result_temporal_component(inner.as_ref(), component)
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_references_result_temporal_component(inner, component),
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_references_result_temporal_component(lhs, component)
                || expr_references_result_temporal_component(rhs, component)
        }
        PureExpr::UnOp(_, operand) => expr_references_result_temporal_component(operand, component),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_references_result_temporal_component(cond, component)
                || expr_references_result_temporal_component(then_expr, component)
                || expr_references_result_temporal_component(else_expr, component)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            expr_references_result_temporal_component(body, component)
                || triggers
                    .iter()
                    .flatten()
                    .any(|trigger| expr_references_result_temporal_component(trigger, component))
        }
        PureExpr::Match { scrutinee, arms } => {
            expr_references_result_temporal_component(scrutinee, component)
                || arms
                    .iter()
                    .any(|arm| expr_references_result_temporal_component(&arm.body, component))
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter()
            .any(|arg| expr_references_result_temporal_component(arg, component)),
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_references_result_temporal_component(receiver, component)
                || args
                    .iter()
                    .any(|arg| expr_references_result_temporal_component(arg, component))
        }
        PureExpr::Let { value, body, .. } => {
            expr_references_result_temporal_component(value, component)
                || expr_references_result_temporal_component(body, component)
        }
        PureExpr::LetAssume { assumption, body } => {
            expr_references_result_temporal_component(assumption, component)
                || expr_references_result_temporal_component(body, component)
        }
        PureExpr::LetObligation { obligation, body } => {
            expr_references_result_temporal_component(obligation, component)
                || expr_references_result_temporal_component(body, component)
        }
        PureExpr::Closure { body, .. } => {
            expr_references_result_temporal_component(body, component)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

fn is_call_result_alias(name: &str) -> bool {
    name.starts_with("call_") || name.starts_with("_call_")
}

#[derive(Default)]
struct MatchArmSelection {
    outer_ctor: Option<&'static str>,
    inner_ctor: Option<&'static str>,
}

fn selected_match_arm_for_implication(
    ensure: &PureExpr,
    scrutinee: &PureExpr,
    arms: &[MatchArm],
) -> Option<usize> {
    let (antecedent, _) = implication_parts(ensure)?;

    let mut conjuncts = Vec::new();
    collect_top_level_conjuncts(antecedent, &mut conjuncts);
    let mut selection = MatchArmSelection::default();
    for conjunct in conjuncts {
        record_selection_conjunct(conjunct, scrutinee, &mut selection);
    }

    selection.outer_ctor?;
    let mut matches = arms
        .iter()
        .enumerate()
        .filter(|(_, arm)| pattern_matches_selection(&arm.pattern, &selection));
    let (index, _) = matches.next()?;
    matches.next().is_none().then_some(index)
}

fn collect_top_level_conjuncts<'a>(expr: &'a PureExpr, conjuncts: &mut Vec<&'a PureExpr>) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            collect_top_level_conjuncts(lhs, conjuncts);
            collect_top_level_conjuncts(rhs, conjuncts);
        }
        _ => conjuncts.push(expr),
    }
}

fn record_selection_conjunct(
    conjunct: &PureExpr,
    scrutinee: &PureExpr,
    selection: &mut MatchArmSelection,
) {
    if record_constructor_equality_selection(conjunct, scrutinee, selection) {
        return;
    }

    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = conjunct
    else {
        return;
    };
    if !args.is_empty() {
        return;
    }

    if same_expr_for_selection(receiver, scrutinee) {
        match method.as_str() {
            "is_ok" => selection.outer_ctor = Some("Ok"),
            "is_err" => selection.outer_ctor = Some("Err"),
            "is_some" => selection.outer_ctor = Some("Some"),
            "is_none" => selection.outer_ctor = Some("None"),
            _ => {}
        }
        return;
    }

    if receiver_is_unwrap_of_scrutinee(receiver, scrutinee) {
        match method.as_str() {
            "is_some" => selection.inner_ctor = Some("Some"),
            "is_none" => selection.inner_ctor = Some("None"),
            "is_ok" => selection.inner_ctor = Some("Ok"),
            "is_err" => selection.inner_ctor = Some("Err"),
            _ => {}
        }
    }
}

fn record_constructor_equality_selection(
    conjunct: &PureExpr,
    scrutinee: &PureExpr,
    selection: &mut MatchArmSelection,
) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = conjunct else {
        return false;
    };

    let candidate = if same_expr_for_selection(left, scrutinee) {
        right.as_ref()
    } else if same_expr_for_selection(right, scrutinee) {
        left.as_ref()
    } else {
        return false;
    };

    let Some(candidate) = constructor_selection_from_expr(candidate) else {
        return false;
    };
    selection.outer_ctor = Some(candidate.outer_ctor);
    selection.inner_ctor = candidate.inner_ctor;
    true
}

struct ConstructorSelection {
    outer_ctor: &'static str,
    inner_ctor: Option<&'static str>,
}

fn constructor_selection_from_expr(expr: &PureExpr) -> Option<ConstructorSelection> {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            let outer_ctor = option_result_constructor_name(name)?;
            let inner_ctor = args
                .first()
                .and_then(option_result_constructor_name_from_expr);
            Some(ConstructorSelection {
                outer_ctor,
                inner_ctor,
            })
        }
        _ => None,
    }
}

fn option_result_constructor_name_from_expr(expr: &PureExpr) -> Option<&'static str> {
    match expr {
        PureExpr::LogicFnCall { name, .. } => option_result_constructor_name(name),
        PureExpr::Var(name, _) => zero_arg_constructor_name(name),
        _ => None,
    }
}

fn option_result_constructor_name(name: &str) -> Option<&'static str> {
    match short_constructor_name(name) {
        "Ok" => Some("Ok"),
        "Err" => Some("Err"),
        "Some" => Some("Some"),
        "None" => Some("None"),
        _ => None,
    }
}

fn zero_arg_constructor_name(name: &str) -> Option<&'static str> {
    match short_constructor_name(name) {
        "None" => Some("None"),
        _ => None,
    }
}

fn receiver_is_unwrap_of_scrutinee(receiver: &PureExpr, scrutinee: &PureExpr) -> bool {
    matches!(
        receiver,
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "unwrap" && args.is_empty() && same_expr_for_selection(receiver, scrutinee)
    )
}

fn same_expr_for_selection(left: &PureExpr, right: &PureExpr) -> bool {
    left == right
}

fn is_var_named(expr: &PureExpr, expected: &str) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == expected)
}

fn same_expr_ignoring_var_sort(left: &PureExpr, right: &PureExpr) -> bool {
    match (left, right) {
        (PureExpr::Var(left_name, _), PureExpr::Var(right_name, _)) => left_name == right_name,
        (PureExpr::Deref(left), PureExpr::Deref(right))
        | (PureExpr::Final(left), PureExpr::Final(right))
        | (PureExpr::Old(left), PureExpr::Old(right))
        | (PureExpr::View(left), PureExpr::View(right)) => same_expr_ignoring_var_sort(left, right),
        _ => left == right,
    }
}

fn pattern_matches_selection(pattern: &Pattern, selection: &MatchArmSelection) -> bool {
    match pattern {
        Pattern::Constructor { name, inner } => {
            if selection
                .outer_ctor
                .is_some_and(|ctor| short_constructor_name(name) != ctor)
            {
                return false;
            }
            match selection.inner_ctor {
                Some(inner_ctor) => inner
                    .as_deref()
                    .is_some_and(|inner| pattern_has_outer_constructor(inner, inner_ctor)),
                None => true,
            }
        }
        Pattern::Alias { pattern, .. } => pattern_matches_selection(pattern, selection),
        _ => false,
    }
}

fn pattern_has_outer_constructor(pattern: &Pattern, expected: &str) -> bool {
    match pattern {
        Pattern::Constructor { name, .. } => short_constructor_name(name) == expected,
        Pattern::Alias { pattern, .. } => pattern_has_outer_constructor(pattern, expected),
        _ => false,
    }
}

fn implication_consequent_can_use_slice_local_result_binding(ensure: &PureExpr) -> bool {
    let Some((_, consequent)) = implication_parts(ensure) else {
        return false;
    };
    consequent_is_result_option_tester(consequent)
        || consequent_is_direct_result_equality(consequent)
}

fn implication_parts(ensure: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    match ensure {
        PureExpr::Forall { body, .. } => implication_parts(body),
        PureExpr::BinOp(antecedent, BinOp::Implies, consequent) => Some((antecedent, consequent)),
        _ => None,
    }
}

fn consequent_is_result_option_tester(consequent: &PureExpr) -> bool {
    matches!(
        consequent,
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "result")
            && matches!(method.as_str(), "is_some" | "is_none")
    )
}

fn consequent_is_direct_result_equality(consequent: &PureExpr) -> bool {
    match consequent {
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            is_result_var(left.as_ref()) || is_result_var(right.as_ref())
        }
        _ => false,
    }
}

fn is_result_var(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == "result")
}

fn expr_is_option_constructor(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            short_constructor_name(name) == "Some"
                || (args.is_empty() && short_constructor_name(name) == "None")
        }
        PureExpr::Var(name, _) => zero_arg_constructor_name(name).is_some(),
        _ => false,
    }
}

fn assert_result_constructor_branch_guards(
    encoder: &mut AYEncoder,
    result_var: Term,
    dt: &DatatypeSort,
    then_expr: &PureExpr,
    then_guard: Term,
    else_expr: &PureExpr,
    else_guard: Term,
) -> Result<(), EncodingError> {
    let Some(then_ctor) = datatype_branch_constructor_name(dt, then_expr) else {
        return Ok(());
    };
    let Some(else_ctor) = datatype_branch_constructor_name(dt, else_expr) else {
        return Ok(());
    };
    if then_ctor == else_ctor {
        return Ok(());
    }

    assert_result_constructor_implies_guard(encoder, result_var, dt, &then_ctor, then_guard);
    assert_result_constructor_implies_guard(encoder, result_var, dt, &else_ctor, else_guard);
    assert_guarded_constructor_payloads(encoder, result_var, dt, &then_ctor, then_expr)?;
    assert_guarded_constructor_payloads(encoder, result_var, dt, &else_ctor, else_expr)?;
    Ok(())
}

fn assert_guarded_constructor_payloads(
    encoder: &mut AYEncoder,
    result_var: Term,
    dt: &DatatypeSort,
    ctor_name: &str,
    branch_expr: &PureExpr,
) -> Result<(), EncodingError> {
    let Some(args) = datatype_branch_constructor_args(dt, ctor_name, branch_expr) else {
        return Ok(());
    };
    let Some(constructor) = dt.constructors.iter().find(|constructor| {
        datatype_constructor_matches(dt, &constructor.name, ctor_name)
            && constructor.fields.len() == args.len()
    }) else {
        return Ok(());
    };
    let tester = match encoder.safe_datatype_tester(
        "result datatype branch tester",
        dt,
        ctor_name,
        result_var,
    ) {
        Ok(tester) => tester,
        Err(_) => return Ok(()),
    };
    for (field, arg) in constructor.fields.iter().zip(args) {
        let selector = encoder
            .solver
            .try_datatype_selector(&field.name, result_var, field.sort.clone())
            .map_err(|e| {
                EncodingError::solver_error(format!(
                    "result datatype branch selector {} failed: {e}",
                    field.name
                ))
            })?;
        let arg_term = encoder.encode_pure(arg)?;
        let equality = encoder.eq_or_iff(selector, arg_term, &field.sort);
        let implication = encoder.solver.implies(tester.clone(), equality);
        encoder.assert_term(implication);
    }
    Ok(())
}

fn datatype_branch_constructor_args<'a>(
    dt: &DatatypeSort,
    ctor_name: &str,
    expr: &'a PureExpr,
) -> Option<&'a [PureExpr]> {
    match strip_let_assume(expr) {
        PureExpr::LogicFnCall { name, args }
            if short_constructor_name(name) == ctor_name
                && datatype_has_constructor_with_arity(dt, ctor_name, args.len()) =>
        {
            Some(args.as_slice())
        }
        PureExpr::Var(name, _) if short_constructor_name(name) == ctor_name => Some(&[]),
        _ => None,
    }
}

fn assert_guarded_branch_let_assume_path_conditions(
    encoder: &mut AYEncoder,
    branch_guard: Term,
    branch_expr: &PureExpr,
) -> Result<(), EncodingError> {
    let mut current = branch_expr;
    while let PureExpr::LetAssume { assumption, body } = current {
        match encoder.encode_pure(assumption) {
            Ok(term) => {
                let assumption_bool = encoder.coerce_bool_operand(term);
                let guarded = encoder
                    .solver
                    .implies(branch_guard.clone(), assumption_bool);
                encoder.assert_term(guarded);
            }
            Err(e) => {
                unsoundness::increment(unsoundness::UnsoundnessCategory::LetAssumeDropped);
                tracing::warn!(
                    assumption = ?assumption,
                    error = %e,
                    "branch-local LetAssume encoding failed — will propagate as error"
                );
                return Err(e);
            }
        }
        current = body.as_ref();
    }
    Ok(())
}

fn assert_result_constructor_implies_guard(
    encoder: &mut AYEncoder,
    result_var: Term,
    dt: &DatatypeSort,
    ctor_name: &str,
    guard: Term,
) {
    if let Ok(tester) =
        encoder.safe_datatype_tester("result constructor guard tester", dt, ctor_name, result_var)
    {
        let implication = encoder.solver.implies(tester, guard);
        encoder.assert_term(implication);
    }
}

fn datatype_branch_constructor_name(dt: &DatatypeSort, expr: &PureExpr) -> Option<String> {
    match strip_let_assume(expr) {
        PureExpr::LogicFnCall { name, args } => {
            let short = short_constructor_name(name);
            datatype_has_constructor_with_arity(dt, short, args.len()).then(|| short.to_string())
        }
        PureExpr::Var(name, _) => {
            let short = short_constructor_name(name);
            datatype_has_constructor_with_arity(dt, short, 0).then(|| short.to_string())
        }
        _ => None,
    }
}

fn datatype_has_constructor_with_arity(dt: &DatatypeSort, ctor_name: &str, arity: usize) -> bool {
    dt.constructors.iter().any(|ctor| {
        datatype_constructor_matches(dt, &ctor.name, ctor_name) && ctor.fields.len() == arity
    })
}

fn postcondition_wraps_result_in_constructor(encoder: &AYEncoder, ensures: &[PureExpr]) -> bool {
    ensures.iter().any(|ensure| {
        let mut wrapped = false;
        ensure.for_each_recursive(|node| {
            if wrapped {
                return;
            }
            let PureExpr::LogicFnCall { name, args } = node else {
                return;
            };
            if encoder.constructor_datatype(name).is_none() {
                return;
            }
            wrapped = args.iter().any(expr_contains_result_var);
        });
        wrapped
    })
}

/// Datatype result binding: wrap body in Option/Result constructor.
fn assert_result_datatype_binding(
    encoder: &mut AYEncoder,
    result_expr: &PureExpr,
    dt_kind: &MatchDatatypeKind,
    requires: &[PureExpr],
) -> Result<(), EncodingError> {
    // Postcondition uses `result` in a match with Option/Result
    // constructors, but MIR unwrapped the enum constructor so
    // `return_expr` is a bare scalar (e.g., `Bool(true)` instead of
    // `Some(Bool(true))`). Re-wrap the body into the datatype
    // constructor and declare `result` as Datatype sort. (#1055)
    let dt = dt_kind.datatype();
    encoder.ensure_datatype_declared(&dt);
    let result_var = encoder.get_or_declare_var("result", Sort::Datatype(dt.clone()))?;

    debug!("  encoding body (datatype wrap): {result_expr:?}");
    debug!("  vars before: {:?}", encoder.var_names());

    let datatype_ite_expr = strip_let_assume(result_expr);
    if let PureExpr::Ite(cond, then_expr, else_expr) = datatype_ite_expr {
        if !std::ptr::eq(datatype_ite_expr, result_expr) {
            super::super::shared_constraints::assert_body_let_assume_path_conditions(
                encoder,
                result_expr,
            )?;
        }
        // Datatype-returning ITEs are better handled as guarded branch
        // equalities. A raw datatype `ite(...)` term can leave tester
        // predicates like `is-Some(result)` too abstract for model
        // validation even when the branches are already concrete
        // constructors.
        let cond_term = encoder.encode_pure(cond)?;
        let cond_bool = encoder.coerce_bool_operand(cond_term);
        let then_value_expr = strip_let_assume(then_expr);
        let else_value_expr = strip_let_assume(else_expr);
        let then_term = encode_branch_as_datatype(encoder, then_value_expr, dt_kind, &dt)?;
        let else_term = encode_branch_as_datatype(encoder, else_value_expr, dt_kind, &dt)?;
        let then_eq = encoder.eq_or_iff(result_var, then_term, &Sort::Datatype(dt.clone()));
        let else_eq = encoder.eq_or_iff(result_var, else_term, &Sort::Datatype(dt.clone()));
        let then_guarded = encoder.solver.implies(cond_bool.clone(), then_eq);
        let not_cond = encoder.solver.not(cond_bool.clone());
        let else_guarded = encoder.solver.implies(not_cond.clone(), else_eq);
        encoder.assert_term(then_guarded);
        encoder.assert_term(else_guarded);
        assert_guarded_branch_let_assume_path_conditions(encoder, cond_bool.clone(), then_expr)?;
        assert_guarded_branch_let_assume_path_conditions(encoder, not_cond.clone(), else_expr)?;
        assert_result_constructor_branch_guards(
            encoder, result_var, &dt, then_expr, cond_bool, else_expr, not_cond,
        )?;
        assert_nullary_discriminant_result_implications_from_requires(
            encoder, result_var, &dt, cond, then_expr, else_expr, requires,
        )?;
        return Ok(());
    }

    // Use the same branch encoder for non-ITE bodies so constructor
    // detection, sort probing, and bridge fallback stay aligned with the
    // guarded ITE path above.
    let ctor_term = encode_branch_as_datatype(encoder, result_expr, dt_kind, &dt)?;

    debug!("  vars after body: {:?}", encoder.var_names());

    let eq = encoder.eq_or_iff(result_var, ctor_term, &Sort::Datatype(dt.clone()));
    encoder.assert_term(eq);
    assert_guarded_ite_result_equalities(
        encoder,
        result_var,
        &Sort::Datatype(dt.clone()),
        result_expr,
    )?;

    // Rebind `result` to the datatype body term so postcondition
    // encoding inlines the body directly, bypassing ay-dpll's
    // ITE transitivity limitation (#1310, #1572).
    if should_rebind_result_var(result_expr) {
        encoder.rebind_var_with_authenticated_witness(
            "result",
            ctor_term,
            Sort::Datatype(dt),
            result_var,
        );
        encoder.record_var_expr_alias("result", result_expr.clone());
    }
    Ok(())
}

/// Encode a single expression as a Datatype constructor term.
///
/// First tries structural constructor matching via
/// [`try_encode_result_constructor_term`]. If that fails (returns `None`),
/// falls back to encoding the body and wrapping in the default constructor.
///
/// Extracted as a helper for ITE branch handling (#2675): each branch of an
/// ITE body is encoded independently so that different constructors can
/// appear in different branches (e.g., `Some(x)` in the then-branch and
/// `None` in the else-branch).
fn encode_branch_as_datatype(
    encoder: &mut AYEncoder,
    branch_expr: &PureExpr,
    dt_kind: &MatchDatatypeKind,
    dt: &DatatypeSort,
) -> Result<Term, EncodingError> {
    // Recurse into nested ITE bodies so deeply nested conditionals
    // (e.g., if-else chains returning different constructors) are
    // handled correctly at each level. Path conditions are not pushed
    // here because `encode_pure` already handles ITE path conditions
    // internally, and `push_path_condition` is encoder-private.
    if let PureExpr::Ite(cond, then_expr, else_expr) = branch_expr {
        let c_raw = encoder.encode_pure(cond)?;
        let c = encoder.coerce_bool_operand(c_raw);

        let then_dt = encode_branch_as_datatype(encoder, then_expr, dt_kind, dt)?;
        let else_dt = encode_branch_as_datatype(encoder, else_expr, dt_kind, dt)?;

        return Ok(encoder.safe_ite(c, then_dt, else_dt));
    }

    if let Some(term) = try_encode_result_constructor_term(encoder, dt, branch_expr)? {
        return Ok(term);
    }

    // Fallback: encode the body and coerce to Int if necessary (Datatype
    // fields are Sort::Int in OptionInt/ResultIntInt).
    let body_term = encoder.encode_pure(branch_expr)?;
    // Context-aware sort for body coercion decision. (#1965)
    let body_sort = encoder.infer_expr_sort_with_context(branch_expr, None);
    let body_int = if body_sort == Sort::Bool {
        let one = encoder.solver_mut().int_const(1);
        let zero = encoder.solver_mut().int_const(0);
        encoder.solver_mut().ite(body_term, one, zero)
    } else {
        body_term
    };
    // Wrap in the constructor: e.g., Some(ite(true, 1, 0)).
    //
    // If the encoded body is already a datatype value of this sort
    // (e.g., branch_expr is `Some(1)` which encodes to OptionInt),
    // avoid double-wrapping into `Some(Some(1))`. (#1553)
    //
    // When the body is a LogicFnCall with a recognized constructor
    // (e.g., `Err(42)`), use that constructor instead of always
    // defaulting to `Ok`/`Some`. (#1811)
    let ctor_name = detect_body_constructor_name(branch_expr)
        .unwrap_or_else(|| dt_kind.value_constructor_name());
    match encoder.safe_datatype_constructor("result datatype wrap", dt, ctor_name, &[body_int]) {
        Ok(term) => {
            encoder.materialize_ground_native_constructor(dt, ctor_name, term, &[body_int]);
            Ok(term)
        }
        Err(ctor_err) => {
            // Probe whether `body_int` is already a term of the
            // target datatype sort; tester succeeds only when the
            // argument sort matches the datatype.
            if encoder
                .safe_datatype_tester("result datatype wrap body probe", dt, ctor_name, body_int)
                .is_ok()
            {
                Ok(body_int)
            } else {
                // Sort mismatch: the body encodes with a sort that
                // the constructor cannot accept. Bridge to the actual
                // field sort from the constructor definition rather than
                // always bridging to Int. (#2699)
                //
                // Look up the constructor's first field sort to use as
                // the bridge target. This handles cases like:
                // - Option<Vec<T>>: body is Seq(Int), ctor wants Int → bridge to Int
                // - Option<HashMap<K,V>>: body is FMap, ctor wants Seq → bridge to Seq
                // - Custom Result<T, E>: body sort varies per ctor field
                let actual_term_sort = encoder.solver_mut().get_sort(body_int);
                let target_field_sort = dt
                    .constructors
                    .iter()
                    .find(|c| datatype_constructor_matches(dt, &c.name, ctor_name))
                    .and_then(|c| c.fields.first())
                    .map(|f| f.sort.clone());
                if actual_term_sort != Sort::Int
                    || target_field_sort
                        .as_ref()
                        .is_some_and(|fs| *fs != Sort::Int)
                {
                    let bridge_sort = target_field_sort.unwrap_or(Sort::Int);
                    unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
                    let id = RESULT_DT_BRIDGE_COUNTER.fetch_add(1, Ordering::Relaxed);
                    let bridged = encoder
                        .solver_mut()
                        .declare_const(&format!("__result_dt_bridge_{id}"), bridge_sort);
                    match encoder.safe_datatype_constructor(
                        "result datatype wrap bridged",
                        dt,
                        ctor_name,
                        &[bridged],
                    ) {
                        Ok(term) => {
                            encoder.materialize_ground_native_constructor(
                                dt,
                                ctor_name,
                                term,
                                &[bridged],
                            );
                            Ok(term)
                        }
                        Err(bridge_err) => Err(EncodingError::solver_error(format!(
                            "result datatype wrap failed for constructor \
                                 {ctor_name} (bridged): {bridge_err}"
                        ))),
                    }
                } else {
                    Err(EncodingError::solver_error(format!(
                        "result datatype wrap failed for constructor \
                             {ctor_name}: {ctor_err}"
                    )))
                }
            }
        }
    }
}

/// Scalar result binding: standard equality with SeqValue propagation.
fn assert_result_scalar_binding(
    encoder: &mut AYEncoder,
    result_expr: &PureExpr,
    result_is_bool: bool,
    ensures: &[PureExpr],
) -> Result<(), EncodingError> {
    let result_sort = if result_is_bool {
        Sort::Bool
    } else {
        // Bracket with unsoundness snapshot/restore for
        // `SortFallbackToIntFromLogicFn`: this is an ANALYTICAL pre-encoding
        // scan of the body, not an encoding step. The walk descends into match
        // arms and hits user-ADT constructor calls (`Frac1(n + m)` in
        // `bug/1208`) that the AST-level inference cannot resolve — it has no
        // encoder context, so `constructor_datatype` is out of reach — and
        // takes the demoting Int fallback. The value is advisory: the body is
        // encoded immediately below and the post-encoding reconciliation
        // overrides `result_sort` with the real `body_term` sort, and any
        // approximation on the ENCODING path still increments uncovered.
        // Same rationale and pattern as the `#2116` bracket a few lines down
        // and `logic_fn/signature.rs` (#2671, analogous to #2062).
        //
        // Without the bracket this fires as a false demotion whenever a logic
        // function's body matches on a user enum and rebuilds it — the goal
        // proves (`ay_result=unsat`) but the verdict is downgraded to
        // "postcondition unverified". It was previously masked by the
        // encoder-lifetime sort-inference memo swallowing the repeat walk;
        // that memo was a use-after-free oracle and is gone.
        let before_result_infer = unsoundness::snapshot();
        let inferred = infer_result_sort(encoder, result_expr);
        unsoundness::restore_category(
            &before_result_infer,
            unsoundness::UnsoundnessCategory::SortFallbackToIntFromLogicFn,
        );
        // When syntactic inference returns Int (the default fallback),
        // consult the ExprSort annotation from `result_expr` (MIR type
        // info) and sort hints. The annotation is authoritative for
        // non-Int sorts, bypassing the heuristic cascade. (#994 Phase 2d)
        if inferred == Sort::Int {
            let ann = extract_inner_var_annotation(result_expr);
            let resolved = encoder.resolve_var_sort_or_int_with_annotation("result", ann);
            // When all body-based inference returns Int, check postconditions
            // for collection sort evidence (e.g., `result == s.reverse()`
            // where `reverse` returns Seq). Without this, `result` is declared
            // as Int, causing ay sort mismatch panics on `eq(Int, Seq)`. (#2116)
            //
            // Bracket with unsoundness snapshot/restore: infer_expr_sort
            // increments SortFallbackToIntFromLogicFn for LogicFnCall nodes
            // (false positive — analytical scan, not encoding). Same pattern
            // as result_is_bool_by_postcondition bracketing above.
            if resolved == Sort::Int {
                let snap = unsoundness::snapshot();
                let collection =
                    result_collection_sort_from_postcondition_with_context(encoder, ensures);
                unsoundness::restore(&snap);
                collection.unwrap_or(resolved)
            } else {
                resolved
            }
        } else {
            inferred
        }
    };

    debug!("  encoding body: {result_expr:?}");
    debug!("  vars before: {:?}", encoder.var_names());

    let body_term = encoder.encode_pure(result_expr)?;

    debug!("  vars after body: {:?}", encoder.var_names());

    // Post-encoding sort reconciliation (#1296): when pre-encoding inference
    // returns Int (the default) but the body term actually has a non-Int sort
    // (e.g., Datatype(OptionInt) from a match on nested ADTs), upgrade
    // `result` to the body's sort. Without this, `result` stays Int and the
    // `result = body` equality triggers sort coercion, replacing the body with
    // an unconstrained fresh constant and disconnecting `result` from the
    // actual computation.
    let body_term_sort = encoder.solver().get_sort(body_term);
    let result_sort = if result_sort == Sort::Int && body_term_sort != Sort::Int {
        body_term_sort
    } else {
        result_sort
    };
    let result_var = encoder.get_or_declare_var("result", result_sort.clone())?;
    let transparent_body_term = encoder
        .body_inner_term_for_transparent_adapter(result_expr)?
        .unwrap_or(body_term);
    // Assert result = body for counterexample extraction: the SMT
    // constant `result` must exist so counterexample models can report
    // its value. Bool-valued bodies keep the iff expansion here: raw solver
    // equality is sound on the current pin, but it regresses completeness on
    // nested short-circuit / comparison formulas in the verification pipeline.
    let eq = encoder.eq_or_iff(result_var, transparent_body_term, &result_sort);
    encoder.assert_term(eq);
    assert_guarded_ite_result_equalities(encoder, result_var, &result_sort, result_expr)?;

    // Propagate SeqValue from body chain to result variable (#1317).
    encoder.propagate_seq_value(transparent_body_term, result_var);

    // Bridge SeqValue from body's *view* variable to result_view (#1317).
    encoder.propagate_body_view_seq_value_to_result(result_expr);

    // When the body contains an ITE, ALSO bind `result` directly to
    // the body term in the variable map so postcondition encoding
    // inlines the body (#1310).
    //
    // ay-dpll (rev 715ed260) cannot prove transitive equality through
    // ITE terms: `result = ite(c,a,b)` + `f = ite(c,a,b)` ⊬ `result = f`.
    // By binding `result` to the body term, postconditions that reference
    // `result` use the body term inline, allowing the solver to match it
    // against axiom instances without intermediate variable reasoning.
    //
    // Keep arbitrary variable bodies on the equality-only path: rebinding
    // `result` to a user variable can change uninterpreted-function arguments
    // observed by requires/ensures. Synthetic call-result aliases are the
    // exception. Quantified closure laws match on the call-site result term
    // (`call_*`, `_call_*`), so rebind `result` to those aliases directly.
    if should_rebind_scalar_result_var_body(encoder, result_expr, ensures) {
        if matches!(result_expr, PureExpr::Var(..)) {
            debug!("[TRUST_WP_DEBUG] rebinding result to call-result alias: {result_expr:?}");
        }
        encoder.rebind_var_with_authenticated_witness(
            "result",
            transparent_body_term,
            result_sort.clone(),
            result_var,
        );
        encoder.record_var_expr_alias("result", result_expr.clone());
        let result_annotation =
            ay_sort_to_expr_sort(&result_sort).or_else(|| tuple_expr_sort_from_sort(&result_sort));
        let rebound_result_expr = PureExpr::Var("result".to_string(), result_annotation);
        assert_guarded_ite_target_expr_field_equalities(
            encoder,
            &rebound_result_expr,
            result_expr,
        )?;
        bind_result_temporal_components_for_mut_ref_body(
            encoder,
            result_expr,
            &result_sort,
            ensures,
        )?;
    }
    Ok(())
}

/// Encode `expr` with `guard` (when present) pushed on the encoder's
/// path-condition stack.
///
/// The guarded-ITE binding lanes below re-encode branch-scoped expressions
/// OUTSIDE `encode_pure_impl`'s own `Ite` traversal, applying the branch
/// guard manually at the equality level. Side obligations collected during
/// those encodes (`divisor != 0`, shift-amount range — ledger
/// int-shift-full) go through `guard_with_active_path`, which only sees the
/// encoder's path-condition stack — so without this wrapper a branch-body
/// obligation escaped its branch UNGUARDED and could fail the VC from a
/// branch the counterexample never takes (the bits.rs `empty` regression:
/// `if rq_ffs == 0 { 0 } else { val & !(1 << rq) }` collected the
/// else-branch shift-range obligation unguarded and "failed" at
/// `rq_ffs == 0`).
fn encode_pure_under_optional_path_condition(
    encoder: &mut AYEncoder,
    guard: Option<Term>,
    expr: &PureExpr,
) -> Result<Term, EncodingError> {
    match guard {
        Some(guard) => encoder.with_path_condition(guard, |encoder| encoder.encode_pure(expr)),
        None => encoder.encode_pure(expr),
    }
}

fn assert_guarded_ite_result_equalities(
    encoder: &mut AYEncoder,
    result_var: Term,
    result_sort: &Sort,
    result_expr: &PureExpr,
) -> Result<(), EncodingError> {
    assert_guarded_ite_result_equalities_under_guard(
        encoder,
        result_var,
        result_sort,
        None,
        result_expr,
    )
}

fn assert_guarded_ite_result_equalities_under_guard(
    encoder: &mut AYEncoder,
    result_var: Term,
    result_sort: &Sort,
    active_guard: Option<Term>,
    result_expr: &PureExpr,
) -> Result<(), EncodingError> {
    match result_expr {
        PureExpr::Ite(cond, then_expr, else_expr) => {
            // A nested ITE condition is only evaluated under the enclosing
            // branch guard: keep that guard active while encoding it so any
            // side obligations it collects stay branch-scoped.
            let cond_term =
                encode_pure_under_optional_path_condition(encoder, active_guard.clone(), cond)?;
            let cond_bool = encoder.coerce_bool_operand(cond_term);
            let not_cond = encoder.solver.not(cond_bool.clone());
            let then_guard = combine_optional_guard(encoder, active_guard.clone(), cond_bool);
            let else_guard = combine_optional_guard(encoder, active_guard, not_cond);

            assert_guarded_result_branch_equality(
                encoder,
                result_var,
                result_sort,
                then_guard.clone(),
                then_expr,
            )?;
            assert_guarded_result_branch_equality(
                encoder,
                result_var,
                result_sort,
                else_guard.clone(),
                else_expr,
            )?;

            assert_guarded_ite_result_equalities_under_guard(
                encoder,
                result_var,
                result_sort,
                Some(then_guard),
                then_expr,
            )?;
            assert_guarded_ite_result_equalities_under_guard(
                encoder,
                result_var,
                result_sort,
                Some(else_guard),
                else_expr,
            )
        }
        PureExpr::Match { scrutinee, arms } => {
            // Scrutinee/pattern-guard encoding happens under the enclosing
            // branch guard for the same obligation-scoping reason as the
            // nested ITE condition above.
            let guards = match active_guard.clone() {
                Some(outer) => encoder.with_path_condition(outer, |encoder| {
                    encoder.encode_match_arm_active_guards(scrutinee, arms, None)
                })?,
                None => encoder.encode_match_arm_active_guards(scrutinee, arms, None)?,
            };
            for (guard, arm) in guards.into_iter().zip(arms) {
                let branch_guard = combine_optional_guard(encoder, active_guard.clone(), guard);
                assert_guarded_result_branch_equality(
                    encoder,
                    result_var,
                    result_sort,
                    branch_guard.clone(),
                    &arm.body,
                )?;
                assert_guarded_ite_result_equalities_under_guard(
                    encoder,
                    result_var,
                    result_sort,
                    Some(branch_guard),
                    &arm.body,
                )?;
            }
            Ok(())
        }
        PureExpr::LetAssume { assumption, body } => {
            if active_guard.is_some() || expr_has_ite_through_let_assume(body) {
                assert_guarded_or_global_assumption(encoder, active_guard.clone(), assumption)?;
            }
            assert_guarded_ite_result_equalities_under_guard(
                encoder,
                result_var,
                result_sort,
                active_guard,
                body,
            )
        }
        _ => Ok(()),
    }
}

fn expr_has_ite_through_let_assume(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Ite(..) => true,
        PureExpr::LetAssume { body, .. } => expr_has_ite_through_let_assume(body),
        _ => false,
    }
}

fn combine_optional_guard(
    encoder: &mut AYEncoder,
    active_guard: Option<Term>,
    branch_guard: Term,
) -> Term {
    match active_guard {
        Some(active_guard) => encoder.solver.and(active_guard, branch_guard),
        None => branch_guard,
    }
}

fn assert_guarded_or_global_assumption(
    encoder: &mut AYEncoder,
    active_guard: Option<Term>,
    assumption: &PureExpr,
) -> Result<(), EncodingError> {
    // Assumption position: a `LetAssume` fact re-states already-verified
    // call/body knowledge, so shift-amount range obligations embedded in it
    // are owned by the body VALUE encoding — see `with_assumption_position`.
    // The active branch guard additionally scopes any other side assertion
    // the encode emits. (ledger int-shift-full)
    let assumption_term = encoder.with_assumption_position(|encoder| {
        encode_pure_under_optional_path_condition(encoder, active_guard.clone(), assumption)
    })?;
    let assumption_bool = encoder.coerce_bool_operand(assumption_term);
    if let Some(active_guard) = active_guard {
        let guarded = encoder.solver.implies(active_guard, assumption_bool);
        encoder.assert_term(guarded);
    } else {
        encoder.assert_term(assumption_bool);
    }
    Ok(())
}

fn assert_guarded_result_branch_equality(
    encoder: &mut AYEncoder,
    result_var: Term,
    result_sort: &Sort,
    branch_guard: Term,
    branch_expr: &PureExpr,
) -> Result<(), EncodingError> {
    let branch_value_expr = strip_let_assume(branch_expr);
    // Encode the branch body with its guard on the path-condition stack:
    // this lane bypasses `encode_pure_impl`'s own Ite branch scoping, so
    // without the explicit push a branch-body side obligation (divisor != 0,
    // shift-amount range) would be collected UNGUARDED — the bits.rs `empty`
    // false counterexample. (ledger int-shift-full)
    let branch_term = encoder.with_path_condition(branch_guard.clone(), |encoder| {
        if let Sort::Datatype(dt) = result_sort {
            match try_encode_result_constructor_term(encoder, dt, branch_value_expr)? {
                Some(term) => Ok(term),
                None => encoder.encode_pure(branch_value_expr),
            }
        } else {
            encoder.encode_pure(branch_value_expr)
        }
    })?;
    let branch_sort = encoder.solver().get_sort(branch_term);
    if branch_sort != *result_sort {
        debug!(
            "  skipping guarded result branch equality: result sort {:?}, branch sort {:?}",
            result_sort, branch_sort
        );
        return Ok(());
    }

    let branch_eq = encoder.eq_or_iff(result_var, branch_term, result_sort);
    let guarded = encoder.solver.implies(branch_guard.clone(), branch_eq);
    encoder.assert_term(guarded);
    let result_annotation =
        ay_sort_to_expr_sort(result_sort).or_else(|| tuple_expr_sort_from_sort(result_sort));
    let result_expr = PureExpr::Var("result".to_string(), result_annotation);
    assert_guarded_tuple_target_branch_fields(
        encoder,
        &result_expr,
        branch_guard,
        branch_value_expr,
    )?;
    Ok(())
}

fn assert_guarded_ite_target_expr_field_equalities(
    encoder: &mut AYEncoder,
    target_expr: &PureExpr,
    result_expr: &PureExpr,
) -> Result<(), EncodingError> {
    assert_guarded_ite_target_expr_field_equalities_under_guard(
        encoder,
        target_expr,
        None,
        result_expr,
    )
}

fn assert_guarded_ite_target_expr_field_equalities_under_guard(
    encoder: &mut AYEncoder,
    target_expr: &PureExpr,
    active_guard: Option<Term>,
    result_expr: &PureExpr,
) -> Result<(), EncodingError> {
    match result_expr {
        PureExpr::Ite(cond, then_expr, else_expr) => {
            // Same branch-scoped side-obligation rule as
            // `assert_guarded_ite_result_equalities_under_guard`.
            let cond_term =
                encode_pure_under_optional_path_condition(encoder, active_guard.clone(), cond)?;
            let cond_bool = encoder.coerce_bool_operand(cond_term);
            let not_cond = encoder.solver.not(cond_bool.clone());
            let then_guard = combine_optional_guard(encoder, active_guard.clone(), cond_bool);
            let else_guard = combine_optional_guard(encoder, active_guard, not_cond);

            assert_guarded_tuple_target_branch_fields(
                encoder,
                target_expr,
                then_guard.clone(),
                strip_let_assume(then_expr),
            )?;
            assert_guarded_tuple_target_branch_fields(
                encoder,
                target_expr,
                else_guard.clone(),
                strip_let_assume(else_expr),
            )?;

            assert_guarded_ite_target_expr_field_equalities_under_guard(
                encoder,
                target_expr,
                Some(then_guard),
                then_expr,
            )?;
            assert_guarded_ite_target_expr_field_equalities_under_guard(
                encoder,
                target_expr,
                Some(else_guard),
                else_expr,
            )
        }
        PureExpr::LetAssume { body, .. } => {
            assert_guarded_ite_target_expr_field_equalities_under_guard(
                encoder,
                target_expr,
                active_guard,
                body,
            )
        }
        _ => Ok(()),
    }
}

fn assert_guarded_tuple_target_branch_fields(
    encoder: &mut AYEncoder,
    target_expr: &PureExpr,
    branch_guard: Term,
    branch_expr: &PureExpr,
) -> Result<(), EncodingError> {
    let PureExpr::LogicFnCall { name, args } = branch_expr else {
        return Ok(());
    };
    let Some(arity) = tuple_logic_fn_arity(name) else {
        return Ok(());
    };
    if arity != args.len() {
        return Ok(());
    }

    for (index, arg) in args.iter().enumerate() {
        let target_field = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(index),
            args: vec![target_expr.clone()],
        };
        let equality = PureExpr::BinOp(Arc::new(target_field), BinOp::Eq, Arc::new(arg.clone()));
        // Branch-scoped encode: tuple field values are branch bodies, so
        // their side obligations carry the branch guard (ledger
        // int-shift-full).
        let eq = encoder.with_path_condition(branch_guard.clone(), |encoder| {
            encoder.encode_formula(&equality)
        })?;
        let eq = encoder.coerce_bool_operand(eq);
        let guarded = encoder.solver.implies(branch_guard.clone(), eq);
        encoder.assert_term(guarded);
    }

    Ok(())
}

fn tuple_expr_sort_from_sort(sort: &Sort) -> Option<ExprSort> {
    let Sort::Uninterpreted(name) = sort else {
        return None;
    };
    let suffix = name.strip_prefix("Tuple")?;
    let arity = suffix.parse::<u8>().ok()?;
    Some(ExprSort::Tuple(arity))
}

fn assert_nullary_discriminant_result_implications_from_requires(
    encoder: &mut AYEncoder,
    result_var: Term,
    dt: &DatatypeSort,
    cond: &PureExpr,
    then_expr: &PureExpr,
    else_expr: &PureExpr,
    requires: &[PureExpr],
) -> Result<(), EncodingError> {
    let Some((receiver, discriminant_value)) = discriminant_equality_receiver_and_value(cond)
    else {
        return Ok(());
    };
    let Some((ctor_name, selected_branch)) =
        selected_nullary_constructor_branch(dt, discriminant_value, then_expr, else_expr)
    else {
        return Ok(());
    };

    let Some(ctor_term) =
        encoder.axiom_datatype_constructor("result nullary discriminant", dt, ctor_name, &[])
    else {
        return Ok(());
    };
    let result_eq_ctor = encoder.eq_or_iff(result_var, ctor_term, &Sort::Datatype(dt.clone()));

    for require in requires {
        let Some(antecedent) =
            implication_antecedent_for_constructor_receiver(require, receiver, selected_branch)
        else {
            continue;
        };
        let antecedent_term = encoder.encode_pure(antecedent)?;
        let antecedent_bool = encoder.coerce_bool_operand(antecedent_term);
        let implication = encoder.solver.implies(antecedent_bool, result_eq_ctor);
        encoder.assert_term(implication);
    }

    Ok(())
}

fn selected_nullary_constructor_branch<'a>(
    dt: &DatatypeSort,
    discriminant_value: i64,
    then_expr: &'a PureExpr,
    else_expr: &'a PureExpr,
) -> Option<(&'a str, &'a PureExpr)> {
    if let Some(then_ctor) = nullary_constructor_expr_name(then_expr) {
        let then_index = datatype_constructor_index(dt, then_ctor)?;
        if then_index == discriminant_value {
            return Some((then_ctor, then_expr));
        }
    }

    if let Some(else_ctor) = nullary_constructor_expr_name(else_expr) {
        let else_index = datatype_constructor_index(dt, else_ctor)?;
        if else_index != discriminant_value {
            return Some((else_ctor, else_expr));
        }
    }

    None
}

fn datatype_constructor_index(dt: &DatatypeSort, ctor_name: &str) -> Option<i64> {
    dt.constructors
        .iter()
        .position(|ctor| datatype_constructor_matches(dt, &ctor.name, ctor_name))
        .and_then(|idx| i64::try_from(idx).ok())
}

fn nullary_constructor_expr_name(expr: &PureExpr) -> Option<&str> {
    match strip_let_assume(expr) {
        PureExpr::LogicFnCall { name, args } if args.is_empty() => {
            let short = short_constructor_name(name);
            zero_arg_constructor_name(short).map(|_| short)
        }
        PureExpr::Var(name, _) => {
            zero_arg_constructor_name(name).map(|_| short_constructor_name(name))
        }
        _ => None,
    }
}

fn implication_antecedent_for_constructor_receiver<'a>(
    require: &'a PureExpr,
    receiver: &PureExpr,
    constructor_expr: &PureExpr,
) -> Option<&'a PureExpr> {
    let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = require else {
        return None;
    };
    receiver_constructor_equality(consequent, receiver, constructor_expr)
        .then_some(antecedent.as_ref())
}

fn receiver_constructor_equality(
    expr: &PureExpr,
    receiver: &PureExpr,
    constructor_expr: &PureExpr,
) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return false;
    };
    (same_expr_ignoring_var_sort(left, receiver) && constructor_expr_equiv(right, constructor_expr))
        || (same_expr_ignoring_var_sort(right, receiver)
            && constructor_expr_equiv(left, constructor_expr))
}

fn constructor_expr_equiv(left: &PureExpr, right: &PureExpr) -> bool {
    normalize_option_constructor_expr(left) == normalize_option_constructor_expr(right)
}

/// True for the sorts trust-wp uses to model a `Seq` field: the native
/// `Sort::Seq(_)` and the forced-uninterpreted `Uninterpreted("Seq")` carrier
/// used when a datatype mixes Seq and native fields (see
/// `force_uninterpreted_seq_sort_for_mixed_datatype`). A constructor field with
/// one of these sorts is a candidate for the `__vec_to_seq` bridge when its
/// argument arrives with a collection-iterator carrier sort. (#2170)
fn is_seq_field_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Seq(_)) || matches!(sort, Sort::Uninterpreted(name) if name == "Seq")
}

fn try_encode_result_constructor_term(
    encoder: &mut AYEncoder,
    dt: &DatatypeSort,
    result_expr: &PureExpr,
) -> Result<Option<Term>, EncodingError> {
    encoder.ensure_datatype_declared(dt);

    let tuple_ctor_for_arity = |arity: usize| -> Option<&DatatypeConstructor> {
        let mut matches = dt
            .constructors
            .iter()
            .filter(|ctor| ctor.fields.len() == arity);
        let ctor = matches.next()?;
        matches.next().is_none().then_some(ctor)
    };

    let tuple_arity_from_sort = |sort: &Sort| -> Option<usize> {
        let Sort::Uninterpreted(name) = sort else {
            return None;
        };
        let suffix = name.strip_prefix("Tuple")?;
        let arity = suffix.parse::<usize>().ok()?;
        (arity >= 1).then_some(arity)
    };

    let (ctor, ctor_args): (&DatatypeConstructor, Vec<PureExpr>) = match result_expr {
        PureExpr::LogicFnCall { name, args } => {
            let short = short_constructor_name(name);
            if let Some(ctor) = dt.constructors.iter().find(|ctor| {
                datatype_constructor_matches(dt, &ctor.name, short)
                    && ctor.fields.len() == args.len()
            }) {
                (ctor, args.clone())
            } else if let Some(arity) = tuple_logic_fn_arity(name) {
                let Some(ctor) = tuple_ctor_for_arity(arity) else {
                    return Ok(None);
                };
                (ctor, args.clone())
            } else {
                return Ok(None);
            }
        }
        PureExpr::Var(name, _) => {
            let short = short_constructor_name(name);
            if let Some(ctor) = dt.constructors.iter().find(|ctor| {
                datatype_constructor_matches(dt, &ctor.name, short) && ctor.fields.is_empty()
            }) {
                (ctor, Vec::new())
            } else {
                let Some(arity) =
                    tuple_arity_from_sort(&encoder.infer_expr_sort_with_context(result_expr, None))
                else {
                    return Ok(None);
                };
                let Some(ctor) = tuple_ctor_for_arity(arity) else {
                    return Ok(None);
                };
                let args = (0..arity)
                    .map(|index| PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(index),
                        args: vec![result_expr.clone()],
                    })
                    .collect();
                (ctor, args)
            }
        }
        _ => return Ok(None),
    };

    let mut arg_terms = Vec::with_capacity(ctor_args.len());
    for (arg, field) in ctor_args.iter().zip(&ctor.fields) {
        preseed_constructor_arg_sort(encoder, arg, &field.sort)?;
        let term = encoder.encode_pure(arg)?;
        let actual_sort = encoder.infer_expr_sort_with_context(arg, None);
        let coerced = match (&actual_sort, &field.sort) {
            (Sort::Bool, Sort::Int) => {
                let one = encoder.solver_mut().int_const(1);
                let zero = encoder.solver_mut().int_const(0);
                encoder.solver_mut().ite(term, one, zero)
            }
            _ => {
                // A field whose declared sort is Seq but whose argument term
                // arrived with a Vec-like / collection-iterator carrier sort
                // (e.g. `field: View(map_inv(..))` encoded as `MapInv`) must be
                // bridged to Seq via the canonical `__vec_to_seq_<Sort>` UF
                // rather than left to the fresh-constant fallback below, which
                // severs the link between the constructor field and the
                // produced collection. `coerce_to_seq` reuses the SAME bridge
                // UF that the iterator/collect view facts already reference, so
                // the field term becomes congruent to those facts. (#2170)
                //
                // SOUND: `__vec_to_seq_<Sort>(x)` is, by the bridge's
                // definition, the faithful Seq view of `x`; equating the
                // constructor field to it only restates `field == x@`, which is
                // exactly the source-level binding (`field: <collection>`).
                // `coerce_to_seq` returns the term unchanged for non-coercible
                // sorts, and we only adopt the result when its sort actually
                // matches the field's declared sort — so a failed coercion
                // falls through to the existing fallback unchanged.
                let term_sort = encoder.solver_mut().get_sort(term);
                if term_sort != field.sort && is_seq_field_sort(&field.sort) {
                    let bridged = encoder.coerce_to_seq(term);
                    if encoder.solver_mut().get_sort(bridged) == field.sort {
                        bridged
                    } else {
                        term
                    }
                } else {
                    term
                }
            }
        };
        arg_terms.push(coerced);
    }

    match encoder.safe_datatype_constructor("result constructor term", dt, &ctor.name, &arg_terms) {
        Ok(term) => {
            encoder.materialize_ground_native_constructor(dt, &ctor.name, term, &arg_terms);
            Ok(Some(term))
        }
        Err(err) => {
            // Sort mismatch in constructor application. Try bridging
            // non-Int argument terms to Int via fresh constants, since
            // OptionInt/ResultIntInt constructors use Int fields. (#2699)
            let mut bridged_args = arg_terms.clone();
            let mut any_bridged = false;
            for (i, (arg_term, field)) in bridged_args.iter_mut().zip(&ctor.fields).enumerate() {
                let term_sort = encoder.solver_mut().get_sort(*arg_term);
                if term_sort != field.sort {
                    unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
                    let id = RESULT_DT_BRIDGE_COUNTER.fetch_add(1, Ordering::Relaxed);
                    *arg_term = encoder.solver_mut().declare_const(
                        &format!("__ctor_field_bridge_{id}_{i}"),
                        field.sort.clone(),
                    );
                    any_bridged = true;
                }
            }
            if any_bridged {
                let term = encoder
                    .safe_datatype_constructor(
                        "result constructor term bridged",
                        dt,
                        &ctor.name,
                        &bridged_args,
                    )
                    .map_err(|bridge_err| {
                        EncodingError::solver_error(format!(
                        "result datatype wrap failed for constructor {} (bridged): {bridge_err}",
                        ctor.name
                    ))
                    })?;
                encoder.materialize_ground_native_constructor(dt, &ctor.name, term, &bridged_args);
                Ok(Some(term))
            } else {
                Err(EncodingError::solver_error(format!(
                    "result datatype wrap failed for constructor {}: {err}",
                    ctor.name
                )))
            }
        }
    }
}

fn preseed_constructor_arg_sort(
    encoder: &mut AYEncoder,
    arg: &PureExpr,
    field_sort: &Sort,
) -> Result<(), EncodingError> {
    if let PureExpr::Var(name, _) = arg {
        let _ = encoder.get_or_declare_var(name, field_sort.clone())?;
    }
    Ok(())
}
