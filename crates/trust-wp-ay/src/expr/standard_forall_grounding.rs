// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Grounding for standard-library Mapping/FMap universal assumptions.

use std::collections::{HashMap, HashSet};

use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::expr_mentions_var;

const TRUST_WP_STANDARD_PRECONDITION_FORALL_INSTANCE_LIMIT: usize = 80;

/// Ground Mapping/FMap standard-spec precondition foralls against keys observed
/// in the same expression set.
pub(crate) fn instantiate_standard_precondition_foralls(exprs: &[PureExpr]) -> Vec<PureExpr> {
    let expr_refs: Vec<&PureExpr> = exprs.iter().collect();
    instantiate_standard_precondition_foralls_from(&expr_refs, &expr_refs)
}

/// Ground Mapping/FMap standard-spec precondition foralls from `source_exprs`
/// using observed keys from `context_exprs`.
pub(crate) fn instantiate_standard_precondition_foralls_from(
    source_exprs: &[&PureExpr],
    context_exprs: &[&PureExpr],
) -> Vec<PureExpr> {
    let context_candidates = collect_observed_grounding_terms(context_exprs);
    let known_int_values = collect_known_int_values(context_exprs);

    let mut instances = Vec::new();
    let mut seen = HashSet::new();
    for expr in source_exprs {
        let PureExpr::Forall {
            var,
            var_sort,
            body,
            ..
        } = expr
        else {
            continue;
        };
        if !is_standard_data_structure_precondition_forall(expr) {
            continue;
        }
        if is_negative_contains_forall_body(body, var) {
            continue;
        }
        let mut candidate_terms = context_candidates.clone();
        collect_bound_equality_witnesses(body, var, &mut candidate_terms, &mut HashSet::new());
        for key in &candidate_terms {
            if expr_mentions_var(key, var) {
                continue;
            }
            if !candidate_matches_var_sort(key, var_sort.as_ref()) {
                continue;
            }
            if candidate_makes_forall_antecedent_false(body, var, key, &known_int_values) {
                continue;
            }
            let mut subst = HashMap::new();
            subst.insert(var.clone(), key.clone());
            let instance = body.substitute(&subst);
            if seen.insert(instance.clone()) {
                instances.push(instance);
                if instances.len() >= TRUST_WP_STANDARD_PRECONDITION_FORALL_INSTANCE_LIMIT {
                    return instances;
                }
            }
        }
    }

    instances
}

fn collect_known_int_values(exprs: &[&PureExpr]) -> HashMap<PureExpr, i64> {
    let mut values = HashMap::new();
    for expr in exprs {
        collect_known_int_values_from_expr(expr, &mut values);
    }
    values
}

fn collect_known_int_values_from_expr(expr: &PureExpr, values: &mut HashMap<PureExpr, i64>) {
    match expr {
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            if let Some(value) = int_literal(right) {
                values.insert(left.as_ref().clone(), value);
            }
            if let Some(value) = int_literal(left) {
                values.insert(right.as_ref().clone(), value);
            }
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_known_int_values_from_expr(left, values);
            collect_known_int_values_from_expr(right, values);
        }
        _ => {}
    }
}

fn candidate_makes_forall_antecedent_false(
    body: &PureExpr,
    var: &str,
    candidate: &PureExpr,
    known_int_values: &HashMap<PureExpr, i64>,
) -> bool {
    let Some(candidate_value) = known_int_value(candidate, known_int_values) else {
        return false;
    };
    let PureExpr::BinOp(antecedent, BinOp::Implies, _) = body else {
        return false;
    };
    antecedent_false_for_candidate(antecedent, var, candidate_value, known_int_values)
}

fn antecedent_false_for_candidate(
    expr: &PureExpr,
    var: &str,
    candidate_value: i64,
    known_int_values: &HashMap<PureExpr, i64>,
) -> bool {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            antecedent_false_for_candidate(left, var, candidate_value, known_int_values)
                || antecedent_false_for_candidate(right, var, candidate_value, known_int_values)
        }
        PureExpr::BinOp(left, BinOp::Le, right) => {
            if is_bound_var_ref(left, var) {
                known_int_value(right, known_int_values)
                    .is_some_and(|bound| candidate_value > bound)
            } else if is_bound_var_ref(right, var) {
                known_int_value(left, known_int_values).is_some_and(|bound| bound > candidate_value)
            } else {
                false
            }
        }
        PureExpr::BinOp(left, BinOp::Lt, right) => {
            if is_bound_var_ref(left, var) {
                known_int_value(right, known_int_values)
                    .is_some_and(|bound| candidate_value >= bound)
            } else if is_bound_var_ref(right, var) {
                known_int_value(left, known_int_values)
                    .is_some_and(|bound| bound >= candidate_value)
            } else {
                false
            }
        }
        PureExpr::BinOp(left, BinOp::Ge, right) => antecedent_false_for_candidate(
            &PureExpr::BinOp(right.clone(), BinOp::Le, left.clone()),
            var,
            candidate_value,
            known_int_values,
        ),
        PureExpr::BinOp(left, BinOp::Gt, right) => antecedent_false_for_candidate(
            &PureExpr::BinOp(right.clone(), BinOp::Lt, left.clone()),
            var,
            candidate_value,
            known_int_values,
        ),
        _ => false,
    }
}

fn known_int_value(expr: &PureExpr, known_int_values: &HashMap<PureExpr, i64>) -> Option<i64> {
    int_literal(expr).or_else(|| known_int_values.get(expr).copied())
}

fn int_literal(expr: &PureExpr) -> Option<i64> {
    match expr {
        PureExpr::Int(value) => Some(*value),
        PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner) => int_literal(inner),
        _ => None,
    }
}

/// Whether a standard-library precondition forall is EXEMPT from grounding.
///
/// `instantiate_standard_precondition_foralls_from` skips negative-contains
/// bodies (e.g. FSet EMPTY's `forall<k> !result.contains(k)`) — grounding at
/// observed keys cannot represent the universal emptiness claim. Callers that
/// drop standard foralls after grounding must NOT drop these: they produced
/// no instances, so dropping them erases the premise entirely (neither
/// grounded nor asserted). That ground-then-drop mismatch fabricates a
/// counterexample to a goal the ghost_set `forall<k> !set.contains(k)`
/// premise discharges; pinned by
/// `grounding_exempt_negative_contains_forall_is_asserted_not_dropped`.
pub(crate) fn is_grounding_exempt_standard_forall(expr: &PureExpr) -> bool {
    let PureExpr::Forall { var, body, .. } = expr else {
        return false;
    };
    is_standard_data_structure_precondition_forall(expr)
        && is_negative_contains_forall_body(body, var)
}

/// Returns true for the Mapping/FMap standard-spec foralls that ay-dpll cannot
/// handle in the base context but that can be soundly replaced by instances.
pub(crate) fn is_standard_data_structure_precondition_forall(expr: &PureExpr) -> bool {
    let PureExpr::Forall { var, body, .. } = expr else {
        return false;
    };
    contains_bound_data_structure_access(body, var)
        || (contains_bound_receiver_precondition(body, var)
            && has_bound_equality_witness(body, var))
}

fn contains_bound_data_structure_access(expr: &PureExpr, var: &str) -> bool {
    match expr {
        PureExpr::MethodCall { method, args, .. } => data_structure_method_key_arg(method, args)
            .is_some_and(|arg| is_bound_var_ref(arg, var)),
        PureExpr::LogicFnCall { name, args } => {
            data_structure_logic_key_arg(name, args).is_some_and(|arg| is_var_named(arg, var))
        }
        PureExpr::BinOp(left, _, right) => {
            contains_bound_data_structure_access(left, var)
                || contains_bound_data_structure_access(right, var)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => contains_bound_data_structure_access(inner, var),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_bound_data_structure_access(cond, var)
                || contains_bound_data_structure_access(then_expr, var)
                || contains_bound_data_structure_access(else_expr, var)
        }
        PureExpr::Match { scrutinee, arms } => {
            contains_bound_data_structure_access(scrutinee, var)
                || arms
                    .iter()
                    .any(|arm| contains_bound_data_structure_access(&arm.body, var))
        }
        PureExpr::Let { value, body, .. } => {
            contains_bound_data_structure_access(value, var)
                || contains_bound_data_structure_access(body, var)
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_bound_data_structure_access(assumption, var)
                || contains_bound_data_structure_access(body, var)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_bound_data_structure_access(obligation, var)
                || contains_bound_data_structure_access(body, var)
        }
        PureExpr::Closure { body, .. } => contains_bound_data_structure_access(body, var),
        PureExpr::Forall { .. } | PureExpr::Exists { .. } => false,
        _ => false,
    }
}

fn contains_bound_receiver_precondition(expr: &PureExpr, var: &str) -> bool {
    match expr {
        PureExpr::MethodCall { method, args, .. } => {
            method == "precondition" && args.first().is_some_and(|arg| is_bound_var_ref(arg, var))
        }
        PureExpr::BinOp(left, _, right) => {
            contains_bound_receiver_precondition(left, var)
                || contains_bound_receiver_precondition(right, var)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => contains_bound_receiver_precondition(inner, var),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_bound_receiver_precondition(cond, var)
                || contains_bound_receiver_precondition(then_expr, var)
                || contains_bound_receiver_precondition(else_expr, var)
        }
        PureExpr::Match { scrutinee, arms } => {
            contains_bound_receiver_precondition(scrutinee, var)
                || arms
                    .iter()
                    .any(|arm| contains_bound_receiver_precondition(&arm.body, var))
        }
        PureExpr::Let { value, body, .. } => {
            contains_bound_receiver_precondition(value, var)
                || contains_bound_receiver_precondition(body, var)
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_bound_receiver_precondition(assumption, var)
                || contains_bound_receiver_precondition(body, var)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_bound_receiver_precondition(obligation, var)
                || contains_bound_receiver_precondition(body, var)
        }
        PureExpr::Closure { body, .. } => contains_bound_receiver_precondition(body, var),
        PureExpr::Forall { .. } | PureExpr::Exists { .. } => false,
        _ => false,
    }
}

fn collect_observed_grounding_terms(exprs: &[&PureExpr]) -> Vec<PureExpr> {
    let mut terms = Vec::new();
    let mut seen = HashSet::new();
    for expr in exprs {
        collect_observed_grounding_terms_from_expr(expr, &mut terms, &mut seen);
        if terms.len() >= TRUST_WP_STANDARD_PRECONDITION_FORALL_INSTANCE_LIMIT {
            break;
        }
    }
    terms
}

fn collect_observed_grounding_terms_from_expr(
    expr: &PureExpr,
    terms: &mut Vec<PureExpr>,
    seen: &mut HashSet<PureExpr>,
) {
    if terms.len() >= TRUST_WP_STANDARD_PRECONDITION_FORALL_INSTANCE_LIMIT {
        return;
    }

    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if let Some(key) = data_structure_method_key_arg(method, args) {
                push_grounding_term(key, terms, seen);
            }
            if method == "precondition" {
                if let Some(receiver_arg) = args.first() {
                    push_grounding_term(receiver_arg, terms, seen);
                }
            }
            collect_observed_grounding_terms_from_expr(receiver, terms, seen);
            for arg in args {
                collect_observed_grounding_terms_from_expr(arg, terms, seen);
            }
        }
        PureExpr::LogicFnCall { name, args } => {
            if let Some(key) = data_structure_logic_key_arg(name, args) {
                push_grounding_term(key, terms, seen);
            }
            for arg in args {
                collect_observed_grounding_terms_from_expr(arg, terms, seen);
            }
        }
        PureExpr::BinOp(left, _, right) => {
            collect_observed_grounding_terms_from_expr(left, terms, seen);
            collect_observed_grounding_terms_from_expr(right, terms, seen);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => collect_observed_grounding_terms_from_expr(inner, terms, seen),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_observed_grounding_terms_from_expr(cond, terms, seen);
            collect_observed_grounding_terms_from_expr(then_expr, terms, seen);
            collect_observed_grounding_terms_from_expr(else_expr, terms, seen);
        }
        PureExpr::Forall { .. }
        | PureExpr::Exists { .. }
        | PureExpr::Match { .. }
        | PureExpr::Let { .. }
        | PureExpr::LetAssume { .. }
        | PureExpr::LetObligation { .. }
        | PureExpr::Closure { .. } => {}
        _ => {}
    }
}

fn collect_bound_equality_witnesses(
    expr: &PureExpr,
    var: &str,
    terms: &mut Vec<PureExpr>,
    seen: &mut HashSet<PureExpr>,
) {
    if terms.len() >= TRUST_WP_STANDARD_PRECONDITION_FORALL_INSTANCE_LIMIT {
        return;
    }

    match expr {
        PureExpr::BinOp(left, trust_wp_core::formula::BinOp::Eq, right) => {
            if is_bound_var_ref(left, var) {
                push_grounding_term_with_receiver_variant(right, terms, seen);
            }
            if is_bound_var_ref(right, var) {
                push_grounding_term_with_receiver_variant(left, terms, seen);
            }
            collect_bound_equality_witnesses(left, var, terms, seen);
            collect_bound_equality_witnesses(right, var, terms, seen);
        }
        PureExpr::BinOp(left, _, right) => {
            collect_bound_equality_witnesses(left, var, terms, seen);
            collect_bound_equality_witnesses(right, var, terms, seen);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => collect_bound_equality_witnesses(inner, var, terms, seen),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_bound_equality_witnesses(cond, var, terms, seen);
            collect_bound_equality_witnesses(then_expr, var, terms, seen);
            collect_bound_equality_witnesses(else_expr, var, terms, seen);
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_bound_equality_witnesses(scrutinee, var, terms, seen);
            for arm in arms {
                collect_bound_equality_witnesses(&arm.body, var, terms, seen);
            }
        }
        PureExpr::Let { value, body, .. } => {
            collect_bound_equality_witnesses(value, var, terms, seen);
            collect_bound_equality_witnesses(body, var, terms, seen);
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_bound_equality_witnesses(assumption, var, terms, seen);
            collect_bound_equality_witnesses(body, var, terms, seen);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_bound_equality_witnesses(obligation, var, terms, seen);
            collect_bound_equality_witnesses(body, var, terms, seen);
        }
        PureExpr::Closure { body, .. } => collect_bound_equality_witnesses(body, var, terms, seen),
        PureExpr::Forall { .. } | PureExpr::Exists { .. } => {}
        _ => {}
    }
}

fn has_bound_equality_witness(expr: &PureExpr, var: &str) -> bool {
    match expr {
        PureExpr::BinOp(left, trust_wp_core::formula::BinOp::Eq, right) => {
            is_bound_var_ref(left, var)
                || is_bound_var_ref(right, var)
                || has_bound_equality_witness(left, var)
                || has_bound_equality_witness(right, var)
        }
        PureExpr::BinOp(left, _, right) => {
            has_bound_equality_witness(left, var) || has_bound_equality_witness(right, var)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => has_bound_equality_witness(inner, var),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            has_bound_equality_witness(cond, var)
                || has_bound_equality_witness(then_expr, var)
                || has_bound_equality_witness(else_expr, var)
        }
        PureExpr::Match { scrutinee, arms } => {
            has_bound_equality_witness(scrutinee, var)
                || arms
                    .iter()
                    .any(|arm| has_bound_equality_witness(&arm.body, var))
        }
        PureExpr::Let { value, body, .. } => {
            has_bound_equality_witness(value, var) || has_bound_equality_witness(body, var)
        }
        PureExpr::LetAssume { assumption, body } => {
            has_bound_equality_witness(assumption, var) || has_bound_equality_witness(body, var)
        }
        PureExpr::LetObligation { obligation, body } => {
            has_bound_equality_witness(obligation, var) || has_bound_equality_witness(body, var)
        }
        PureExpr::Closure { body, .. } => has_bound_equality_witness(body, var),
        PureExpr::Forall { .. } | PureExpr::Exists { .. } => false,
        _ => false,
    }
}

fn push_grounding_term_with_receiver_variant(
    term: &PureExpr,
    terms: &mut Vec<PureExpr>,
    seen: &mut HashSet<PureExpr>,
) {
    push_grounding_term(term, terms, seen);
    if let PureExpr::Deref(inner) = term {
        push_grounding_term(inner, terms, seen);
    }
}

fn push_grounding_term(term: &PureExpr, terms: &mut Vec<PureExpr>, seen: &mut HashSet<PureExpr>) {
    if is_ground_instantiation_key(term) && seen.insert(term.clone()) {
        terms.push(term.clone());
    }
}

fn data_structure_method_key_arg<'a>(method: &str, args: &'a [PureExpr]) -> Option<&'a PureExpr> {
    matches!(method, "get" | "contains" | "lookup" | "index_logic")
        .then(|| args.first())
        .flatten()
}

fn data_structure_logic_key_arg<'a>(name: &str, args: &'a [PureExpr]) -> Option<&'a PureExpr> {
    matches!(
        name,
        "get" | "contains" | "lookup" | "mapping_get" | "fmap_contains" | "fmap_lookup"
    )
    .then(|| args.get(1))
    .flatten()
}

fn is_ground_instantiation_key(expr: &PureExpr) -> bool {
    !matches!(expr, PureExpr::Bool(_) | PureExpr::Float(_))
}

fn is_negative_contains_forall_body(expr: &PureExpr, var: &str) -> bool {
    let PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, inner) = expr else {
        return false;
    };
    match inner.as_ref() {
        PureExpr::MethodCall { method, args, .. } => {
            matches!(method.as_str(), "contains")
                && args.first().is_some_and(|arg| is_var_named(arg, var))
        }
        PureExpr::LogicFnCall { name, args } => {
            matches!(name.as_str(), "contains" | "fmap_contains")
                && args.get(1).is_some_and(|arg| is_var_named(arg, var))
        }
        _ => false,
    }
}

fn is_var_named(expr: &PureExpr, expected: &str) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == expected)
}

fn is_bound_var_ref(expr: &PureExpr, expected: &str) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == expected,
        PureExpr::Deref(inner) | PureExpr::Final(inner) => is_bound_var_ref(inner, expected),
        _ => false,
    }
}

fn candidate_matches_var_sort(candidate: &PureExpr, var_sort: Option<&ExprSort>) -> bool {
    let Some(var_sort) = var_sort else {
        return true;
    };

    match var_sort {
        ExprSort::Int => candidate_can_be_int(candidate),
        ExprSort::Bool => matches!(
            candidate,
            PureExpr::Bool(_) | PureExpr::Var(_, Some(ExprSort::Bool))
        ),
        ExprSort::Ref(expected) => matches!(
            candidate,
            PureExpr::Var(_, Some(ExprSort::Ref(actual))) if actual.as_ref() == expected.as_ref()
        ),
        ExprSort::MutRef(expected) => matches!(
            candidate,
            PureExpr::Var(_, Some(ExprSort::MutRef(actual))) if actual.as_ref() == expected.as_ref()
        ),
        expected => matches!(candidate, PureExpr::Var(_, Some(actual)) if actual == expected),
    }
}

fn candidate_can_be_int(candidate: &PureExpr) -> bool {
    match candidate {
        PureExpr::Int(_) => true,
        PureExpr::Var(_, None | Some(ExprSort::Int)) => true,
        PureExpr::MethodCall { method, .. } if method == "len" => true,
        PureExpr::BinOp(
            left,
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::DivTrunc
            | BinOp::RemTrunc,
            right,
        ) => candidate_can_be_int(left) && candidate_can_be_int(right),
        PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner) => candidate_can_be_int(inner),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

    use super::{
        instantiate_standard_precondition_foralls, is_standard_data_structure_precondition_forall,
    };

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn int_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::Int))
    }

    fn int(value: i64) -> PureExpr {
        PureExpr::Int(value)
    }

    fn deref(expr: PureExpr) -> PureExpr {
        PureExpr::Deref(Arc::new(expr))
    }

    fn method(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: method.to_string(),
            args,
        }
    }

    fn eq(left: PureExpr, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), BinOp::Eq, Arc::new(right))
    }

    fn le(left: PureExpr, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), BinOp::Le, Arc::new(right))
    }

    fn lt(left: PureExpr, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), BinOp::Lt, Arc::new(right))
    }

    fn and(left: PureExpr, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), BinOp::And, Arc::new(right))
    }

    fn implies(left: PureExpr, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), BinOp::Implies, Arc::new(right))
    }

    #[test]
    fn index_logic_forall_grounds_from_observed_index_terms() {
        let i = int_var("i");
        let pred = var("pred");
        let pred_len = method(pred.clone(), "len", vec![]);
        let result_elem = method(var("result"), "index_logic", vec![i.clone()]);
        let pred_elem = method(pred, "index_logic", vec![i.clone()]);
        let bridge = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(implies(
                and(le(int(0), i.clone()), lt(i, pred_len)),
                eq(result_elem, pred_elem),
            )),
            triggers: Vec::new(),
        };
        let observed_zero = method(var("result"), "index_logic", vec![int(0)]);
        let observed_one = method(var("result"), "index_logic", vec![int(1)]);

        assert!(is_standard_data_structure_precondition_forall(&bridge));

        let instances =
            instantiate_standard_precondition_foralls(&[bridge, observed_zero, observed_one]);
        let rendered = format!("{instances:?}");
        assert!(
            rendered.contains("Int(0)") && rendered.contains("Int(1)"),
            "expected index_logic forall instances for observed 0 and 1, got {instances:?}"
        );
    }

    #[test]
    fn index_logic_forall_skips_statically_out_of_bounds_instance() {
        let i = int_var("i");
        let pred = var("pred");
        let pred_len = method(pred.clone(), "len", vec![]);
        let result_elem = method(var("result"), "index_logic", vec![i.clone()]);
        let pred_elem = method(pred.clone(), "index_logic", vec![i.clone()]);
        let bridge = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(implies(
                and(le(int(0), i.clone()), lt(i, pred_len.clone())),
                eq(result_elem, pred_elem),
            )),
            triggers: Vec::new(),
        };
        let pred_len_is_one = eq(pred_len, int(1));
        let observed_zero = method(var("result"), "index_logic", vec![int(0)]);
        let observed_one = method(var("result"), "index_logic", vec![int(1)]);

        let instances = instantiate_standard_precondition_foralls(&[
            bridge,
            pred_len_is_one,
            observed_zero,
            observed_one,
        ]);
        let rendered = format!("{instances:?}");
        assert!(
            rendered.contains("Int(0)"),
            "expected in-bounds index 0 instance, got {instances:?}"
        );
        assert!(
            !rendered.contains("Int(1)"),
            "index 1 is out of bounds when pred.len() == 1 and should not be instantiated: {instances:?}"
        );
    }

    #[test]
    fn get_forall_grounds_from_observed_index_logic_lookup_key() {
        let z = int_var("z");
        let pred0_fact = PureExpr::Forall {
            var: "z".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(eq(method(var("pred0"), "get", vec![z]), var("body"))),
            triggers: Vec::new(),
        };
        let observed_lookup = method(
            method(var("slice0_view"), "index_logic", vec![int(0)]),
            "index_logic",
            vec![int_var("call_18")],
        );

        assert!(is_standard_data_structure_precondition_forall(&pred0_fact));

        let instances = instantiate_standard_precondition_foralls(&[pred0_fact, observed_lookup]);
        assert!(
            instances
                .iter()
                .any(|instance| format!("{instance:?}").contains("\"call_18\"")),
            "expected closure-map get forall to ground at observed lookup key, got {instances:?}"
        );
    }

    #[test]
    fn receiver_precondition_forall_grounds_from_bound_equality_witness() {
        let precondition = method(var("T_deref_mut"), "precondition", vec![var("y")]);
        let body = implies(
            and(
                method(var("inv"), "call", vec![var("y")]),
                eq(deref(var("y")), deref(var("x"))),
            ),
            precondition,
        );
        let forall = PureExpr::Forall {
            var: "y".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: Vec::new(),
        };

        assert!(is_standard_data_structure_precondition_forall(&forall));

        let instances = instantiate_standard_precondition_foralls(&[forall]);
        assert!(
            instances
                .iter()
                .any(|instance| format!("{instance:?}").contains("precondition")
                    && format!("{instance:?}").contains("\"x\"")),
            "expected a grounded precondition instance using x witness, got {instances:?}"
        );
    }
}
