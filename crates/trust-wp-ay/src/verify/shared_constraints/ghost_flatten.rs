// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost implication flattening and constant propagation.
//!
//! Originally part of `shared_constraints.rs`. Extracted as part of #1988.

use std::{collections::HashSet, sync::Arc};

use tracing::debug;
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

use crate::{encoder::MAX_ENCODING_DEPTH, error::EncodingError};

/// Flatten implications and propagate ground constants in ghost context
/// to work around ay-dpll's inability to combine UF equality with
/// arithmetic inside implications.
///
/// ay-dpll returns "incomplete" for patterns like `b ==> f(x) == f(a) + 1`
/// even when `b` is provably true from other assertions, and also for
/// transitive UF+arithmetic chains like `f(a)==0` + `f(b)==f(a)+1` ⊢ `f(b)==1`.
///
/// This function:
/// 1. Identifies Bool variables known to be true (direct assertion or equality propagation)
/// 2. Flattens implications whose antecedent is known-true
/// 3. Collects ground equalities mapping complex expressions to constants
/// 4. Substitutes known constants into remaining expressions to help the solver
///
/// All transformations are sound: they only assert logical consequences of
/// facts already in the ghost context.
pub(crate) fn flatten_ghost_implications(
    encoder: &mut crate::encoder::AYEncoder,
    ghost_exprs: &[PureExpr],
) -> Result<(), EncodingError> {
    use std::collections::{HashMap, HashSet};

    // Phase 0: ground instantiation of universally quantified ghost facts.
    //
    // Ghost data structure specs (FSet, FMap) use forall quantifiers for
    // frame axioms and emptiness properties (e.g., `forall x, !s.contains(x)`).
    // ay-dpll's quantifier instantiation cannot connect these with arithmetic
    // chains through implications, returning Unknown(Incomplete).
    //
    // Sound optimization: instantiate each `forall x, body(x)` with every
    // ground Int constant that appears in the ghost context. This produces
    // ground facts the solver can directly reason about.
    //
    // Example: given `forall x, !call_1.contains(x)` and `int(1)` in context,
    // assert `!call_1.contains(1)` directly. (#2671, #2696)
    let ground_instances = instantiate_ghost_foralls(ghost_exprs);
    for instance in &ground_instances {
        let term = encoder.encode_pure(instance)?;
        let bool_term = encoder.coerce_bool_operand(term);
        encoder.assert_term(bool_term);
    }
    if !ground_instances.is_empty() {
        debug!(
            "[flatten] Phase 0: {} ground instances from forall instantiation",
            ground_instances.len()
        );
        for inst in &ground_instances {
            debug!("[flatten]   ground instance: {inst}");
        }
    }

    // Build extended context including ground instances for downstream phases.
    let extended_ghost_exprs: Vec<PureExpr> = ghost_exprs
        .iter()
        .cloned()
        .chain(ground_instances.into_iter())
        .collect();
    let ghost_exprs = extended_ghost_exprs.as_slice();

    // Phase 1: collect Bool variable names that are directly asserted (known true).
    let mut true_vars: HashSet<&str> = HashSet::new();
    for expr in ghost_exprs {
        if let PureExpr::Var(name, _) = expr {
            true_vars.insert(name.as_str());
        }
    }

    // Phase 2: propagate through equalities.
    // If `Eq(Var(b), rhs)` and `rhs` appears as a direct assertion in
    // the ghost_context, then `b` is true.
    //
    // Use a HashSet for O(1) membership checks instead of the previous
    // O(n) linear scan per equality. (#2535)
    let ghost_expr_set: HashSet<&PureExpr> = ghost_exprs.iter().collect();
    for expr in ghost_exprs {
        if let PureExpr::BinOp(left, BinOp::Eq, right) = expr {
            if let PureExpr::Var(name, _) = left.as_ref() {
                if ghost_expr_set.contains(right.as_ref()) {
                    true_vars.insert(name.as_str());
                }
            }
            if let PureExpr::Var(name, _) = right.as_ref() {
                if ghost_expr_set.contains(left.as_ref()) {
                    true_vars.insert(name.as_str());
                }
            }
        }
    }

    debug!("[flatten] Phase 1+2: true_vars = {:?}", true_vars);

    // Phase 3: for each implication with a true Bool antecedent, assert consequent.
    // Collect the consequents for use in Phase 4.
    let mut flattened_consequents: Vec<&PureExpr> = Vec::new();
    if !true_vars.is_empty() {
        for expr in ghost_exprs {
            if let PureExpr::BinOp(left, BinOp::Implies, right) = expr {
                let antecedent_true = match left.as_ref() {
                    PureExpr::Var(name, _) => true_vars.contains(name.as_str()),
                    _ => false,
                };
                if antecedent_true {
                    let term = encoder.encode_pure(right)?;
                    let bool_term = encoder.coerce_bool_operand(term);
                    encoder.assert_term(bool_term);
                    flattened_consequents.push(right.as_ref());
                }
            }
        }
    }

    // Phase 4: ground constant propagation.
    //
    // Collect equalities of the form `complex_expr == constant` where
    // `complex_expr` is a MethodCall, LogicFnCall, or other non-trivial
    // expression and `constant` is an Int or Bool literal. Then substitute
    // these known values into other expressions.
    //
    // This helps ay-dpll handle chains like:
    //   f(a) == 0, f(b) == f(a) + 1 ⊢ f(b) == 1
    // by asserting the simplified form `f(b) == 0 + 1` directly.
    let all_exprs: Vec<&PureExpr> = ghost_exprs
        .iter()
        .chain(flattened_consequents.iter().copied())
        .collect();

    // Use a HashMap for O(1) constant lookups instead of the previous
    // O(n) linear scan per tree node. (#2535)
    let mut const_map: HashMap<&PureExpr, &PureExpr> = HashMap::new();
    for expr in &all_exprs {
        if let PureExpr::BinOp(left, BinOp::Eq, right) = expr {
            if is_ground_constant(right) && is_substitutable_expr(left) {
                const_map.entry(left.as_ref()).or_insert(right.as_ref());
            } else if is_ground_constant(left) && is_substitutable_expr(right) {
                const_map.entry(right.as_ref()).or_insert(left.as_ref());
            }
        }
    }

    debug!(
        "[flatten] Phase 4: const_map has {} entries",
        const_map.len()
    );
    for (k, v) in &const_map {
        debug!("[flatten]   {:?} => {:?}", k, v);
    }

    if !const_map.is_empty() {
        // For each expression in the ghost context that contains a
        // subexpression with a known constant, assert the simplified version.
        // This covers both equalities (lhs == rhs) and implications
        // (antecedent ==> consequent), enabling the solver to work with
        // pre-simplified arithmetic.
        for expr in &all_exprs {
            if let Some(simplified) = substitute_constants_indexed(expr, &const_map) {
                if &simplified != *expr {
                    debug!("[flatten] Phase 4: asserting simplified: {:?}", simplified);

                    let term = encoder.encode_pure(&simplified)?;
                    let bool_term = encoder.coerce_bool_operand(term);
                    encoder.assert_term(bool_term);
                }
            }
        }
    }

    Ok(())
}

/// Cross-domain ground instantiation: instantiate forall quantifiers from
/// preconditions using ground constants from the combined ghost+precondition
/// context. (#2671)
///
/// In the ghost pipeline, FSet/FMap specs produce forall quantifiers as
/// preconditions (not ghost context). The ghost context only contains alias
/// facts like `set == ^call_1`. Without this cross-domain instantiation,
/// the solver cannot connect universal emptiness axioms (in preconditions)
/// with ghost mutation chains (in ghost context).
///
/// Called after `flatten_ghost_implications` when ghost context is present.
/// Only instantiates foralls from `requires`; ghost-context foralls are
/// already handled by Phase 0 inside `flatten_ghost_implications`.
pub(crate) fn instantiate_precondition_foralls_for_ghost(
    encoder: &mut crate::encoder::AYEncoder,
    requires: &[PureExpr],
    ensures: &[PureExpr],
    ghost_exprs: &[PureExpr],
) -> Result<(), EncodingError> {
    // Collect ground constants from both domains
    let combined: Vec<PureExpr> = requires
        .iter()
        .chain(ensures.iter())
        .chain(ghost_exprs.iter())
        .cloned()
        .collect();
    let instances = instantiate_ghost_foralls_from(&combined, requires);

    if !instances.is_empty() {
        debug!(
            "[flatten] cross-domain: {} ground instances from precondition foralls",
            instances.len()
        );
        for inst in &instances {
            debug!("[flatten]   precondition ground instance: {inst}");
        }
    }

    for instance in &instances {
        let term = encoder.encode_pure(instance)?;
        let bool_term = encoder.coerce_bool_operand(term);
        encoder.assert_term(bool_term);
    }

    Ok(())
}

/// Flatten concrete precondition implications whose guards are already known
/// from the combined precondition + ghost context.
///
/// This is intentionally syntactic and local: it only fires for asserted
/// ground facts and for facts derived by boolean equality from asserted facts.
/// Each asserted consequent is therefore a direct logical consequence of an
/// existing `A ==> B` fact plus an already-known-true `A`.
pub(crate) fn assert_known_ghost_precondition_implications(
    encoder: &mut crate::encoder::AYEncoder,
    requires: &[PureExpr],
    ensures: &[PureExpr],
    ghost_exprs: &[PureExpr],
) -> Result<Vec<PureExpr>, EncodingError> {
    let combined: Vec<PureExpr> = requires
        .iter()
        .chain(ensures.iter())
        .chain(ghost_exprs.iter())
        .cloned()
        .collect();
    let precondition_instances = instantiate_ghost_foralls_from(&combined, requires);

    let mut asserted_facts = Vec::new();
    let mut seen_facts = HashSet::new();
    let mut known = KnownBoolFacts::default();

    for expr in requires
        .iter()
        .chain(ghost_exprs.iter())
        .chain(precondition_instances.iter())
    {
        add_asserted_bool_fact(
            expr.clone(),
            &mut asserted_facts,
            &mut seen_facts,
            &mut known,
        );
    }

    let mut asserted_consequents = Vec::new();
    let mut encoded_facts = seen_facts.clone();
    loop {
        let mut changed = propagate_boolean_equalities(&asserted_facts, &mut known);
        let current_facts = asserted_facts.clone();

        for fact in current_facts {
            let before_len = asserted_facts.len();
            collect_new_implication_consequents(
                &fact,
                &mut known,
                encoder,
                &mut asserted_facts,
                &mut seen_facts,
                &mut encoded_facts,
                &mut asserted_consequents,
            )?;
            if asserted_facts.len() > before_len {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    if !asserted_consequents.is_empty() {
        debug!(
            "[flatten] ghost preconditions: asserted {} known-guard implication consequents",
            asserted_consequents.len()
        );
        for consequent in &asserted_consequents {
            debug!("[flatten]   precondition consequent: {consequent}");
        }
    }

    Ok(asserted_consequents)
}

/// Assert UF congruence bridges for collection method calls across ghost aliases.
///
/// Ghost blocks frequently produce alias facts such as `set == ^call_1`, while
/// the proof assertion mentions `set.contains(k)` and the method specs mention
/// `(^call_1).contains(k)`. Full EUF congruence would connect those terms from
/// the alias equality alone, but ay-dpll can miss that propagation for FSet/FMap
/// UFs. These equalities are direct logical consequences of the alias fact.
pub(crate) fn assert_ghost_alias_method_congruence(
    encoder: &mut crate::encoder::AYEncoder,
    requires: &[PureExpr],
    ensures: &[PureExpr],
    ghost_exprs: &[PureExpr],
) -> Result<(), EncodingError> {
    let aliases = collect_ghost_alias_pairs(ghost_exprs);
    if aliases.is_empty() {
        return Ok(());
    }

    let known_bool_facts = collect_known_bool_facts(requires.iter().chain(ghost_exprs.iter()));
    let mut calls = Vec::new();
    for expr in requires.iter().chain(ensures.iter()) {
        collect_ground_collection_method_calls(expr, &mut calls);
    }

    let mut seen = HashSet::new();
    let mut seen_literals = HashSet::new();
    for call in calls {
        for (left, right) in &aliases {
            let Some(counterpart_receiver) = alias_counterpart(&call.receiver, left, right) else {
                continue;
            };
            let counterpart = CollectionMethodCall {
                receiver: counterpart_receiver.clone(),
                method: call.method.clone(),
                args: call.args.clone(),
            };
            let original_expr = call.to_expr();
            let counterpart_expr = counterpart.to_expr();
            if !seen.insert((original_expr.clone(), counterpart_expr.clone())) {
                continue;
            }
            let original = encoder.encode_pure(&original_expr)?;
            let alias = encoder.encode_pure(&counterpart_expr)?;
            let eq = encoder.eq_term(original, alias);
            encoder.assert_term(eq);
            assert_known_alias_bool_literal(
                encoder,
                &original_expr,
                &counterpart_expr,
                &known_bool_facts,
                &mut seen_literals,
            )?;
        }
    }

    Ok(())
}

#[derive(Default)]
struct KnownBoolFacts {
    true_exprs: HashSet<PureExpr>,
    false_exprs: HashSet<PureExpr>,
}

fn add_asserted_bool_fact(
    expr: PureExpr,
    asserted_facts: &mut Vec<PureExpr>,
    seen_facts: &mut HashSet<PureExpr>,
    known: &mut KnownBoolFacts,
) -> bool {
    let inserted = seen_facts.insert(expr.clone());
    if inserted {
        asserted_facts.push(expr.clone());
    }
    let mut changed = add_known_true(expr.clone(), known);
    if let PureExpr::BinOp(left, BinOp::And, right) = expr {
        changed |= add_asserted_bool_fact(left.as_ref().clone(), asserted_facts, seen_facts, known);
        changed |=
            add_asserted_bool_fact(right.as_ref().clone(), asserted_facts, seen_facts, known);
    }
    inserted || changed
}

fn add_known_true(expr: PureExpr, known: &mut KnownBoolFacts) -> bool {
    match expr {
        PureExpr::Bool(true) => false,
        PureExpr::Bool(false) => known.false_exprs.insert(PureExpr::Bool(false)),
        PureExpr::UnOp(UnOp::Not, inner) => {
            let inserted = known
                .true_exprs
                .insert(PureExpr::UnOp(UnOp::Not, inner.clone()));
            add_known_false(inner.as_ref().clone(), known) || inserted
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            let inserted =
                known
                    .true_exprs
                    .insert(PureExpr::BinOp(left.clone(), BinOp::And, right.clone()));
            let left_changed = add_known_true(left.as_ref().clone(), known);
            let right_changed = add_known_true(right.as_ref().clone(), known);
            inserted || left_changed || right_changed
        }
        other => known.true_exprs.insert(other),
    }
}

fn add_known_false(expr: PureExpr, known: &mut KnownBoolFacts) -> bool {
    match expr {
        PureExpr::Bool(false) => false,
        PureExpr::Bool(true) => known.false_exprs.insert(PureExpr::Bool(true)),
        PureExpr::UnOp(UnOp::Not, inner) => {
            let inserted = known
                .false_exprs
                .insert(PureExpr::UnOp(UnOp::Not, inner.clone()));
            add_known_true(inner.as_ref().clone(), known) || inserted
        }
        other => known.false_exprs.insert(other),
    }
}

fn propagate_boolean_equalities(asserted_facts: &[PureExpr], known: &mut KnownBoolFacts) -> bool {
    let mut changed = false;
    for fact in asserted_facts {
        let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
            continue;
        };
        if is_known_true(left, known) {
            changed |= add_known_true(right.as_ref().clone(), known);
        }
        if is_known_true(right, known) {
            changed |= add_known_true(left.as_ref().clone(), known);
        }
        if is_known_false(left, known) {
            changed |= add_known_false(right.as_ref().clone(), known);
        }
        if is_known_false(right, known) {
            changed |= add_known_false(left.as_ref().clone(), known);
        }
    }
    changed
}

fn collect_known_bool_facts<'a>(exprs: impl IntoIterator<Item = &'a PureExpr>) -> KnownBoolFacts {
    let mut asserted_facts = Vec::new();
    let mut seen_facts = HashSet::new();
    let mut known = KnownBoolFacts::default();
    for expr in exprs {
        add_asserted_bool_fact(
            expr.clone(),
            &mut asserted_facts,
            &mut seen_facts,
            &mut known,
        );
    }

    while propagate_boolean_equalities(&asserted_facts, &mut known) {}
    known
}

fn assert_known_alias_bool_literal(
    encoder: &mut crate::encoder::AYEncoder,
    original: &PureExpr,
    counterpart: &PureExpr,
    known: &KnownBoolFacts,
    seen_literals: &mut HashSet<PureExpr>,
) -> Result<(), EncodingError> {
    if is_known_true(original, known) {
        assert_known_literal(encoder, counterpart.clone(), seen_literals)?;
    }
    if is_known_false(original, known) {
        assert_known_literal(
            encoder,
            PureExpr::UnOp(UnOp::Not, Arc::new(counterpart.clone())),
            seen_literals,
        )?;
    }
    if is_known_true(counterpart, known) {
        assert_known_literal(encoder, original.clone(), seen_literals)?;
    }
    if is_known_false(counterpart, known) {
        assert_known_literal(
            encoder,
            PureExpr::UnOp(UnOp::Not, Arc::new(original.clone())),
            seen_literals,
        )?;
    }
    Ok(())
}

fn assert_known_literal(
    encoder: &mut crate::encoder::AYEncoder,
    literal: PureExpr,
    seen_literals: &mut HashSet<PureExpr>,
) -> Result<(), EncodingError> {
    if seen_literals.insert(literal.clone()) {
        let term = encoder.encode_pure(&literal)?;
        let bool_term = encoder.coerce_bool_operand(term);
        encoder.assert_term(bool_term);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn collect_new_implication_consequents(
    fact: &PureExpr,
    known: &mut KnownBoolFacts,
    encoder: &mut crate::encoder::AYEncoder,
    asserted_facts: &mut Vec<PureExpr>,
    seen_facts: &mut HashSet<PureExpr>,
    encoded_facts: &mut HashSet<PureExpr>,
    asserted_consequents: &mut Vec<PureExpr>,
) -> Result<(), EncodingError> {
    match fact {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_new_implication_consequents(
                left,
                known,
                encoder,
                asserted_facts,
                seen_facts,
                encoded_facts,
                asserted_consequents,
            )?;
            collect_new_implication_consequents(
                right,
                known,
                encoder,
                asserted_facts,
                seen_facts,
                encoded_facts,
                asserted_consequents,
            )?;
        }
        PureExpr::BinOp(antecedent, BinOp::Implies, consequent)
            if is_known_true(antecedent, known)
                && encoded_facts.insert(consequent.as_ref().clone()) =>
        {
            let term = encoder.encode_pure(consequent)?;
            let bool_term = encoder.coerce_bool_operand(term);
            encoder.assert_term(bool_term);
            asserted_consequents.push(consequent.as_ref().clone());
            add_asserted_bool_fact(
                consequent.as_ref().clone(),
                asserted_facts,
                seen_facts,
                known,
            );
        }
        _ => {}
    }
    Ok(())
}

fn is_known_true(expr: &PureExpr, known: &KnownBoolFacts) -> bool {
    if matches!(eval_ground_bool(expr), Some(true)) || known.true_exprs.contains(expr) {
        return true;
    }
    match expr {
        PureExpr::UnOp(UnOp::Not, inner) => is_known_false(inner, known),
        PureExpr::BinOp(left, BinOp::And, right) => {
            is_known_true(left, known) && is_known_true(right, known)
        }
        PureExpr::BinOp(left, BinOp::Or, right) => {
            is_known_true(left, known) || is_known_true(right, known)
        }
        PureExpr::BinOp(left, BinOp::Implies, right) => {
            is_known_false(left, known) || is_known_true(right, known)
        }
        _ => false,
    }
}

fn is_known_false(expr: &PureExpr, known: &KnownBoolFacts) -> bool {
    if matches!(eval_ground_bool(expr), Some(false)) || known.false_exprs.contains(expr) {
        return true;
    }
    match expr {
        PureExpr::UnOp(UnOp::Not, inner) => is_known_true(inner, known),
        PureExpr::BinOp(left, BinOp::And, right) => {
            is_known_false(left, known) || is_known_false(right, known)
        }
        PureExpr::BinOp(left, BinOp::Or, right) => {
            is_known_false(left, known) && is_known_false(right, known)
        }
        PureExpr::BinOp(left, BinOp::Implies, right) => {
            is_known_true(left, known) && is_known_false(right, known)
        }
        _ => false,
    }
}

fn eval_ground_bool(expr: &PureExpr) -> Option<bool> {
    match expr {
        PureExpr::Bool(value) => Some(*value),
        PureExpr::UnOp(UnOp::Not, inner) => Some(!eval_ground_bool(inner)?),
        PureExpr::BinOp(left, BinOp::And, right) => {
            Some(eval_ground_bool(left)? && eval_ground_bool(right)?)
        }
        PureExpr::BinOp(left, BinOp::Or, right) => {
            Some(eval_ground_bool(left)? || eval_ground_bool(right)?)
        }
        PureExpr::BinOp(left, BinOp::Implies, right) => {
            Some(!eval_ground_bool(left)? || eval_ground_bool(right)?)
        }
        PureExpr::BinOp(left, op, right)
            if matches!(
                op,
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
            ) =>
        {
            let left = eval_ground_int(left)?;
            let right = eval_ground_int(right)?;
            Some(match op {
                BinOp::Eq => left == right,
                BinOp::Ne => left != right,
                BinOp::Lt => left < right,
                BinOp::Le => left <= right,
                BinOp::Gt => left > right,
                BinOp::Ge => left >= right,
                _ => return None,
            })
        }
        _ => None,
    }
}

fn eval_ground_int(expr: &PureExpr) -> Option<i64> {
    match expr {
        PureExpr::Int(value) => Some(*value),
        PureExpr::UnOp(UnOp::Neg, inner) => Some(-eval_ground_int(inner)?),
        PureExpr::BinOp(left, BinOp::Add, right) => {
            Some(eval_ground_int(left)? + eval_ground_int(right)?)
        }
        PureExpr::BinOp(left, BinOp::Sub, right) => {
            Some(eval_ground_int(left)? - eval_ground_int(right)?)
        }
        PureExpr::BinOp(left, BinOp::Mul, right) => {
            Some(eval_ground_int(left)? * eval_ground_int(right)?)
        }
        _ => None,
    }
}

#[derive(Clone)]
struct CollectionMethodCall {
    receiver: PureExpr,
    method: String,
    args: Vec<PureExpr>,
}

impl CollectionMethodCall {
    fn to_expr(&self) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(self.receiver.clone()),
            method: self.method.clone(),
            args: self.args.clone(),
        }
    }
}

fn collect_ghost_alias_pairs(ghost_exprs: &[PureExpr]) -> Vec<(PureExpr, PureExpr)> {
    let mut aliases = Vec::new();
    for expr in ghost_exprs {
        let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
            continue;
        };
        if ghost_alias_side_is_collection_carrier(left)
            && ghost_alias_side_is_collection_carrier(right)
            && left.as_ref() != right.as_ref()
        {
            aliases.push((left.as_ref().clone(), right.as_ref().clone()));
        }
    }
    aliases
}

fn ghost_alias_side_is_collection_carrier(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::Var(_, _) | PureExpr::Final(_) | PureExpr::Deref(_) | PureExpr::View(_)
    )
}

fn alias_counterpart<'a>(
    receiver: &PureExpr,
    left: &'a PureExpr,
    right: &'a PureExpr,
) -> Option<&'a PureExpr> {
    if receiver == left {
        Some(right)
    } else if receiver == right {
        Some(left)
    } else {
        None
    }
}

fn collect_ground_collection_method_calls(expr: &PureExpr, out: &mut Vec<CollectionMethodCall>) {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if is_collection_congruence_method(method) && args_are_ground_for_congruence(args) {
                out.push(CollectionMethodCall {
                    receiver: receiver.as_ref().clone(),
                    method: method.clone(),
                    args: args.clone(),
                });
            }
            collect_ground_collection_method_calls(receiver, out);
            for arg in args {
                collect_ground_collection_method_calls(arg, out);
            }
        }
        PureExpr::BinOp(left, _, right) => {
            collect_ground_collection_method_calls(left, out);
            collect_ground_collection_method_calls(right, out);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => collect_ground_collection_method_calls(inner, out),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_ground_collection_method_calls(cond, out);
            collect_ground_collection_method_calls(then_expr, out);
            collect_ground_collection_method_calls(else_expr, out);
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                collect_ground_collection_method_calls(arg, out);
            }
        }
        PureExpr::Forall { .. }
        | PureExpr::Exists { .. }
        | PureExpr::Match { .. }
        | PureExpr::Let { .. }
        | PureExpr::LetAssume { .. }
        | PureExpr::LetObligation { .. }
        | PureExpr::Closure { .. }
        | PureExpr::Bool(_)
        | PureExpr::Int(_)
        | PureExpr::Float(_)
        | PureExpr::Var(_, _) => {}
        #[allow(unreachable_patterns)]
        _ => {}
    }
}

fn is_collection_congruence_method(method: &str) -> bool {
    matches!(
        method,
        "contains"
            | "contains_ghost"
            | "len"
            | "len_ghost"
            | "is_empty"
            | "is_empty_ghost"
            | "get"
            | "lookup"
            | "index"
            | "index_logic"
    )
}

fn args_are_ground_for_congruence(args: &[PureExpr]) -> bool {
    args.iter().all(|arg| {
        !arg.any_free_var(|name, _| {
            // User/local variables are valid ground solver constants. The
            // quantified binders we must avoid are skipped by not descending
            // into Forall/Exists, so every remaining Var is a ground term.
            name.is_empty()
        })
    })
}

/// Instantiate forall quantifiers from `source_exprs` using ground constants
/// collected from `context_exprs`.
fn instantiate_ghost_foralls_from(
    context_exprs: &[PureExpr],
    source_exprs: &[PureExpr],
) -> Vec<PureExpr> {
    use std::collections::HashMap;

    let ground_constants = collect_ground_int_constants(context_exprs);
    let known_int_values = collect_known_int_values_for_ghost(context_exprs);
    let max_constants = 20;
    let constants = if ground_constants.len() > max_constants {
        &ground_constants[..max_constants]
    } else {
        &ground_constants
    };

    if constants.is_empty() {
        return Vec::new();
    }

    let mut instances = Vec::new();
    let max_total = 50;

    for expr in source_exprs {
        if let PureExpr::Forall { var, body, .. } = expr {
            for &constant in constants {
                if instances.len() >= max_total {
                    break;
                }
                if ghost_forall_candidate_makes_antecedent_false(
                    body,
                    var,
                    constant,
                    &known_int_values,
                ) {
                    continue;
                }
                let mut subst = HashMap::new();
                subst.insert(var.clone(), PureExpr::Int(constant));
                instances.push(body.substitute(&subst));
            }
        }
        if instances.len() >= max_total {
            break;
        }
    }

    instances
}

fn collect_known_int_values_for_ghost(
    exprs: &[PureExpr],
) -> std::collections::HashMap<PureExpr, i64> {
    let mut values = std::collections::HashMap::new();
    for expr in exprs {
        collect_known_int_values_for_ghost_expr(expr, &mut values);
    }
    values
}

fn collect_known_int_values_for_ghost_expr(
    expr: &PureExpr,
    values: &mut std::collections::HashMap<PureExpr, i64>,
) {
    match expr {
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            if let PureExpr::Int(value) = right.as_ref() {
                values.insert(left.as_ref().clone(), *value);
            }
            if let PureExpr::Int(value) = left.as_ref() {
                values.insert(right.as_ref().clone(), *value);
            }
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_known_int_values_for_ghost_expr(left, values);
            collect_known_int_values_for_ghost_expr(right, values);
        }
        _ => {}
    }
}

fn ghost_forall_candidate_makes_antecedent_false(
    body: &PureExpr,
    var: &str,
    candidate_value: i64,
    known_int_values: &std::collections::HashMap<PureExpr, i64>,
) -> bool {
    let PureExpr::BinOp(antecedent, BinOp::Implies, _) = body else {
        return false;
    };
    ghost_antecedent_false_for_candidate(antecedent, var, candidate_value, known_int_values)
}

fn ghost_antecedent_false_for_candidate(
    expr: &PureExpr,
    var: &str,
    candidate_value: i64,
    known_int_values: &std::collections::HashMap<PureExpr, i64>,
) -> bool {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            ghost_antecedent_false_for_candidate(left, var, candidate_value, known_int_values)
                || ghost_antecedent_false_for_candidate(
                    right,
                    var,
                    candidate_value,
                    known_int_values,
                )
        }
        PureExpr::BinOp(left, BinOp::Le, right) => {
            if is_bound_var_ref(left, var) {
                ghost_known_int_value(right, known_int_values)
                    .is_some_and(|bound| candidate_value > bound)
            } else if is_bound_var_ref(right, var) {
                ghost_known_int_value(left, known_int_values)
                    .is_some_and(|bound| bound > candidate_value)
            } else {
                false
            }
        }
        PureExpr::BinOp(left, BinOp::Lt, right) => {
            if is_bound_var_ref(left, var) {
                ghost_known_int_value(right, known_int_values)
                    .is_some_and(|bound| candidate_value >= bound)
            } else if is_bound_var_ref(right, var) {
                ghost_known_int_value(left, known_int_values)
                    .is_some_and(|bound| bound >= candidate_value)
            } else {
                false
            }
        }
        PureExpr::BinOp(left, BinOp::Ge, right) => ghost_antecedent_false_for_candidate(
            &PureExpr::BinOp(right.clone(), BinOp::Le, left.clone()),
            var,
            candidate_value,
            known_int_values,
        ),
        PureExpr::BinOp(left, BinOp::Gt, right) => ghost_antecedent_false_for_candidate(
            &PureExpr::BinOp(right.clone(), BinOp::Lt, left.clone()),
            var,
            candidate_value,
            known_int_values,
        ),
        _ => false,
    }
}

fn ghost_known_int_value(
    expr: &PureExpr,
    known_int_values: &std::collections::HashMap<PureExpr, i64>,
) -> Option<i64> {
    match expr {
        PureExpr::Int(value) => Some(*value),
        PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner) => ghost_known_int_value(inner, known_int_values),
        _ => known_int_values.get(expr).copied(),
    }
}

fn is_bound_var_ref(expr: &PureExpr, expected: &str) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == expected,
        PureExpr::Deref(inner) | PureExpr::Final(inner) => is_bound_var_ref(inner, expected),
        _ => false,
    }
}

/// Returns true if the expression is a ground constant (Int or Bool literal).
pub(in crate::verify) fn is_ground_constant(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_)
    )
}

/// Returns true if the expression is complex enough to be worth substituting
/// (MethodCall, LogicFnCall, or compound expressions involving these).
pub(in crate::verify) fn is_substitutable_expr(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall { .. }
            | PureExpr::LogicFnCall { .. }
            | PureExpr::BinOp(_, _, _)
            | PureExpr::UnOp(_, _)
            | PureExpr::Final(_)
            | PureExpr::Deref(_)
            | PureExpr::View(_)
    )
}

fn should_descend_for_constant_substitution(node: &PureExpr) -> bool {
    !matches!(
        node,
        PureExpr::Forall { .. }
            | PureExpr::Exists { .. }
            | PureExpr::Match { .. }
            | PureExpr::Let { .. }
            | PureExpr::LetAssume { .. }
            | PureExpr::LetObligation { .. }
            | PureExpr::Closure { .. }
            // `Final` is a TEMPORAL wrapper, not a function of its inner
            // expression's current value: from `e == c` one may NOT conclude
            // `^e == ^c` (that is the `^p == *p` inversion of the
            // Final-collapse audit, reached through equals-for-equals
            // rewriting instead of through a fold). Substituting a
            // current-state const-map entry (`*g2 => 1`) INSIDE a `Final`
            // wrapper minted `Final(Int(1))` from the ghost fact
            // `^*g2 == 1`, which the Fix A constant-carrier guard refuses —
            // erroring the whole solve (ghost/ghost_let regression, #124).
            // The `Final` node ITSELF still gets a whole-node lookup (the
            // prune only stops descent), so `^*g2 => 1` entries keep firing.
            | PureExpr::Final(_)
    )
}

fn substitute_constants_with_lookup(
    expr: &PureExpr,
    mut lookup: impl FnMut(&PureExpr) -> Option<PureExpr>,
) -> Option<PureExpr> {
    expr.rewrite_bottom_up_prune_with_depth_limit_if_changed(
        MAX_ENCODING_DEPTH,
        should_descend_for_constant_substitution,
        |node| lookup(&node),
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum PureExprHead {
    Bool,
    Int,
    Float,
    Var,
    BinOp,
    UnOp,
    Ite,
    Old,
    Deref,
    Final,
    View,
    MethodCall,
    Forall,
    Exists,
    Match,
    LogicFnCall,
    Let,
    LetAssume,
    LetObligation,
    Closure,
    Other,
}

impl PureExprHead {
    fn of(expr: &PureExpr) -> Self {
        match expr {
            PureExpr::Bool(_) => Self::Bool,
            PureExpr::Int(_) => Self::Int,
            PureExpr::Float(_) => Self::Float,
            PureExpr::Var(_, _) => Self::Var,
            PureExpr::BinOp(_, _, _) => Self::BinOp,
            PureExpr::UnOp(_, _) => Self::UnOp,
            PureExpr::Ite(_, _, _) => Self::Ite,
            PureExpr::Old(_) => Self::Old,
            PureExpr::Deref(_) => Self::Deref,
            PureExpr::Final(_) => Self::Final,
            PureExpr::View(_) => Self::View,
            PureExpr::MethodCall { .. } => Self::MethodCall,
            PureExpr::Forall { .. } => Self::Forall,
            PureExpr::Exists { .. } => Self::Exists,
            PureExpr::Match { .. } => Self::Match,
            PureExpr::LogicFnCall { .. } => Self::LogicFnCall,
            PureExpr::Let { .. } => Self::Let,
            PureExpr::LetAssume { .. } => Self::LetAssume,
            PureExpr::LetObligation { .. } => Self::LetObligation,
            PureExpr::Closure { .. } => Self::Closure,
            _ => Self::Other,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum SubstituteLookupKey<'a> {
    BinOp {
        op: BinOp,
        left: PureExprHead,
        right: PureExprHead,
    },
    UnOp {
        op: UnOp,
        inner: PureExprHead,
    },
    Final {
        inner: PureExprHead,
    },
    Deref {
        inner: PureExprHead,
    },
    View {
        inner: PureExprHead,
    },
    MethodCall {
        method: &'a str,
        receiver: PureExprHead,
        arg_len: usize,
    },
    LogicFnCall {
        name: &'a str,
        arg_len: usize,
    },
}

impl<'a> SubstituteLookupKey<'a> {
    fn of(expr: &'a PureExpr) -> Option<Self> {
        match expr {
            PureExpr::BinOp(left, op, right) => Some(Self::BinOp {
                op: *op,
                left: PureExprHead::of(left),
                right: PureExprHead::of(right),
            }),
            PureExpr::UnOp(op, inner) => Some(Self::UnOp {
                op: *op,
                inner: PureExprHead::of(inner),
            }),
            PureExpr::Final(inner) => Some(Self::Final {
                inner: PureExprHead::of(inner),
            }),
            PureExpr::Deref(inner) => Some(Self::Deref {
                inner: PureExprHead::of(inner),
            }),
            PureExpr::View(inner) => Some(Self::View {
                inner: PureExprHead::of(inner),
            }),
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => Some(Self::MethodCall {
                method,
                receiver: PureExprHead::of(receiver),
                arg_len: args.len(),
            }),
            PureExpr::LogicFnCall { name, args } => Some(Self::LogicFnCall {
                name,
                arg_len: args.len(),
            }),
            _ => None,
        }
    }
}

type IndexedConstLookup<'a> =
    std::collections::HashMap<SubstituteLookupKey<'a>, Vec<(&'a PureExpr, &'a PureExpr)>>;

fn build_indexed_const_lookup<'a>(
    const_lookup: &'a std::collections::HashMap<&'a PureExpr, &'a PureExpr>,
) -> IndexedConstLookup<'a> {
    let mut index: IndexedConstLookup<'a> = std::collections::HashMap::new();
    for (&expr, &constant) in const_lookup {
        if let Some(key) = SubstituteLookupKey::of(expr) {
            index.entry(key).or_default().push((expr, constant));
        }
    }
    index
}

/// Substitute known constant values for matching subexpressions.
/// Returns Some(new_expr) if any substitution was made, None otherwise.
#[cfg(test)]
pub(in crate::verify) fn substitute_constants(
    expr: &PureExpr,
    const_map: &[(&PureExpr, &PureExpr)],
) -> Option<PureExpr> {
    substitute_constants_with_lookup(expr, |node| {
        const_map
            .iter()
            .find(|(candidate, _)| *candidate == node)
            .map(|(_, constant)| (*constant).clone())
    })
}

/// Hash-indexed variant of [`substitute_constants`] for the hot path in
/// `flatten_ghost_implications` Phase 4. Uses O(1) HashMap lookups instead
/// of O(n) linear scans per tree node. (#2535)
fn substitute_constants_indexed(
    expr: &PureExpr,
    const_lookup: &std::collections::HashMap<&PureExpr, &PureExpr>,
) -> Option<PureExpr> {
    let indexed_lookup = build_indexed_const_lookup(const_lookup);
    substitute_constants_with_lookup(expr, |node| {
        let key = SubstituteLookupKey::of(node)?;
        indexed_lookup.get(&key).and_then(|candidates| {
            candidates
                .iter()
                .find(|(candidate, _)| *candidate == node)
                .map(|(_, constant)| (*constant).clone())
        })
    })
}

/// Collect ground Int constants from all expressions in the context.
///
/// Descends into all subexpressions to find `PureExpr::Int(_)` leaves.
/// Returns deduplicated set of integer values.
fn collect_ground_int_constants(exprs: &[PureExpr]) -> Vec<i64> {
    use std::collections::HashSet;

    fn walk(expr: &PureExpr, found: &mut HashSet<i64>) {
        match expr {
            PureExpr::Int(n) => {
                found.insert(*n);
            }
            PureExpr::BinOp(l, _, r) => {
                walk(l, found);
                walk(r, found);
            }
            PureExpr::UnOp(_, inner)
            | PureExpr::Final(inner)
            | PureExpr::Deref(inner)
            | PureExpr::View(inner)
            | PureExpr::Old(inner) => {
                walk(inner, found);
            }
            PureExpr::Ite(c, t, e) => {
                walk(c, found);
                walk(t, found);
                walk(e, found);
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                walk(receiver, found);
                for arg in args {
                    walk(arg, found);
                }
            }
            PureExpr::LogicFnCall { args, .. } => {
                for arg in args {
                    walk(arg, found);
                }
            }
            PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
                walk(body, found);
            }
            PureExpr::Let { value, body, .. } => {
                walk(value, found);
                walk(body, found);
            }
            PureExpr::LetAssume { assumption, body } => {
                walk(assumption, found);
                walk(body, found);
            }
            PureExpr::LetObligation { obligation, body } => {
                walk(obligation, found);
                walk(body, found);
            }
            PureExpr::Match { scrutinee, arms } => {
                walk(scrutinee, found);
                for arm in arms {
                    walk(&arm.body, found);
                }
            }
            PureExpr::Closure { body, .. } => {
                walk(body, found);
            }
            _ => {}
        }
    }

    let mut found = std::collections::HashSet::new();
    for expr in exprs {
        walk(expr, &mut found);
    }
    let mut result: Vec<i64> = found.into_iter().collect();
    result.sort();
    result
}

/// Instantiate universally quantified ghost facts with ground constants.
///
/// For each `forall var, body` in the ghost context, substitutes the
/// quantified variable with each ground Int constant from the context.
/// This is sound universal instantiation (forall elimination).
///
/// Cap: at most 20 ground constants per forall to prevent explosion.
/// Cap: at most 50 total ground instances to prevent solver overload.
fn instantiate_ghost_foralls(ghost_exprs: &[PureExpr]) -> Vec<PureExpr> {
    use std::collections::HashMap;

    let ground_constants = collect_ground_int_constants(ghost_exprs);
    let known_int_values = collect_known_int_values_for_ghost(ghost_exprs);
    // Cap constants to prevent combinatorial explosion
    let max_constants = 20;
    let constants = if ground_constants.len() > max_constants {
        &ground_constants[..max_constants]
    } else {
        &ground_constants
    };

    if constants.is_empty() {
        return Vec::new();
    }

    let mut instances = Vec::new();
    let max_total = 50;

    for expr in ghost_exprs {
        if let PureExpr::Forall { var, body, .. } = expr {
            for &constant in constants {
                if instances.len() >= max_total {
                    break;
                }
                if ghost_forall_candidate_makes_antecedent_false(
                    body,
                    var,
                    constant,
                    &known_int_values,
                ) {
                    continue;
                }
                let mut subst = HashMap::new();
                subst.insert(var.clone(), PureExpr::Int(constant));
                instances.push(body.substitute(&subst));
            }
        }
        if instances.len() >= max_total {
            break;
        }
    }

    instances
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    #[test]
    fn test_is_ground_constant() {
        assert!(is_ground_constant(&PureExpr::Int(42)));
        assert!(is_ground_constant(&PureExpr::Bool(true)));
        assert!(!is_ground_constant(&PureExpr::Var("x".into(), None)));
        assert!(!is_ground_constant(&PureExpr::View(Arc::new(
            PureExpr::Int(1)
        ))));
    }

    #[test]
    fn test_is_substitutable_expr() {
        assert!(is_substitutable_expr(&PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("v".into(), None)),
            method: "len".into(),
            args: vec![],
        }));
        assert!(is_substitutable_expr(&PureExpr::LogicFnCall {
            name: "f".into(),
            args: vec![PureExpr::Var("x".into(), None)],
        }));
        assert!(is_substitutable_expr(&PureExpr::View(Arc::new(
            PureExpr::Var("x".into(), None)
        ))));
        assert!(!is_substitutable_expr(&PureExpr::Int(42)));
        assert!(!is_substitutable_expr(&PureExpr::Var("x".into(), None)));
    }

    #[test]
    fn test_substitute_constants_direct_match_and_no_match() {
        let f_a = PureExpr::LogicFnCall {
            name: "f".into(),
            args: vec![PureExpr::Var("a".into(), None)],
        };
        let f_b = PureExpr::LogicFnCall {
            name: "f".into(),
            args: vec![PureExpr::Var("b".into(), None)],
        };
        let zero = PureExpr::Int(0);
        let map: Vec<(&PureExpr, &PureExpr)> = vec![(&f_a, &zero)];
        assert_eq!(substitute_constants(&f_a, &map), Some(PureExpr::Int(0)));
        assert_eq!(substitute_constants(&f_b, &map), None);
    }

    #[test]
    fn test_substitute_constants_binop() {
        let f_a = PureExpr::LogicFnCall {
            name: "f".into(),
            args: vec![PureExpr::Var("a".into(), None)],
        };
        let f_b = PureExpr::LogicFnCall {
            name: "f".into(),
            args: vec![PureExpr::Var("b".into(), None)],
        };
        let expr = PureExpr::BinOp(Arc::new(f_a.clone()), BinOp::Add, Arc::new(f_b.clone()));
        let zero = PureExpr::Int(0);
        let one = PureExpr::Int(1);
        let map: Vec<(&PureExpr, &PureExpr)> = vec![(&f_a, &zero), (&f_b, &one)];
        assert_eq!(
            substitute_constants(&expr, &map),
            Some(PureExpr::BinOp(
                Arc::new(PureExpr::Int(0)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ))
        );
    }

    #[test]
    fn test_substitute_constants_nested_and_view() {
        let f_a = PureExpr::LogicFnCall {
            name: "f".into(),
            args: vec![PureExpr::Var("a".into(), None)],
        };
        let zero = PureExpr::Int(0);
        let map: Vec<(&PureExpr, &PureExpr)> = vec![(&f_a, &zero)];
        // g(f(a)) where f(a) = 0 → g(0)
        let g_fa = PureExpr::LogicFnCall {
            name: "g".into(),
            args: vec![f_a.clone()],
        };
        assert_eq!(
            substitute_constants(&g_fa, &map),
            Some(PureExpr::LogicFnCall {
                name: "g".into(),
                args: vec![PureExpr::Int(0)]
            })
        );
        // View(f(a)) where f(a) = 0 → View(0)
        let view_fa = PureExpr::View(Arc::new(f_a.clone()));
        assert_eq!(
            substitute_constants(&view_fa, &map),
            Some(PureExpr::View(Arc::new(PureExpr::Int(0))))
        );
    }

    /// ★#124 pin: Phase-4 constant propagation must NOT rewrite under a
    /// `Final` wrapper. `Final` is temporal, not a function of its inner
    /// expression's current value: `e == c` does not entail `^e == ^c`
    /// (that is the `^p == *p` inversion). Substituting `*g2 => 1` inside
    /// the ghost fact `^*g2 == 1` minted `Final(Int(1))` — refused
    /// fail-closed by the Fix A constant-carrier guard, which errored the
    /// whole `ghost/ghost_let` solve. Whole-node `Final` keys still fire.
    #[test]
    fn test_substitute_constants_never_rewrites_under_final() {
        let deref_g2 = PureExpr::Deref(Arc::new(PureExpr::Var("g2".into(), None)));
        let final_deref_g2 = PureExpr::Final(Arc::new(deref_g2.clone()));
        let one = PureExpr::Int(1);

        // Same-state key `*g2 => 1` must not reach inside `^*g2`.
        let map: Vec<(&PureExpr, &PureExpr)> = vec![(&deref_g2, &one)];
        assert_eq!(
            substitute_constants(&final_deref_g2, &map),
            None,
            "a current-state const-map entry must not rewrite under `Final`"
        );
        let fact = PureExpr::BinOp(
            Arc::new(final_deref_g2.clone()),
            BinOp::Eq,
            Arc::new(one.clone()),
        );
        assert_eq!(
            substitute_constants(&fact, &map),
            None,
            "`^*g2 == 1` must survive Phase 4 untouched by the `*g2 => 1` entry"
        );

        // A whole-node key `^*g2 => 1` still substitutes (prune stops
        // descent, not the node's own lookup).
        let final_map: Vec<(&PureExpr, &PureExpr)> = vec![(&final_deref_g2, &one)];
        let expr = PureExpr::BinOp(
            Arc::new(final_deref_g2.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::Var("y".into(), None)),
        );
        assert_eq!(
            substitute_constants(&expr, &final_map),
            Some(PureExpr::BinOp(
                Arc::new(one.clone()),
                BinOp::Eq,
                Arc::new(PureExpr::Var("y".into(), None)),
            )),
            "whole-node Final keys must keep firing"
        );
    }

    #[test]
    fn test_substitute_constants_leaf_no_change() {
        let map: Vec<(&PureExpr, &PureExpr)> = vec![];
        assert_eq!(
            substitute_constants(&PureExpr::Var("x".into(), None), &map),
            None
        );
        assert_eq!(substitute_constants(&PureExpr::Int(1), &map), None);
    }

    #[test]
    fn instantiate_ghost_foralls_skips_statically_false_bounds() {
        let i = PureExpr::Var("i".into(), None);
        let pred = PureExpr::Var("pred".into(), None);
        let pred_len = PureExpr::MethodCall {
            receiver: Arc::new(pred.clone()),
            method: "len".into(),
            args: vec![],
        };
        let result_at_i = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("result".into(), None)),
            method: "index_logic".into(),
            args: vec![i.clone()],
        };
        let pred_at_i = PureExpr::MethodCall {
            receiver: Arc::new(pred.clone()),
            method: "index_logic".into(),
            args: vec![i.clone()],
        };
        let antecedent = PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Int(0)),
                BinOp::Le,
                Arc::new(i.clone()),
            )),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(i),
                BinOp::Lt,
                Arc::new(pred_len.clone()),
            )),
        );
        let body = PureExpr::BinOp(
            Arc::new(antecedent),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(result_at_i),
                BinOp::Eq,
                Arc::new(pred_at_i),
            )),
        );
        let forall = PureExpr::Forall {
            var: "i".into(),
            var_sort: None,
            body: Arc::new(body),
            triggers: Vec::new(),
        };
        let pred_len_is_one =
            PureExpr::BinOp(Arc::new(pred_len), BinOp::Eq, Arc::new(PureExpr::Int(1)));

        let instances =
            instantiate_ghost_foralls_from(&[forall.clone(), pred_len_is_one], &[forall]);
        let rendered = format!("{instances:?}");
        assert!(
            rendered.contains("Int(0)"),
            "in-bounds constant 0 should still instantiate: {instances:?}"
        );
        assert!(
            !rendered.contains("Int(1)"),
            "constant 1 is statically outside i < pred.len() when pred.len() == 1: {instances:?}"
        );
    }
}
