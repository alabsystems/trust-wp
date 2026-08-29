// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager existential instantiation subsystem.
//!
//! This module implements eager instantiation of negated existential
//! postconditions using ground witness terms from preconditions.
//! It works around ay-dpll's E-matching limitations with multi-trigger
//! patterns by collecting ground terms and asserting instantiated
//! ground clauses directly.

mod collectors;
pub(crate) mod matching;
pub(crate) mod structural_eq;

#[cfg(test)]
pub(crate) use collectors::{collect_ground_postcondition_mut_calls, collect_ground_resolve_calls};
#[cfg(test)]
pub(crate) use matching::{
    expr_mentions_bound_var, normalize_deref_final, try_match_expr, try_match_method_call,
    try_match_resolve_call,
};
#[cfg(test)]
pub(crate) use structural_eq::exprs_structurally_equal;
#[cfg(test)]
mod tests;

use tracing::debug;
use trust_wp_core::formula::PureExpr;

use super::substitute_vars_in_expr;
use crate::{encoder::AYEncoder, error::EncodingError};

/// A postcondition_mut method call pattern: receiver, method args.
pub(crate) struct MethodCallPattern<'a> {
    pub(crate) receiver: &'a PureExpr,
    pub(crate) args: &'a [PureExpr],
}

/// A normalized method call with owned expressions (after Deref/Final flattening).
struct NormalizedMethodCall {
    receiver: PureExpr,
    args: Vec<PureExpr>,
}

/// Eagerly instantiate negated existential postconditions using ground witness
/// terms from preconditions.
///
/// ay-dpll's E-matching does not support multi-trigger patterns (each pattern
/// must bind ALL quantifier variables). When a postcondition like
/// `exists<st1, st2, r> A(st1, r) && B(st1, st2) && C(st2)` is negated to
/// `forall<st1, st2, r> NOT(A && B && C)`, no single trigger covers all
/// three variables, so the universal is never instantiated.
///
/// This function works around the limitation by:
/// 1. Collecting bound variables and the body from nested existentials
/// 2. Finding ground `postcondition_mut` method calls in the preconditions
/// 3. Matching body method calls against ground calls to build a witness binding
/// 4. Asserting `NOT body[witness]` as a ground clause
///
/// The ground clause is a logical consequence of the negated universal
/// (it's a specific instantiation), so asserting it is sound. It makes the
/// ground terms available to the DPLL solver without requiring E-matching.
///
/// Must be called after `encode_and_assert_negated_postconditions` and after
/// preconditions have been asserted. (#970, closures/07_mutable_capture)
///
/// `body_assumptions` carries `LetAssume` assumptions collected from the
/// return-expression body. Functions like `call_fnmut` make sequential
/// `f(); f()` calls that lower to body-local `postcondition_mut(...)`
/// assumptions — those are exactly the ground witnesses an
/// `exists<st1, st2, r>` postcondition needs. Reusing the binder-aware
/// ground walker on both `requires` and `body_assumptions` lets the eager
/// instantiator find witnesses regardless of where the closure is invoked.
pub(crate) fn assert_eager_negated_existential_instantiations(
    encoder: &mut AYEncoder,
    ensures: &[PureExpr],
    requires: &[PureExpr],
    body_assumptions: &[&PureExpr],
) -> Result<(), EncodingError> {
    for ensure in ensures {
        let Some((bound_vars, body)) = flatten_nested_existentials(ensure) else {
            continue;
        };
        if !AYEncoder::body_has_any_postcondition_mut(body) {
            continue;
        }
        try_eager_instantiate_one(encoder, &bound_vars, body, requires, body_assumptions)?;
    }
    Ok(())
}

/// Attempt eager instantiation for a single existential postcondition.
///
/// Builds a witness binding from ground precondition terms, asserts resolve
/// facts for terminal states, then asserts NOT body[witness].
fn try_eager_instantiate_one(
    encoder: &mut AYEncoder,
    bound_vars: &[String],
    body: &PureExpr,
    requires: &[PureExpr],
    body_assumptions: &[&PureExpr],
) -> Result<(), EncodingError> {
    debug!("  [eager-neg-inst] bound_vars: {bound_vars:?}");
    debug!("  [eager-neg-inst] body: {body:?}");

    // Collect and normalize ground postcondition_mut calls from preconditions
    // and body-local LetAssume assumptions. Body assumptions carry the
    // sequential call witnesses (e.g., `f(); f()` in `call_fnmut`) that
    // existential postconditions over chained `postcondition_mut(...)` need.
    // Call-site assumptions use Deref/Final wrappers (from MIR's *self/^self)
    // while ensures bodies use bare variables. Normalization bridges the gap.
    let raw_ground_calls_requires = collectors::collect_ground_postcondition_mut_calls(requires);
    let raw_ground_calls_body =
        collectors::collect_ground_postcondition_mut_calls_from_refs(body_assumptions);
    let synthetic_ground_calls =
        encoder.synthetic_ground_postcondition_mut_calls_from_once_requires(requires);
    let ground_calls: Vec<NormalizedMethodCall> = raw_ground_calls_requires
        .iter()
        .chain(raw_ground_calls_body.iter())
        .map(|gc| NormalizedMethodCall {
            receiver: matching::normalize_deref_final(gc.receiver),
            args: gc
                .args
                .iter()
                .map(matching::normalize_deref_final)
                .collect(),
        })
        .chain(
            synthetic_ground_calls
                .iter()
                .map(|(receiver, args)| NormalizedMethodCall {
                    receiver: matching::normalize_deref_final(receiver),
                    args: args.iter().map(matching::normalize_deref_final).collect(),
                }),
        )
        .collect();

    log_ground_calls(&ground_calls);

    if ground_calls.is_empty() {
        return Ok(());
    }

    let body_calls = collectors::collect_body_postcondition_mut_calls(body, bound_vars);

    log_body_calls(&body_calls);

    if body_calls.is_empty() {
        return Ok(());
    }

    let mut binding = build_witness_binding(bound_vars, &body_calls, &ground_calls);
    extend_binding_with_resolves(&mut binding, body, bound_vars, requires, body_assumptions);

    log_binding_state(&binding, bound_vars);

    if binding.len() < bound_vars.len() {
        debug!(
            "  [eager-neg-inst] incomplete binding: {}/{} vars resolved",
            binding.len(),
            bound_vars.len()
        );

        return Ok(());
    }

    let instantiated_body = substitute_vars_in_expr(body, &binding);

    // Assert resolve facts for terminal postcondition_mut chain states.
    // By-value FnMut parameters are consumed at function exit, so the terminal
    // state resolves (Rust ownership). Without this, NOT(resolve(f_final_final))
    // is satisfiable because the axiom system's Skolem-based resolve can't be
    // unified with the concrete state variable in one E-matching round.
    let body_resolve_calls = collectors::collect_body_resolve_calls(body, bound_vars);
    for body_resolve_arg in &body_resolve_calls {
        let substituted = substitute_vars_in_expr(body_resolve_arg, &binding);

        debug!("  [eager-neg-inst] asserting resolve({substituted:?})");

        let resolve_expr = PureExpr::LogicFnCall {
            name: "resolve".to_string(),
            args: vec![substituted],
        };
        let resolve_term = encoder.encode_pure(&resolve_expr)?;
        encoder.assert_term(resolve_term);
    }

    debug!(
        "  [eager-neg-inst] asserting ground negated instantiation for {} bound vars",
        bound_vars.len()
    );

    let body_term = encoder.encode_pure(&instantiated_body)?;
    let body_term = encoder.coerce_bool_operand(body_term);
    let negated = encoder.solver_mut().not(body_term);
    encoder.assert_term(negated);
    Ok(())
}

/// Build witness binding by iteratively matching body patterns against ground calls.
fn build_witness_binding(
    bound_vars: &[String],
    body_calls: &[MethodCallPattern<'_>],
    ground_calls: &[NormalizedMethodCall],
) -> std::collections::HashMap<String, PureExpr> {
    use std::collections::HashMap;
    let mut binding: HashMap<String, PureExpr> = HashMap::new();
    let mut progress = true;
    while progress {
        progress = false;
        for body_call in body_calls {
            for ground_call in ground_calls {
                let gc_pattern = MethodCallPattern {
                    receiver: &ground_call.receiver,
                    args: &ground_call.args,
                };
                if let Some(new_bindings) =
                    matching::try_match_method_call(body_call, &gc_pattern, bound_vars, &binding)
                {
                    for (var, val) in new_bindings {
                        if let std::collections::hash_map::Entry::Vacant(e) = binding.entry(var) {
                            e.insert(val);
                            progress = true;
                        }
                    }
                }
            }
        }
    }
    binding
}

/// Extend the binding with resolve() call matches from preconditions and
/// body-local LetAssume assumptions. (#970)
fn extend_binding_with_resolves(
    binding: &mut std::collections::HashMap<String, PureExpr>,
    body: &PureExpr,
    bound_vars: &[String],
    requires: &[PureExpr],
    body_assumptions: &[&PureExpr],
) {
    let body_resolve_calls = collectors::collect_body_resolve_calls(body, bound_vars);
    let raw_ground_resolve_calls = collectors::collect_ground_resolve_calls(requires);
    let raw_ground_resolve_calls_body =
        collectors::collect_ground_resolve_calls_from_refs(body_assumptions);
    let normalized_ground_resolves: Vec<PureExpr> = raw_ground_resolve_calls
        .iter()
        .chain(raw_ground_resolve_calls_body.iter())
        .map(|r| matching::normalize_deref_final(r))
        .collect();
    for body_resolve in &body_resolve_calls {
        for ground_resolve in &normalized_ground_resolves {
            if let Some(new_bindings) =
                matching::try_match_resolve_call(body_resolve, ground_resolve, bound_vars, binding)
            {
                for (var, val) in new_bindings {
                    binding.entry(var).or_insert(val);
                }
            }
        }
    }
}

fn log_ground_calls(ground_calls: &[NormalizedMethodCall]) {
    debug!(
        "  [eager-neg-inst] found {} ground postcondition_mut calls in requires",
        ground_calls.len()
    );
    for (i, gc) in ground_calls.iter().enumerate() {
        debug!(
            "    ground[{i}]: receiver={:?}, args={:?}",
            gc.receiver, gc.args
        );
    }
}

fn log_body_calls(body_calls: &[MethodCallPattern<'_>]) {
    debug!(
        "  [eager-neg-inst] found {} body postcondition_mut calls",
        body_calls.len()
    );
    for (i, bc) in body_calls.iter().enumerate() {
        debug!(
            "    body[{i}]: receiver={:?}, args={:?}",
            bc.receiver, bc.args
        );
    }
}

fn log_binding_state(binding: &std::collections::HashMap<String, PureExpr>, bound_vars: &[String]) {
    debug!(
        "  [eager-neg-inst] binding state: {}/{} vars resolved",
        binding.len(),
        bound_vars.len()
    );
    for (k, v) in binding {
        debug!("    {k} -> {v:?}");
    }
}

/// Flatten nested `Exists` into a list of bound variable names and the
/// innermost non-Exists body.
pub(crate) fn flatten_nested_existentials(expr: &PureExpr) -> Option<(Vec<String>, &PureExpr)> {
    let mut vars = Vec::new();
    let mut current = expr;
    while let PureExpr::Exists {
        var,
        body,
        triggers,
        ..
    } = current
    {
        if !triggers.is_empty() {
            // Stop: user-provided triggers mean E-matching handles this level.
            // Don't collect the triggered variable — consistent with
            // collect_nested_quantifier_vars in logic_fn.rs which uses a match
            // guard to skip triggered quantifiers entirely.
            break;
        }
        vars.push(var.clone());
        current = body;
    }
    if vars.is_empty() {
        None
    } else {
        Some((vars, current))
    }
}
