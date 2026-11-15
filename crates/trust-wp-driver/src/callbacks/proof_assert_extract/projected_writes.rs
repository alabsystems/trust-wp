// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Projected write handling for proof_assert extraction.
//!
//! When ghost blocks mutate tuple fields through `deref_mut`, the MIR creates
//! intermediate variables and projected write facts. This module detects these
//! patterns and updates the substitution map in-place.

use std::collections::HashMap;

use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_index, tuple_logic_fn_arity},
    BinOp, PureExpr,
};

/// Return true when an assumption is useful for repairing tuple projected writes
/// in a proof_assert snapshot substitution map.
pub(in crate::callbacks) fn is_projected_write_repair_assumption(assumption: &PureExpr) -> bool {
    projected_tuple_write(assumption).is_some()
        || projected_write_constructor_alias(assumption).is_some()
}

/// Update substitutions with projected write facts from call assumptions.
///
/// When a ghost block mutates a tuple field through deref_mut, the MIR creates:
///   - `call_N = deref_mut(&mut p)` — intermediate variable
///   - `tuple_get_I(call_N) == V` — projected write fact (call assumption)
///   - `T::deref_mut.postcondition(*(tuple_ctor(...)), call_N)` — call assumption
///
/// The substitution map has `p → tupleK(a0, a1, ...)` reflecting the pre-mutation
/// value. This function detects the pattern and updates the tuple constructor
/// in-place: `p → tupleK(a0, ..., V_at_I, ..., aN)`.
///
/// Returns the number of projected writes applied. (#1572)
pub(in crate::callbacks) fn apply_projected_writes_to_substitutions(
    substitutions: &mut HashMap<String, PureExpr>,
    call_assumptions: &[PureExpr],
) -> usize {
    // Collect projected write facts: tuple_get_I(var) == value
    let mut projected_writes: Vec<(String, usize, PureExpr)> = Vec::new();
    for assumption in call_assumptions {
        if let Some(write) = projected_tuple_write(assumption) {
            projected_writes.push(write);
        }
    }
    if projected_writes.is_empty() {
        return 0;
    }

    // Find deref_mut postcondition patterns that link intermediates to substitution
    // variables: T::deref_mut.postcondition(*(tupleK(...)), call_N)
    // The first arg contains the original tuple constructor (matching a substitution
    // value), and the second arg is the intermediate variable name.
    let mut intermediate_to_sub_key: HashMap<String, String> = HashMap::new();
    for assumption in call_assumptions {
        if let PureExpr::MethodCall { method, args, .. } = assumption {
            if method == "postcondition" && args.len() == 2 {
                if let PureExpr::Var(ref intermediate_name, _) = args[1] {
                    // The first arg is Deref(tuple_ctor(...)) — extract the inner
                    // constructor and find which substitution variable has it.
                    let ctor_expr = match &args[0] {
                        PureExpr::Deref(inner) => inner.as_ref(),
                        other => other,
                    };
                    for (sub_key, sub_value) in substitutions.iter() {
                        if sub_value == ctor_expr {
                            record_projected_write_alias_mapping(
                                &mut intermediate_to_sub_key,
                                intermediate_name,
                                sub_key,
                            );
                            break;
                        }
                    }
                }
            }
        }
        if let Some((intermediate_name, ctor_expr)) = projected_write_constructor_alias(assumption)
        {
            for (sub_key, sub_value) in substitutions.iter() {
                if sub_value == ctor_expr {
                    record_projected_write_alias_mapping(
                        &mut intermediate_to_sub_key,
                        intermediate_name,
                        sub_key,
                    );
                    break;
                }
            }
        }
    }

    // Apply projected writes to substitution values
    let mut applied = 0usize;
    for (intermediate_var, field_idx, new_value) in &projected_writes {
        let sub_key = intermediate_to_sub_key
            .get(intermediate_var)
            .cloned()
            .or_else(|| {
                substitutions
                    .contains_key(intermediate_var)
                    .then(|| intermediate_var.clone())
            });
        let Some(sub_key) = sub_key else { continue };
        let Some(sub_value) = substitutions.get_mut(&sub_key) else {
            continue;
        };
        if let PureExpr::LogicFnCall { args, name } = sub_value {
            if let Some(arity) = tuple_logic_fn_arity(name) {
                if arity == args.len() && *field_idx < args.len() {
                    args[*field_idx] = new_value.clone();
                    applied += 1;
                }
            }
        }
    }
    applied
}

fn projected_tuple_write(assumption: &PureExpr) -> Option<(String, usize, PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = assumption else {
        return None;
    };
    selector_var(lhs.as_ref())
        .map(|(var_name, field_idx)| (var_name, field_idx, rhs.as_ref().clone()))
        .or_else(|| {
            selector_var(rhs.as_ref())
                .map(|(var_name, field_idx)| (var_name, field_idx, lhs.as_ref().clone()))
        })
}

fn selector_var(expr: &PureExpr) -> Option<(String, usize)> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    let field_idx = tuple_field_logic_fn_index(name)?;
    if args.len() != 1 {
        return None;
    }
    let PureExpr::Var(var_name, _) = &args[0] else {
        return None;
    };
    Some((var_name.clone(), field_idx))
}

fn projected_write_constructor_alias(assumption: &PureExpr) -> Option<(&str, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = assumption else {
        return None;
    };
    match (lhs.as_ref(), rhs.as_ref()) {
        (PureExpr::Var(name, _), expr) => Some((name.as_str(), strip_deref_wrapper(expr))),
        (expr, PureExpr::Var(name, _)) => Some((name.as_str(), strip_deref_wrapper(expr))),
        _ => None,
    }
}

fn strip_deref_wrapper(expr: &PureExpr) -> &PureExpr {
    match expr {
        PureExpr::Deref(inner) => inner.as_ref(),
        other => other,
    }
}

fn record_projected_write_alias_mapping(
    intermediate_to_sub_key: &mut HashMap<String, String>,
    intermediate_name: &str,
    sub_key: &str,
) {
    intermediate_to_sub_key
        .entry(intermediate_name.to_string())
        .or_insert_with(|| sub_key.to_string());
    if let Some(alias_name) = projected_write_alias_name(intermediate_name) {
        intermediate_to_sub_key
            .entry(alias_name)
            .or_insert_with(|| sub_key.to_string());
    }
}

fn projected_write_alias_name(name: &str) -> Option<String> {
    if let Some(local_id) = name.strip_prefix("$local_") {
        return local_id
            .chars()
            .all(|ch| ch.is_ascii_digit())
            .then(|| format!("$call_{local_id}"));
    }
    if let Some(local_id) = name.strip_prefix("$call_") {
        return local_id
            .chars()
            .all(|ch| ch.is_ascii_digit())
            .then(|| format!("$local_{local_id}"));
    }
    None
}
