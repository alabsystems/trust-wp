// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! By-value alias constraint assertion and invariant receiver extraction.
//!
//! Contains function-specific utilities: by-value alias constraints
//! (`_current` chain equalities for non-mutable-borrow verification) and
//! invariant receiver extraction.
//!
//! Shared utilities (`infer_result_sort`, `assert_current_chain_alias_constraints`)
//! live in `verify::shared_constraints`.

use tracing::debug;
use trust_wp_core::formula::PureExpr;

use crate::{
    encoder::sort_context::{ay_sort_to_expr_sort, DerivedKind},
    error::EncodingError,
};

fn is_mutref_carrier_sort(sort: &ay_dpll::api::Sort) -> bool {
    matches!(
        ay_sort_to_expr_sort(sort),
        Some(trust_wp_core::formula::ExprSort::MutRef(_))
    ) || matches!(
        sort,
        ay_dpll::api::Sort::Uninterpreted(name) if name.starts_with("__trust_wp_mutref::")
    )
}

/// Extract the receiver variable name from an invariant method call expression.
///
/// Given a PureExpr like `x.__trust_wp_invariant_Vec()` or `(*x).__trust_wp_invariant_Vec()`,
/// returns `Some("x")` if the method name matches. Returns None otherwise.
pub(in crate::verify) fn extract_invariant_receiver_var(
    expr: &PureExpr,
    method_name: &str,
) -> Option<String> {
    let PureExpr::MethodCall {
        receiver, method, ..
    } = expr
    else {
        return None;
    };
    if method != method_name {
        return None;
    }
    // Peel through Deref: (*x).method() => x
    let inner = if let PureExpr::Deref(inner) = receiver.as_ref() {
        inner.as_ref()
    } else {
        receiver.as_ref()
    };
    if let PureExpr::Var(name, _) = inner {
        Some(name.clone())
    } else {
        None
    }
}

/// Assert dereference identity constraints for by-value parameters (#970).
///
/// In the regular (non-mutable-borrow) verification path, call-site
/// assumptions from `FnMut::call_mut` specs produce variables like
/// `f_current` (from `(*self)`) and `f_final` (from `^self`), while the
/// function's own ensures clause references bare `f`. Without identity
/// constraints, these are disconnected SMT variables.
///
/// This function asserts `*v = v` for by-value parameters: any variable
/// `FOO_current` is equated with `FOO` when both exist. This covers:
/// - `v_current = v` (direct parameter dereference)
/// - `v_final_current = v_final` (deref of prophecy)
/// - `v_final_final_current = v_final_final` (deref of nested prophecy)
///
/// We do NOT equate `v_final_final = v_final` (prophecy-of-prophecy).
/// In multi-call scenarios (e.g., `call_fnmut(&mut c); call_fnmut(c)`),
/// `Final(Var("x"))` and `Final(Final(Var("x")))` represent distinct
/// intermediate states in a mutation chain. Collapsing them would destroy
/// the state-threading needed for sequential FnMut call verification.
pub(in crate::verify) fn assert_by_value_alias_constraints(
    encoder: &mut crate::encoder::AYEncoder,
) -> Result<(), EncodingError> {
    let mut var_names = encoder.var_names();
    var_names.sort();
    let var_set: std::collections::HashSet<&str> = var_names.iter().map(String::as_str).collect();

    let mut aliases: Vec<(String, String)> = Vec::new();
    // O(1) dedup check for alias names, replacing O(N) linear scan (#1937)
    let mut alias_names: std::collections::HashSet<String> = std::collections::HashSet::new();

    for name in &var_names {
        // FOO_current = FOO: by-value dereference identity (*v = v)
        // This handles v_current=v, v_final_current=v_final, etc.
        //
        // Also handles chained _current suffixes from Box<T> deref in contracts:
        // When a contract has `**(expr)` where one deref is a Box deref (no-op
        // in MIR) and the other is a reference deref, the encoder produces
        // `x_current_current`. The body only produces `x_current` (Box deref
        // is an alias). Allowing the chain `x_current_current = x_current`
        // connects the contract to the body constraints. (#1302)
        if let Some((DerivedKind::Current, base)) = DerivedKind::strip_from(name) {
            if var_set.contains(base) && !encoder.var_sort(base).is_some_and(is_mutref_carrier_sort)
            {
                alias_names.insert(name.clone());
                aliases.push((name.clone(), base.to_string()));
            }
        }
    }

    // For deeper _current chains from Box deref (e.g., x_current_current where
    // x_current doesn't exist but x does), create intermediate aliases. This
    // happens when the contract has a Box deref that the body doesn't, and the
    // encoder's deref-push-into-args produces the deeper chain without creating
    // the intermediate variable. (#1302)
    //
    // Example: contract has Deref(tuple_get_1(Deref(Var("x")))) which produces
    // tuple_get_1(x_current_current), but body has tuple_get_1(Var("x")) which
    // produces tuple_get_1(x). The intermediate x_current was never created.
    // We need: x_current_current = x_current = x.
    for name in &var_names {
        let mut remaining = name.as_str();
        let mut root: Option<&str> = None;
        // Peel _current suffixes to find a root that exists in var_set.
        while let Some((DerivedKind::Current, base)) = DerivedKind::strip_from(remaining) {
            if var_set.contains(base) {
                // Direct base exists — no intermediate chain needed for THIS
                // step, but continue peeling in case the first loop already
                // handles it via the direct match.
                root = Some(base);
                break;
            }
            remaining = base;
            // Check if the peeled base itself is in var_set (the ultimate root).
            if var_set.contains(remaining) {
                root = Some(remaining);
            }
        }
        // If we found a root that's not the direct parent (i.e., we peeled
        // past the direct base), create the full chain from root to name.
        if let Some(r) = root {
            if encoder.var_sort(r).is_some_and(is_mutref_carrier_sort) {
                continue;
            }
            let r_str = r.to_string();
            let mut current = r_str.clone();
            let mut chain_part = r_str;
            // Build the chain from root up to the full name.
            while chain_part != *name {
                chain_part = DerivedKind::Current.format_name(&chain_part);
                if alias_names.insert(chain_part.clone()) {
                    aliases.push((chain_part.clone(), current.clone()));
                }
                current.clone_from(&chain_part);
            }
        }
    }

    aliases.sort();
    aliases.dedup();

    for (alias_name, target_name) in &aliases {
        // Use resolve_var_sort_or_int to check declared sorts, sort hints,
        // and suffix-derived base sorts before falling back to Int. (#1608)
        let sort = encoder.resolve_var_sort_or_int(target_name);
        let alias_var = encoder.get_or_declare_var(alias_name, sort.clone())?;
        let target_var = encoder.get_or_declare_var(target_name, sort.clone())?;
        if alias_var == target_var {
            continue;
        }
        encoder.assert_eq(alias_var, target_var);

        debug!("  alias: {alias_name} = {target_name}");
    }

    Ok(())
}
