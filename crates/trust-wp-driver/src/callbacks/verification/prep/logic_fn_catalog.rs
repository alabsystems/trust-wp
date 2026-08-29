// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic-function catalog shaping for shared verification preparation.

use std::collections::{HashMap, HashSet};

use rustc_middle::ty::TyCtxt;
use trust_wp_core::{formula::PureExpr, logic::LogicFnDef};
use trust_wp_driver::StdSpec;

use crate::callbacks::contract_rewrite::{
    rewrite_logic_fn_defs_shadowed_builtin_calls, rewrite_logic_method_calls_expr,
    UserShadowedBuiltins,
};

/// Build the downstream (solver-facing) logic-function set, neutralizing
/// functions whose postconditions could not be verified (#1878).
///
/// An unverified logic function must not contribute ANY axiom a caller could
/// rely on: neither its `ensures` spec axiom (unproven, hence unsound to
/// assume) nor its defining/body axiom. This function previously achieved that
/// by *dropping* such functions from the set entirely.
///
/// Dropping, however, has a sort side effect: a caller that still references
/// the (now-absent) function forces the SMT encoder to synthesize an opaque
/// placeholder UF, and AST-level sort inference falls through to the *demoting*
/// `SortFallbackToIntFromLogicFn` catch-all. That demotion discards
/// already-proved obligations — e.g. `binary_search_list`'s `List::index`,
/// where `len_logic`'s `#[ensures(result >= 0)]` is unverified, so `len_logic`
/// was dropped, its uses in the loop invariant/precondition fell back to `Int`,
/// and the proved loop-initialization obligation was demoted to `Unknown`.
///
/// Instead, KEEP each unverified function in the set but strip it to a bare
/// declaration: force it opaque (suppresses the defining/body axiom regardless
/// of caller scope) and clear its `ensures` (suppresses the spec axiom). This
/// is soundness-equivalent to dropping — no axiom of an unverified function
/// reaches any caller — while preserving the function's declared signature so
/// its return sort resolves without the demoting fallback. Preserving the slice
/// length also keeps `mode_overrides` aligned. (#1878; binary_search_list
/// demotion false positive)
pub(in crate::callbacks) fn filter_downstream_logic_fns(
    logic_fns: &[LogicFnDef],
    unverified_axioms: &HashSet<String>,
) -> Vec<LogicFnDef> {
    logic_fns
        .iter()
        .map(|lf| {
            if unverified_axioms.contains(lf.full_path()) {
                let mut neutralized = lf.clone();
                neutralized.set_is_opaque(true);
                neutralized.set_ensures(Vec::new());
                neutralized
            } else {
                lf.clone()
            }
        })
        .collect()
}

pub(in crate::callbacks) fn build_trait_logic_fn_groups(
    tcx: TyCtxt<'_>,
    logic_fns: &[LogicFnDef],
) -> HashMap<String, String> {
    let logic_fn_paths: HashSet<&str> = logic_fns.iter().map(LogicFnDef::full_path).collect();
    let mut groups = HashMap::new();

    for logic_fn in crate::logic::find_logic_functions(tcx) {
        if !logic_fn.is_trait_method {
            continue;
        }
        let full_path = logic_fn.full_path;
        if !logic_fn_paths.contains(full_path.as_str()) {
            continue;
        }
        let Some((trait_path, _)) = full_path.rsplit_once("::") else {
            continue;
        };
        groups.insert(full_path.clone(), trait_path.to_string());
    }

    groups
}

pub(in crate::callbacks) fn downgrade_unverified_logic_specs<K, F>(
    user_specs: &mut HashMap<K, StdSpec>,
    is_unverified_logic_fn: F,
) where
    K: Eq + std::hash::Hash,
    F: Fn(&K) -> bool,
{
    for (key, spec) in user_specs.iter_mut() {
        if is_unverified_logic_fn(key) {
            spec.ensures.clear();
        }
    }
}

/// Rewrite `receiver.method(args)` in logic function bodies, requires, and
/// ensures into `LogicFnCall("method", [receiver, ...args])` form, mirroring
/// the contract rewriting in `rewrite_parsed_contract_structure`. Logic bodies
/// are parsed without type/path context, so they retain method-call syntax for
/// calls that the contract parser later lowers to `LogicFnCall`. Without this
/// alignment, prechecks such as `inline_logic_fn_calls_from_defs` produce
/// expressions whose `MethodCall` and `LogicFnCall` shapes do not match across
/// the equality, blocking proofs like `x.g(y) == x.f(y) + 1` for a sealed
/// default `g(self, x) = self.f(x) + 1`.
pub(super) fn rewrite_logic_fn_method_calls(
    logic_fns: &mut [LogicFnDef],
    logic_method_names: &HashSet<String>,
    user_shadowed_builtins: &UserShadowedBuiltins,
) {
    for lf in logic_fns.iter_mut() {
        if logic_method_names.is_empty() {
            break;
        }
        lf.set_body(rewrite_logic_method_calls_expr(
            lf.body(),
            logic_method_names,
        ));
        for require in lf.requires_mut() {
            *require = rewrite_logic_method_calls_expr(require, logic_method_names);
        }
        for ensure in lf.ensures_mut() {
            *ensure = rewrite_logic_method_calls_expr(ensure, logic_method_names);
        }
    }
    // Shadowed builtin methods (`self[i]` on an ADT with a user IndexLogic
    // impl) in logic fn bodies must route through LogicFnCall as well, so
    // defining axioms reference the same interpreted symbol as call sites.
    rewrite_logic_fn_defs_shadowed_builtin_calls(logic_fns, user_shadowed_builtins);
}

/// Substitute evaluated const-item values into logic-fn bodies and contract
/// clauses (ledger int-shift-full).
///
/// A name that collides with one of the fn's own params is NOT substituted —
/// the parameter binds tighter than any same-named crate const. Fns that
/// reference no substitutable const are left untouched.
pub(super) fn substitute_const_items_into_logic_fns(
    logic_fns: &mut [LogicFnDef],
    substitutions: &HashMap<String, PureExpr>,
) {
    if substitutions.is_empty() {
        return;
    }
    for lf in logic_fns.iter_mut() {
        let filtered: HashMap<String, PureExpr> = substitutions
            .iter()
            .filter(|(name, _)| !lf.params().iter().any(|param| param == *name))
            .map(|(name, value)| (name.clone(), value.clone()))
            .collect();
        if filtered.is_empty() {
            continue;
        }
        let references =
            |expr: &PureExpr| expr.any_free_var(|name, _sort| filtered.contains_key(name));
        if !(references(lf.body())
            || lf.requires().iter().any(|e| references(e))
            || lf.ensures().iter().any(|e| references(e)))
        {
            continue;
        }
        let new_body = lf.body().substitute(&filtered);
        lf.set_body(new_body);
        for require in lf.requires_mut() {
            *require = require.substitute(&filtered);
        }
        for ensure in lf.ensures_mut() {
            *ensure = ensure.substitute(&filtered);
        }
    }
}
