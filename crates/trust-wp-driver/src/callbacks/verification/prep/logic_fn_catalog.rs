// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic-function catalog shaping for shared verification preparation.

use std::collections::{BTreeSet, HashMap, HashSet};

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
                neutralized(lf)
            } else {
                lf.clone()
            }
        })
        .collect()
}

/// `lf` stripped to a bare declaration: no defining axiom, no spec axiom.
/// The one spelling of neutralization, for the downstream set and for the
/// logic pass's own environment alike.
pub(in crate::callbacks) fn neutralized(lf: &LogicFnDef) -> LogicFnDef {
    let mut neutralized = lf.clone();
    neutralized.set_is_opaque(true);
    neutralized.set_ensures(Vec::new());
    neutralized
}

/// Name a neutralized axiom this obligation's own symbols can reach, if any.
///
/// Neutralization (see [`filter_downstream_logic_fns`]) WITHDRAWS an unproved
/// logic function's axioms. The solver may then build a model in which the
/// withdrawn fact is false — and a model that exists only because a fact was
/// taken away refutes nothing the user wrote. Publishing it as a
/// counterexample asserts "a state exists that violates your contract"; the
/// honest claim is "I cannot decide this without the axiom I refused to
/// grant". The verdict path asks this question before it publishes a
/// refutation.
///
/// Deliberately over-approximate, and only ever in the refusal direction. The
/// same logic symbol is spelled as a full path, a crate-relative path, or a
/// bare method name depending on which rewrite produced the call, so a call is
/// matched on any of the three; and reachability runs through the bodies and
/// clauses of the functions that are still live, because a withdrawn fact
/// reached two hops away is just as absent. A spurious match costs one
/// withheld refutation; a missed one publishes a false counterexample, which
/// is the worse error.
pub(in crate::callbacks) fn neutralized_axiom_reached<'e>(
    logic_fns: &[LogicFnDef],
    unverified_axioms: &HashSet<String>,
    obligations: impl IntoIterator<Item = &'e PureExpr>,
) -> Option<String> {
    if unverified_axioms.is_empty() {
        return None;
    }
    let mut withdrawn: HashMap<String, &str> = HashMap::new();
    for path in unverified_axioms {
        for spelling in path_spellings(path) {
            withdrawn.entry(spelling).or_insert(path.as_str());
        }
    }
    // A live function's axioms still hold, so reaching one is not a hit — but
    // the symbols ITS body and clauses mention are reachable from here, and a
    // withdrawn fact two hops away is just as absent.
    let mut live: HashMap<String, Vec<&LogicFnDef>> = HashMap::new();
    for lf in logic_fns {
        let is_withdrawn = unverified_axioms.contains(lf.full_path());
        for spelling in def_spellings(lf) {
            if is_withdrawn {
                withdrawn.entry(spelling).or_insert(lf.full_path());
            } else {
                live.entry(spelling).or_default().push(lf);
            }
        }
    }

    let mut pending: Vec<String> = Vec::new();
    for obligation in obligations {
        collect_logic_call_names(obligation, &mut pending);
    }
    let mut seen: HashSet<String> = HashSet::new();
    let mut expanded: HashSet<&str> = HashSet::new();
    let mut hits: BTreeSet<&str> = BTreeSet::new();
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        if let Some(path) = withdrawn.get(&name) {
            hits.insert(path);
            continue;
        }
        let Some(defs) = live.get(&name) else {
            continue;
        };
        for def in defs {
            if !expanded.insert(def.full_path()) {
                continue;
            }
            collect_logic_call_names(def.body(), &mut pending);
            for clause in def.requires().iter().chain(def.ensures()) {
                collect_logic_call_names(clause, &mut pending);
            }
        }
    }
    hits.into_iter().next().map(str::to_owned)
}

/// Every way a call site may spell the logic function defined at `full_path`.
///
/// The solver symbol is the injective unique id, but clauses that never
/// reached name normalization still carry the source path, the crate-relative
/// path, or the bare method name.
fn path_spellings(full_path: &str) -> Vec<String> {
    let mut spellings = vec![
        full_path.to_string(),
        trust_wp_core::logic::identity::logic_fn_unique_id(full_path),
    ];
    if let Some((_, relative)) = full_path.split_once("::") {
        if !relative.is_empty() {
            spellings.push(relative.to_string());
        }
    }
    if let Some((_, leaf)) = full_path.rsplit_once("::") {
        if !leaf.is_empty() {
            spellings.push(leaf.to_string());
        }
    }
    spellings
}

/// The spellings a definition answers to, including the id it was renamed to.
fn def_spellings(lf: &LogicFnDef) -> Vec<String> {
    let mut spellings = path_spellings(lf.full_path());
    spellings.push(lf.name().to_string());
    spellings.push(lf.short_name().to_string());
    spellings
}

/// Collect the callee names a formula mentions.
///
/// Both call shapes count: contract rewriting turns a receiver call into
/// `LogicFnCall`, but clauses that never went through it keep `MethodCall`,
/// and the axiom is equally absent under either spelling.
fn collect_logic_call_names(expr: &PureExpr, out: &mut Vec<String>) {
    expr.any_recursive(|node| {
        match node {
            PureExpr::LogicFnCall { name, .. } => out.push(name.clone()),
            PureExpr::MethodCall { method, .. } => out.push(method.clone()),
            _ => {}
        }
        false
    });
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

#[cfg(test)]
mod neutralized_axiom_reached_tests {
    use std::collections::HashSet;

    use trust_wp_core::{
        formula::PureExpr,
        logic::{identity::logic_fn_unique_id, LogicFnDef},
    };

    use super::neutralized_axiom_reached;

    fn def(full_path: &str, body: PureExpr) -> LogicFnDef {
        let leaf = full_path.rsplit_once("::").map_or(full_path, |(_, l)| l);
        let mut lf = LogicFnDef::new(
            leaf.to_string(),
            full_path.to_string(),
            vec!["self".to_string()],
            body,
        );
        // Name normalization renames every definition to its injective id, so
        // call sites in real obligations are spelled that way and nothing else.
        lf.assign_unique_id(logic_fn_unique_id(full_path));
        lf
    }

    fn call(full_path: &str) -> PureExpr {
        PureExpr::LogicFnCall {
            name: logic_fn_unique_id(full_path),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }
    }

    #[test]
    fn a_call_to_the_withdrawn_axiom_is_named() {
        let bumped = def("c::Spec::bumped", PureExpr::Bool(true));
        let unverified: HashSet<String> = ["c::Spec::bumped".to_string()].into_iter().collect();
        let obligation = call("c::Spec::bumped");

        assert_eq!(
            neutralized_axiom_reached(&[bumped], &unverified, [&obligation]),
            Some("c::Spec::bumped".to_string())
        );
    }

    #[test]
    fn a_withdrawn_axiom_two_hops_away_is_still_reached() {
        // `via` keeps its axioms, so the model is only free where `bumped` was
        // withdrawn — but the obligation reaches that freedom through `via`.
        let bumped = def("c::Spec::bumped", PureExpr::Bool(true));
        let via = def("c::via", call("c::Spec::bumped"));
        let unverified: HashSet<String> = ["c::Spec::bumped".to_string()].into_iter().collect();
        let obligation = call("c::via");

        assert_eq!(
            neutralized_axiom_reached(&[bumped, via], &unverified, [&obligation]),
            Some("c::Spec::bumped".to_string())
        );
    }

    #[test]
    fn an_obligation_that_reaches_no_withdrawn_axiom_keeps_its_refutation() {
        let base = def("c::Spec::base", PureExpr::Bool(true));
        let bumped = def("c::Spec::bumped", PureExpr::Bool(true));
        let unverified: HashSet<String> = ["c::Spec::bumped".to_string()].into_iter().collect();
        let obligation = call("c::Spec::base");

        assert_eq!(
            neutralized_axiom_reached(&[base, bumped], &unverified, [&obligation]),
            None
        );
    }

    #[test]
    fn nothing_withdrawn_means_nothing_withheld() {
        let bumped = def("c::Spec::bumped", PureExpr::Bool(true));
        let obligation = call("c::Spec::bumped");

        assert_eq!(
            neutralized_axiom_reached(&[bumped], &HashSet::new(), [&obligation]),
            None
        );
    }

    #[test]
    fn a_withdrawn_path_absent_from_the_slice_is_still_matched() {
        // The catalog slice need not contain the definition whose postcondition
        // was refused; the path alone must still withhold the refutation.
        let unverified: HashSet<String> = ["c::Spec::bumped".to_string()].into_iter().collect();
        let obligation = call("c::Spec::bumped");

        assert_eq!(
            neutralized_axiom_reached(&[], &unverified, [&obligation]),
            Some("c::Spec::bumped".to_string())
        );
    }

    #[test]
    fn a_cycle_between_live_definitions_terminates() {
        let mut left = def("c::left", call("c::right"));
        let right = def("c::right", call("c::left"));
        left.set_body(call("c::right"));
        let unverified: HashSet<String> = ["c::gone".to_string()].into_iter().collect();
        let obligation = call("c::left");

        assert_eq!(
            neutralized_axiom_reached(&[left, right], &unverified, [&obligation]),
            None
        );
    }
}
