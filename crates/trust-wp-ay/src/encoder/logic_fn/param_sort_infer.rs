// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parameter sort inference helpers for logic function registration.
//!
//! All functions in this module are pure PureExpr walkers — no `&mut self`,
//! no `AYEncoder` state. They infer parameter sorts (Seq, Datatype) from
//! logic function bodies, requires, and ensures clauses.
//!
//! Extracted from `logic_fn.rs` as part of the encoder decomposition (#2072).

use std::collections::{HashMap, HashSet};

use ay_dpll::api::{DatatypeSort, FuncDecl};
use trust_wp_core::formula::{PureExpr, PureExprDepthLimitedTraversalExt as _};

use super::super::{
    match_enc::SwitchTarget,
    sort_context::{extract_base_var_name, is_seq_family_sort},
};

pub(super) fn infer_seq_like_params(
    logic_fn: &trust_wp_core::logic::LogicFnDef,
) -> HashSet<String> {
    let mut seq_candidates = HashSet::new();
    let mut fset_params = HashSet::new();
    let param_names: HashSet<&str> = logic_fn.params().iter().map(String::as_str).collect();

    for expr in logic_fn
        .requires()
        .iter()
        .chain(logic_fn.ensures().iter())
        .chain(std::iter::once(logic_fn.body()))
    {
        collect_seq_like_params(expr, &param_names, &mut seq_candidates);
        collect_fset_like_params(expr, &param_names, &mut fset_params);
    }

    // Parameters used with FSet-only methods (peek, remove, is_empty,
    // intersection, difference) are FSet — not Seq. Without this exclusion,
    // shared methods like `contains` and `len` cause FSet parameters to be
    // misclassified as Seq, breaking sort inference for logic functions like
    // `set_max`. (#2701, bug/vcgen.rs regression)
    for fset_param in &fset_params {
        seq_candidates.remove(fset_param);
    }

    seq_candidates
}

/// Methods that are unambiguously FSet (not shared with Seq/FMap).
///
/// `peek`, `remove` (1-arg), `is_empty`, `intersection`, `difference` are
/// FSet-only. `contains` and `len` are shared with Seq and cannot disambiguate.
/// `insert` with 1 arg is FSet but with 2 args is FMap — we include it here
/// because Seq does not have `insert` at all.
const FSET_ONLY_METHODS: &[&str] = &[
    "peek",
    "remove",
    "is_empty",
    "intersection",
    "difference",
    "insert",
];

/// Collect parameters used with FSet-only methods.
///
/// These parameters should NOT be classified as Seq even if they also appear
/// with shared methods like `contains` or `len`. (#2701)
fn collect_fset_like_params(
    expr: &PureExpr,
    param_names: &HashSet<&str>,
    out: &mut HashSet<String>,
) {
    expr.for_each_recursive_with_depth_limit(super::super::MAX_ENCODING_DEPTH, |node| {
        if let PureExpr::MethodCall {
            receiver, method, ..
        } = node
        {
            if FSET_ONLY_METHODS.contains(&method.as_str()) {
                if let Some(name) = extract_base_var_name(receiver) {
                    if param_names.contains(name) {
                        out.insert(name.to_string());
                    }
                }
            }
        }
    });
}

fn collect_seq_like_params(
    expr: &PureExpr,
    param_names: &HashSet<&str>,
    out: &mut HashSet<String>,
) {
    const SEQ_METHODS: &[&str] = &[
        "len",
        "index",
        "index_logic",
        "subsequence",
        "push_back",
        "set",
        "concat",
        "contains",
    ];

    expr.for_each_recursive_with_depth_limit(super::super::MAX_ENCODING_DEPTH, |node| {
        if let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = node
        {
            if SEQ_METHODS.contains(&method.as_str()) {
                if let Some(name) = extract_base_var_name(receiver) {
                    if param_names.contains(name) {
                        out.insert(name.to_string());
                    }
                }
            }
            if method == "concat" {
                for arg in args {
                    if let Some(name) = extract_base_var_name(arg) {
                        if param_names.contains(name) {
                            out.insert(name.to_string());
                        }
                    }
                }
            }
        }
    });
}

/// Infer Datatype sorts for logic function parameters by scanning the body
/// for `match param { Ctor1(..) => .., Ctor2(..) => .. }` patterns. (#2002)
///
/// When a logic function body contains a match expression whose scrutinee is
/// a parameter (or `*param`), and the match arms use `Constructor` patterns,
/// we can infer that the parameter has a Datatype sort built from those
/// constructors. Without this, parameters on custom ADTs (e.g., `List::len(self)`)
/// fall through to `Sort::Int`, causing sort mismatches when call-site arguments
/// are Datatype-sorted.
pub(super) fn infer_param_datatypes_from_body(
    logic_fn: &trust_wp_core::logic::LogicFnDef,
) -> HashMap<&str, DatatypeSort> {
    let param_set: HashSet<&str> = logic_fn.params().iter().map(String::as_str).collect();
    let mut result: HashMap<&str, DatatypeSort> = HashMap::new();

    collect_param_datatypes(logic_fn.body(), &param_set, &mut result);
    for expr in logic_fn.requires().iter().chain(logic_fn.ensures().iter()) {
        collect_param_datatypes(expr, &param_set, &mut result);
    }

    result
}

/// Recursively scan an expression for `Match` on parameter variables and
/// extract Datatype sorts from constructor patterns.
fn collect_param_datatypes<'a>(
    expr: &PureExpr,
    param_names: &HashSet<&'a str>,
    out: &mut HashMap<&'a str, DatatypeSort>,
) {
    expr.for_each_recursive_with_depth_limit(super::super::MAX_ENCODING_DEPTH, |node| {
        let PureExpr::Match { scrutinee, arms } = node else {
            return;
        };
        // Check if the scrutinee is a parameter (Var or Deref(Var))
        let Some(param_name) = extract_match_scrutinee_param(scrutinee, param_names) else {
            return;
        };
        if out.contains_key(param_name) {
            return;
        }
        if let Some(target) = SwitchTarget::from_arms(arms) {
            let dt = target.datatype();
            // Only use UserDefined datatypes — Option/Result have
            // their own encoding paths and don't need this inference.
            if matches!(target, SwitchTarget::UserDefined { .. }) {
                out.insert(param_name, dt);
            }
        }
    });
}

/// Extract the parameter name from a match scrutinee, if it's a Var or
/// Deref(Var) referencing a known parameter.
fn extract_match_scrutinee_param<'a>(
    scrutinee: &PureExpr,
    param_names: &HashSet<&'a str>,
) -> Option<&'a str> {
    let var_name = match scrutinee {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner) => {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                Some(name.as_str())
            } else {
                None
            }
        }
        _ => None,
    };
    var_name.and_then(|name| param_names.get(name).copied())
}

/// Detect params passed to already-declared logic functions at Seq-sorted
/// positions. This catches cases where `infer_seq_like_params` misses a param
/// because it's only used as an argument to another function (no direct Seq
/// method calls). (#1572)
pub(super) fn collect_cross_fn_seq_params(
    expr: &PureExpr,
    param_names: &HashSet<&str>,
    declared_fns: &HashMap<String, FuncDecl>,
    out: &mut HashSet<String>,
) {
    expr.for_each_recursive_with_depth_limit(super::super::MAX_ENCODING_DEPTH, |node| {
        let PureExpr::LogicFnCall { name, args } = node else {
            return;
        };
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        let Some(func_decl) = declared_fns.get(&smt_name) else {
            return;
        };
        let domain = func_decl.domain();
        for (i, arg) in args.iter().enumerate() {
            if let Some(sort) = domain.get(i) {
                if is_seq_family_sort(sort) {
                    if let Some(base) = extract_base_var_name(arg) {
                        if param_names.contains(base) {
                            out.insert(base.to_string());
                        }
                    }
                }
            }
        }
    });
}

// Re-exported for test module (tests/cross_fn_seq.rs uses `Sort` via `super::*`).
#[cfg(test)]
use ay_dpll::api::Sort;

#[cfg(test)]
mod tests;
