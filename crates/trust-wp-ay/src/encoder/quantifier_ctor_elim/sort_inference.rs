// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort inference helpers for quantifier variables.
//!
//! Supports constructor-argument inference plus method-call usage inference for
//! quantifier-bound variables. Both single-variable and batched traversals use
//! depth-bounded recursive walks with binder shadowing.
//!
//! Extracted from `quantifier_ctor_elim.rs` as part of #1988 structural decomposition.

use std::collections::{HashMap, HashSet};

use ay_dpll::api::Sort;
use trust_wp_core::formula::PureExpr;

use super::{
    super::{match_enc::short_constructor_name, AYEncoder, MAX_ENCODING_DEPTH},
    arg_is_qvar_reference,
};
use crate::encoder::sort_context::sort_inference::fmap_sort;

/// Infer a constructor argument field sort for a quantifier variable.
///
/// Walks the expression tree looking for constructor calls where the quantified
/// variable appears as a direct argument. When found and the constructor's
/// datatype is declared, returns the declared field sort at that argument
/// position.
///
/// This handles the "broader sort pre-scanning" for #1752: when the constructor equality
/// elimination doesn't fire (e.g., multi-variable quantifiers, non-standard patterns),
/// the variable still gets the constructor field sort instead of the `Sort::Int` fallback.
pub(crate) fn infer_constructor_arg_sort(
    encoder: &AYEncoder,
    body: &PureExpr,
    qvar: &str,
) -> Option<Sort> {
    infer_constructor_arg_sort_inner(encoder, body, qvar, 0)
}

/// Infer a quantifier variable sort from recognized method-call usage.
///
/// This detects two broad classes of evidence:
/// - Receiver usage, e.g. `s.len()`, `s.push_back(v)`, `m.lookup(k)`
/// - Key/index argument usage, e.g. `seq.get(i)`, `map.lookup(k)`
///
/// Receiver-based evidence is the primary purpose of this pass: it upgrades
/// fallback-`Int` quantifier binders to Seq/FMap sorts when the body uses the
/// variable as a collection receiver. Key/index arguments still resolve to
/// `Sort::Int`, which is mainly useful for consistency with the batch pass.
pub(crate) fn infer_method_call_usage_sort(body: &PureExpr, qvar: &str) -> Option<Sort> {
    infer_method_call_usage_sort_inner(body, qvar, 0)
}

fn infer_method_call_usage_sort_inner(body: &PureExpr, qvar: &str, depth: usize) -> Option<Sort> {
    if depth > MAX_ENCODING_DEPTH {
        return None;
    }
    let next = depth + 1;
    let recurse = |e: &PureExpr| infer_method_call_usage_sort_inner(e, qvar, next);
    let search_slice = |exprs: &[PureExpr]| -> Option<Sort> {
        exprs
            .iter()
            .fold(None, |best, expr| combine_usage_sorts(best, recurse(expr)))
    };

    match body {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let direct = direct_method_call_usage_sort(receiver, method, args, qvar);
            combine_usage_sorts(
                direct,
                combine_usage_sorts(recurse(receiver), search_slice(args)),
            )
        }
        PureExpr::LogicFnCall { args, .. } => search_slice(args),
        PureExpr::BinOp(l, _, r) => combine_usage_sorts(recurse(l), recurse(r)),
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => recurse(inner),
        PureExpr::Closure {
            params,
            body: inner,
        } => {
            if params.iter().any(|(name, _)| name == qvar) {
                None
            } else {
                recurse(inner)
            }
        }
        PureExpr::Forall {
            var, body: inner, ..
        }
        | PureExpr::Exists {
            var, body: inner, ..
        } => {
            if var == qvar {
                None
            } else {
                recurse(inner)
            }
        }
        PureExpr::Ite(a, b, c) => {
            combine_usage_sorts(recurse(a), combine_usage_sorts(recurse(b), recurse(c)))
        }
        PureExpr::Match { scrutinee, arms } => {
            let mut result = recurse(scrutinee);
            for arm in arms {
                if arm.pattern.binds_name(qvar) {
                    continue;
                }
                result = combine_usage_sorts(result, recurse(&arm.body));
            }
            result
        }
        PureExpr::Let { var, value, body } => combine_usage_sorts(
            recurse(value),
            if var == qvar { None } else { recurse(body) },
        ),
        PureExpr::LetAssume {
            assumption: value,
            body,
        }
        | PureExpr::LetObligation {
            obligation: value,
            body,
        } => combine_usage_sorts(recurse(value), recurse(body)),
        PureExpr::Var(..) | PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => None,
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

/// Batch-infer method-call usage sorts for multiple quantifier variables in a
/// single tree walk.
pub(crate) fn infer_method_call_usage_sorts_batch<'a>(
    body: &PureExpr,
    qvars: &[&'a str],
) -> HashMap<&'a str, Sort> {
    let qvar_set: HashSet<&'a str> = qvars.iter().copied().collect();
    let mut result: HashMap<&'a str, Sort> = HashMap::new();
    infer_method_call_usage_sorts_batch_inner(body, &qvar_set, &mut result, 0);
    result
}

fn infer_method_call_usage_sorts_batch_inner<'a>(
    body: &PureExpr,
    qvar_set: &HashSet<&'a str>,
    result: &mut HashMap<&'a str, Sort>,
    depth: usize,
) {
    if qvar_set.is_empty() || depth > MAX_ENCODING_DEPTH {
        return;
    }
    let next = depth + 1;
    let recurse =
        |expr: &PureExpr, visible_qvars: &HashSet<&'a str>, result: &mut HashMap<&'a str, Sort>| {
            infer_method_call_usage_sorts_batch_inner(expr, visible_qvars, result, next);
        };
    let search_slice = |exprs: &[PureExpr],
                        visible_qvars: &HashSet<&'a str>,
                        result: &mut HashMap<&'a str, Sort>| {
        for expr in exprs {
            infer_method_call_usage_sorts_batch_inner(expr, visible_qvars, result, next);
        }
    };

    match body {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            record_direct_method_call_usage_sorts(receiver, method, args, qvar_set, result);
            recurse(receiver, qvar_set, result);
            search_slice(args, qvar_set, result);
        }
        PureExpr::LogicFnCall { args, .. } => search_slice(args, qvar_set, result),
        PureExpr::BinOp(l, _, r) => {
            recurse(l, qvar_set, result);
            recurse(r, qvar_set, result);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => recurse(inner, qvar_set, result),
        PureExpr::Closure {
            params,
            body: inner,
        } => {
            let visible_qvars =
                filter_visible_qvars(qvar_set, |v| !params.iter().any(|(name, _)| name == v));
            recurse(inner, &visible_qvars, result);
        }
        PureExpr::Forall {
            var, body: inner, ..
        }
        | PureExpr::Exists {
            var, body: inner, ..
        } => {
            let visible_qvars = filter_visible_qvars(qvar_set, |v| v != var.as_str());
            recurse(inner, &visible_qvars, result);
        }
        PureExpr::Ite(a, b, c) => {
            recurse(a, qvar_set, result);
            recurse(b, qvar_set, result);
            recurse(c, qvar_set, result);
        }
        PureExpr::Match { scrutinee, arms } => {
            recurse(scrutinee, qvar_set, result);
            for arm in arms {
                let visible_qvars = filter_visible_qvars(qvar_set, |v| !arm.pattern.binds_name(v));
                recurse(&arm.body, &visible_qvars, result);
            }
        }
        PureExpr::Let { var, value, body } => {
            recurse(value, qvar_set, result);
            let visible_qvars = filter_visible_qvars(qvar_set, |v| v != var.as_str());
            recurse(body, &visible_qvars, result);
        }
        PureExpr::LetAssume {
            assumption: value,
            body,
        }
        | PureExpr::LetObligation {
            obligation: value,
            body,
        } => {
            recurse(value, qvar_set, result);
            recurse(body, qvar_set, result);
        }
        PureExpr::Var(..) | PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => {}
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => {}
    }
}

fn direct_method_call_usage_sort(
    receiver: &PureExpr,
    method: &str,
    args: &[PureExpr],
    qvar: &str,
) -> Option<Sort> {
    // For receiver sort inference, only match bare qvar references (not
    // View-wrapped). When the receiver is `View(Var("b"))`, the variable `b`
    // is NOT a Seq — its *view* `b@` is. The existing View/derived-name
    // mechanism handles that case via `{var}_view` sort hints. Matching
    // through View wrappers would incorrectly upgrade `b` from Int to Seq,
    // breaking the view-variable separation (#579).
    let receiver_sort = if is_bare_qvar_reference(receiver, qvar) {
        receiver_method_usage_sort(method, args.len())
    } else {
        None
    };

    // For argument sort inference, use the general reference check (including
    // View wrappers) since View-wrapping an argument doesn't change the
    // expected argument sort (e.g., `seq.get(v@)` still expects Int index).
    let arg_sort = args.iter().enumerate().fold(None, |best, (idx, arg)| {
        let matches = if method == "exchange" && idx == 0 {
            is_bare_qvar_reference(arg, qvar)
        } else {
            arg_is_qvar_reference(arg, qvar)
        };
        if matches {
            combine_usage_sorts(best, method_arg_usage_sort(method, idx, args.len()))
        } else {
            best
        }
    });

    combine_usage_sorts(receiver_sort, arg_sort)
}

fn record_direct_method_call_usage_sorts<'a>(
    receiver: &PureExpr,
    method: &str,
    args: &[PureExpr],
    qvar_set: &HashSet<&'a str>,
    result: &mut HashMap<&'a str, Sort>,
) {
    // Same bare-reference restriction as direct_method_call_usage_sort:
    // View-wrapped receivers must not infer receiver sort (#579).
    if let Some(var_name) = is_bare_any_qvar_reference(receiver, qvar_set) {
        if let Some(sort) = receiver_method_usage_sort(method, args.len()) {
            record_usage_sort(result, var_name, sort);
        }
    }

    for (idx, arg) in args.iter().enumerate() {
        let var_name = if method == "exchange" && idx == 0 {
            is_bare_any_qvar_reference(arg, qvar_set)
        } else {
            arg_is_any_qvar_reference(arg, qvar_set)
        };
        if let Some(var_name) = var_name {
            if let Some(sort) = method_arg_usage_sort(method, idx, args.len()) {
                record_usage_sort(result, var_name, sort);
            }
        }
    }
}

/// Check if expression is a bare qvar reference: `Var("x")`, `Deref(Var("x"))`,
/// `Old(Var("x"))`, `Final(Var("x"))` — but NOT `View(Var("x"))`.
///
/// View-wrapped receivers indicate the variable's *model view* is the
/// collection, not the variable itself. The View/derived-name mechanism
/// handles sort inference for views separately (#579).
fn is_bare_qvar_reference(expr: &PureExpr, qvar: &str) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == qvar,
        PureExpr::Deref(inner) | PureExpr::Old(inner) | PureExpr::Final(inner) => {
            is_bare_qvar_reference(inner, qvar)
        }
        // View is deliberately excluded — see doc comment.
        _ => false,
    }
}

/// Batch version of `is_bare_qvar_reference` — returns the matching variable
/// name from the set, or `None`.
fn is_bare_any_qvar_reference<'a>(expr: &PureExpr, qvars: &HashSet<&'a str>) -> Option<&'a str> {
    match expr {
        PureExpr::Var(name, _) => qvars.get(name.as_str()).copied(),
        PureExpr::Deref(inner) | PureExpr::Old(inner) | PureExpr::Final(inner) => {
            is_bare_any_qvar_reference(inner, qvars)
        }
        // View is deliberately excluded.
        _ => None,
    }
}

fn receiver_method_usage_sort(method: &str, arg_count: usize) -> Option<Sort> {
    // A well-formed exchange takes another sequence and two indices. Do not
    // infer a collection carrier from an invalid call that must be refused.
    if method == "exchange" {
        return (arg_count == 3).then(|| Sort::seq(Sort::Int));
    }
    if matches!(
        method,
        "contains_key" | "lookup" | "insert" | "insert_ghost" | "merge"
    ) {
        Some(fmap_sort())
    } else if matches!(
        method,
        "is_subset" | "is_superset" | "union" | "intersection" | "difference"
    ) {
        Some(Sort::Uninterpreted("FSet".to_string()))
    } else if method == "mapping_get" {
        Some(Sort::Uninterpreted("Mapping".to_string()))
    } else if matches!(
        method,
        "len"
            | "len_logic"
            | "is_empty"
            | "get"
            | "get_mut_ghost"
            | "index"
            | "index_logic"
            | "set"
            | "push_back"
            | "push_back_ghost"
            | "push_front"
            | "push_front_ghost"
            | "pop_front"
            | "pop_front_ghost"
            | "pop_back"
            | "pop_back_ghost"
            | "tail"
            | "concat"
            | "subsequence"
            | "reverse"
            | "sum"
            | "to_owned_seq"
            | "contains"
            | "ext_eq"
            | "sorted"
            | "permutation_of"
            | "split_first_mut"
            | "split_last_mut"
            | "into_inner"
            | "num_of"
    ) {
        Some(Sort::seq(Sort::Int))
    } else {
        None
    }
}

fn method_arg_usage_sort(method: &str, arg_idx: usize, arg_count: usize) -> Option<Sort> {
    if method == "exchange" {
        return match (arg_count, arg_idx) {
            (3, 0) => Some(Sort::seq(Sort::Int)),
            (3, 1 | 2) => Some(Sort::Int),
            _ => None,
        };
    }
    match (method, arg_idx) {
        (
            "get" | "get_mut_ghost" | "index" | "index_logic" | "lookup" | "contains"
            | "contains_key",
            0,
        )
        | ("set", 0 | 1)
        | ("push_back" | "push_back_ghost" | "push_front" | "push_front_ghost", 0)
        | ("subsequence", 0 | 1)
        | ("insert" | "insert_ghost", 0)
        | ("num_of", 0 | 1) => Some(Sort::Int),
        ("union" | "intersection" | "difference" | "is_subset" | "is_superset", 0) => {
            Some(Sort::Uninterpreted("FSet".to_string()))
        }
        // ext_eq/permutation_of: the argument is a Seq (second collection)
        ("ext_eq" | "permutation_of" | "concat", 0) => Some(Sort::seq(Sort::Int)),
        ("merge", 0) => Some(Sort::Uninterpreted("FMap".to_string())),
        _ => None,
    }
}

fn combine_usage_sorts(lhs: Option<Sort>, rhs: Option<Sort>) -> Option<Sort> {
    match (lhs, rhs) {
        (Some(left), Some(right)) => {
            if usage_sort_priority(&right) > usage_sort_priority(&left) {
                Some(right)
            } else {
                Some(left)
            }
        }
        (Some(sort), None) | (None, Some(sort)) => Some(sort),
        (None, None) => None,
    }
}

fn usage_sort_priority(sort: &Sort) -> u8 {
    if *sort == fmap_sort() {
        3
    } else if *sort == Sort::Uninterpreted("FSet".to_string()) {
        2
    } else if *sort == Sort::Uninterpreted("Mapping".to_string()) {
        2
    } else if sort.is_seq() {
        2
    } else if *sort == Sort::Int {
        1
    } else {
        0
    }
}

fn record_usage_sort<'a>(result: &mut HashMap<&'a str, Sort>, var_name: &'a str, sort: Sort) {
    match result.get(var_name) {
        Some(existing) if usage_sort_priority(existing) >= usage_sort_priority(&sort) => {}
        _ => {
            result.insert(var_name, sort);
        }
    }
}

fn filter_visible_qvars<'a>(
    qvar_set: &HashSet<&'a str>,
    mut keep: impl FnMut(&str) -> bool,
) -> HashSet<&'a str> {
    qvar_set.iter().copied().filter(|v| keep(v)).collect()
}

fn infer_constructor_arg_sort_inner(
    encoder: &AYEncoder,
    body: &PureExpr,
    qvar: &str,
    depth: usize,
) -> Option<Sort> {
    if depth > MAX_ENCODING_DEPTH {
        return None;
    }
    let next = depth + 1;
    let search_slice = |exprs: &[PureExpr]| -> Option<Sort> {
        exprs
            .iter()
            .find_map(|e| infer_constructor_arg_sort_inner(encoder, e, qvar, next))
    };
    let recurse = |e: &PureExpr| infer_constructor_arg_sort_inner(encoder, e, qvar, next);

    match body {
        PureExpr::LogicFnCall { name, args } => {
            // Check if qvar appears as a direct constructor argument and return
            // that argument's field sort.
            if let Some(dt) = encoder.constructor_datatype(name) {
                let short_name = short_constructor_name(name);
                if let Some(ctor) = dt.constructors.iter().find(|ctor| ctor.name == short_name) {
                    for (idx, arg) in args.iter().enumerate() {
                        if arg_is_qvar_reference(arg, qvar) {
                            if let Some(field) = ctor.fields.get(idx) {
                                return Some(field.sort.clone());
                            }
                        }
                    }
                }
            }
            search_slice(args)
        }
        PureExpr::BinOp(l, _, r) => recurse(l).or_else(|| recurse(r)),
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => recurse(inner),
        PureExpr::Closure {
            params,
            body: inner,
        } => {
            if params.iter().any(|(name, _)| name == qvar) {
                None
            } else {
                recurse(inner)
            }
        }
        PureExpr::Forall {
            var, body: inner, ..
        }
        | PureExpr::Exists {
            var, body: inner, ..
        } => {
            if var == qvar {
                None
            } else {
                recurse(inner)
            }
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            recurse(receiver).or_else(|| search_slice(args))
        }
        PureExpr::Ite(a, b, c) => recurse(a).or_else(|| recurse(b)).or_else(|| recurse(c)),
        PureExpr::Match { scrutinee, arms } => recurse(scrutinee).or_else(|| {
            arms.iter().find_map(|arm| {
                if arm.pattern.binds_name(qvar) {
                    None
                } else {
                    recurse(&arm.body)
                }
            })
        }),
        PureExpr::Let { var, value, body } => {
            recurse(value).or_else(|| if var == qvar { None } else { recurse(body) })
        }
        PureExpr::LetAssume {
            assumption: value,
            body,
        }
        | PureExpr::LetObligation {
            obligation: value,
            body,
        } => recurse(value).or_else(|| recurse(body)),
        PureExpr::Var(..) | PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => None,
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

/// Batch-infer constructor argument sorts for multiple quantifier variables
/// in a single tree walk. Returns a map from variable name to inferred sort.
///
/// This avoids the O(V*T) cost of calling `infer_constructor_arg_sort` once
/// per variable, reducing it to O(T + V) for V variables over a tree of size T.
/// Part of #2346 (quadratic scaling patterns in quantifier encoding).
pub(crate) fn infer_constructor_arg_sorts_batch<'a>(
    encoder: &AYEncoder,
    body: &PureExpr,
    qvars: &[&'a str],
) -> HashMap<&'a str, Sort> {
    let qvar_set: HashSet<&'a str> = qvars.iter().copied().collect();
    let mut result: HashMap<&'a str, Sort> = HashMap::new();
    infer_constructor_arg_sorts_batch_inner(encoder, body, &qvar_set, &mut result, qvars.len(), 0);
    result
}

#[allow(clippy::too_many_lines)] // Deep pattern-matching traversal over constructor arguments
fn infer_constructor_arg_sorts_batch_inner<'a>(
    encoder: &AYEncoder,
    body: &PureExpr,
    qvar_set: &HashSet<&'a str>,
    result: &mut HashMap<&'a str, Sort>,
    total_vars: usize,
    depth: usize,
) {
    // Early exit: all variables resolved or depth exceeded.
    if result.len() == total_vars || depth > MAX_ENCODING_DEPTH {
        return;
    }
    let next = depth + 1;
    let recurse = |e: &PureExpr, result: &mut HashMap<&'a str, Sort>| {
        infer_constructor_arg_sorts_batch_inner(encoder, e, qvar_set, result, total_vars, next);
    };
    let search_slice = |exprs: &[PureExpr], result: &mut HashMap<&'a str, Sort>| {
        for e in exprs {
            if result.len() == total_vars {
                break;
            }
            infer_constructor_arg_sorts_batch_inner(encoder, e, qvar_set, result, total_vars, next);
        }
    };

    match body {
        PureExpr::LogicFnCall { name, args } => {
            // Check if any qvar appears as a direct constructor argument.
            if let Some(dt) = encoder.constructor_datatype(name) {
                let short_name = short_constructor_name(name);
                if let Some(ctor) = dt.constructors.iter().find(|ctor| ctor.name == short_name) {
                    for (idx, arg) in args.iter().enumerate() {
                        if let Some(var_name) = arg_is_any_qvar_reference(arg, qvar_set) {
                            if !result.contains_key(var_name) {
                                if let Some(field) = ctor.fields.get(idx) {
                                    result.insert(var_name, field.sort.clone());
                                }
                            }
                        }
                    }
                }
            }
            search_slice(args, result);
        }
        PureExpr::BinOp(l, _, r) => {
            recurse(l, result);
            recurse(r, result);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => recurse(inner, result),
        PureExpr::Closure {
            params,
            body: inner,
        } => {
            // If ALL unresolved qvars are shadowed, skip. Otherwise recurse.
            let all_unresolved_shadowed = qvar_set
                .iter()
                .all(|&v| result.contains_key(v) || params.iter().any(|(name, _)| name == v));
            if !all_unresolved_shadowed {
                recurse(inner, result);
            }
        }
        PureExpr::Forall {
            var, body: inner, ..
        }
        | PureExpr::Exists {
            var, body: inner, ..
        } => {
            // Skip only if all unresolved qvars are this shadowed var.
            let all_unresolved_shadowed = qvar_set
                .iter()
                .all(|&v| result.contains_key(v) || v == var.as_str());
            if !all_unresolved_shadowed {
                recurse(inner, result);
            }
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            recurse(receiver, result);
            search_slice(args, result);
        }
        PureExpr::Ite(a, b, c) => {
            recurse(a, result);
            recurse(b, result);
            recurse(c, result);
        }
        PureExpr::Match { scrutinee, arms } => {
            recurse(scrutinee, result);
            for arm in arms {
                if result.len() == total_vars {
                    break;
                }
                recurse(&arm.body, result);
            }
        }
        PureExpr::Let { var, value, body } => {
            recurse(value, result);
            let all_unresolved_shadowed = qvar_set
                .iter()
                .all(|&v| result.contains_key(v) || v == var.as_str());
            if !all_unresolved_shadowed {
                recurse(body, result);
            }
        }
        PureExpr::LetAssume {
            assumption: value,
            body,
        }
        | PureExpr::LetObligation {
            obligation: value,
            body,
        } => {
            recurse(value, result);
            recurse(body, result);
        }
        PureExpr::Var(..) | PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => {}
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => {}
    }
}

/// Check if an expression is a reference to any of the given quantifier variables.
/// Returns the matching variable name if found.
pub(crate) fn arg_is_any_qvar_reference<'a>(
    expr: &PureExpr,
    qvars: &HashSet<&'a str>,
) -> Option<&'a str> {
    match expr {
        PureExpr::Var(name, _) => qvars.get(name.as_str()).copied(),
        PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => arg_is_any_qvar_reference(inner, qvars),
        _ => None,
    }
}
