// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use ay_dpll::api::Sort;
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

use super::super::sort_inference::{infer_expr_sort_cached, InferExprSortCache};
use crate::encoder::unsoundness::{self, UnsoundnessCategory};

pub(crate) fn collect_bool_hints(
    expr: &PureExpr,
    var_names: &mut HashSet<String>,
    fn_names: &mut HashSet<String>,
) {
    // Suppress SortFallbackToIntFromLogicFn: hint collection is Tier 3, encoding is Tier 1. (#2062)
    let before = unsoundness::snapshot();
    collect_bool_hints_cached(
        expr,
        var_names,
        fn_names,
        &mut InferExprSortCache::default(),
    );
    unsoundness::restore_category(&before, UnsoundnessCategory::SortFallbackToIntFromLogicFn);
}

fn collect_bool_hints_cached(
    expr: &PureExpr,
    var_names: &mut HashSet<String>,
    fn_names: &mut HashSet<String>,
    sort_cache: &mut InferExprSortCache,
) {
    match expr {
        PureExpr::UnOp(UnOp::Not, inner) => {
            collect_names_as_bool(inner, var_names, fn_names);
            collect_bool_hints_cached(inner, var_names, fn_names, sort_cache);
        }
        PureExpr::BinOp(l, op, r) => {
            match op {
                BinOp::And | BinOp::Or | BinOp::Implies => {
                    collect_names_as_bool(l, var_names, fn_names);
                    collect_names_as_bool(r, var_names, fn_names);
                }
                BinOp::Eq | BinOp::Ne => {
                    if infer_expr_sort_cached(l, sort_cache) == Sort::Bool {
                        collect_names_as_bool(r, var_names, fn_names);
                    }
                    if infer_expr_sort_cached(r, sort_cache) == Sort::Bool {
                        collect_names_as_bool(l, var_names, fn_names);
                    }
                }
                _ => {}
            }
            collect_bool_hints_cached(l, var_names, fn_names, sort_cache);
            collect_bool_hints_cached(r, var_names, fn_names, sort_cache);
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_names_as_bool(cond, var_names, fn_names);
            collect_bool_hints_cached(cond, var_names, fn_names, sort_cache);
            if infer_expr_sort_cached(then_expr, sort_cache) == Sort::Bool {
                collect_names_as_bool(else_expr, var_names, fn_names);
            }
            if infer_expr_sort_cached(else_expr, sort_cache) == Sort::Bool {
                collect_names_as_bool(then_expr, var_names, fn_names);
            }
            collect_bool_hints_cached(then_expr, var_names, fn_names, sort_cache);
            collect_bool_hints_cached(else_expr, var_names, fn_names, sort_cache);
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner)
        | PureExpr::UnOp(_, inner) => {
            collect_bool_hints_cached(inner, var_names, fn_names, sort_cache);
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            collect_bool_hints_cached(receiver, var_names, fn_names, sort_cache);
            for arg in args {
                collect_bool_hints_cached(arg, var_names, fn_names, sort_cache);
            }
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                collect_bool_hints_cached(arg, var_names, fn_names, sort_cache);
            }
        }
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
            collect_bool_hints_cached(body, var_names, fn_names, sort_cache);
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_bool_hints_cached(scrutinee, var_names, fn_names, sort_cache);
            for arm in arms {
                collect_bool_hints_cached(&arm.body, var_names, fn_names, sort_cache);
            }
        }
        PureExpr::Let { value, body, .. } => {
            collect_bool_hints_cached(value, var_names, fn_names, sort_cache);
            collect_bool_hints_cached(body, var_names, fn_names, sort_cache);
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_bool_hints_cached(assumption, var_names, fn_names, sort_cache);
            collect_bool_hints_cached(body, var_names, fn_names, sort_cache);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_bool_hints_cached(obligation, var_names, fn_names, sort_cache);
            collect_bool_hints_cached(body, var_names, fn_names, sort_cache);
        }
        _ => {}
    }
}

pub(in crate::encoder) fn collect_names_as_bool(
    expr: &PureExpr,
    var_names: &mut HashSet<String>,
    fn_names: &mut HashSet<String>,
) {
    match expr {
        PureExpr::Var(name, _) => {
            var_names.insert(name.clone());
        }
        PureExpr::MethodCall {
            receiver, method, ..
        } => {
            // Formula-position method calls (for example bare `x.index_logic(k)`
            // assumptions) need Bool-returning UF fallback when sort inference
            // cannot recover a concrete collection model. Record the method
            // name so the method-call encoder can honor the formula context.
            // Qualify with receiver name to prevent cross-receiver sort hint
            // pollution when multiple closures/mappings use the same method
            // name with different return sorts (#2245).
            fn_names.insert(receiver_qualified_method_hint_key(receiver, method));
        }
        PureExpr::LogicFnCall { name, .. } => {
            fn_names.insert(trust_wp_core::logic::logic_fn_smt_name(name));
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            collect_names_as_bool(inner, var_names, fn_names);
        }
        PureExpr::Ite(_, then_expr, else_expr) => {
            collect_names_as_bool(then_expr, var_names, fn_names);
            collect_names_as_bool(else_expr, var_names, fn_names);
        }
        PureExpr::Match { arms, .. } => {
            for arm in arms {
                collect_names_as_bool(&arm.body, var_names, fn_names);
            }
        }
        PureExpr::Let { body, .. } => {
            collect_names_as_bool(body, var_names, fn_names);
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_names_as_bool(assumption, var_names, fn_names);
            collect_names_as_bool(body, var_names, fn_names);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_names_as_bool(obligation, var_names, fn_names);
            collect_names_as_bool(body, var_names, fn_names);
        }
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
            collect_names_as_bool(body, var_names, fn_names);
        }
        _ => {}
    }
}

/// Build a receiver-qualified sort hint key for a method call.
///
/// When the receiver is a simple `Var`, produces `"{receiver_name}.{method}"`.
/// Otherwise falls back to the bare method name. This prevents a Bool sort hint
/// registered for one mapping's `.get()` from poisoning a different mapping's
/// `.get()` with a different return sort. (#2245)
pub(in crate::encoder) fn receiver_qualified_method_hint_key(
    receiver: &PureExpr,
    method: &str,
) -> String {
    match receiver {
        PureExpr::Var(recv_name, _) => format!("{recv_name}.{method}"),
        PureExpr::Deref(inner) | PureExpr::Old(inner) | PureExpr::View(inner) => {
            receiver_qualified_method_hint_key(inner, method)
        }
        _ => method.to_string(),
    }
}
