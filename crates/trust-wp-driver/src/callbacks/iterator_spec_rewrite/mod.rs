// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Iterator `produces`/`completed` rewriting for supported iterator types.
//!
//! Supported families include:
//! - `Vec::IntoIter`
//! - `HashMap::{IntoIter, Iter, IterMut}`
//! - `slice::IterMut` (snapshot-aware, #2238)
//! - `Range`
//! - `Empty`, `Once`, `Repeat`, `Fuse`, `Cloned`, `Copied`
//! - `Rev`, `Skip`, `Take`, `Enumerate`, `Zip`, `Chain`, `Peekable`
//! - `Map`, `Filter`, `FilterMap`, `MapInv` (completed only; produces deferred)
//!
//! Representative rewrites:
//! - `receiver.produces(visited, next)` → `receiver@.ext_eq(visited.concat(next@))`
//! - `receiver.completed()` → `receiver@.len() == 0`
//!
//! This gives the solver content-equality semantics instead of length-only,
//! enabling proofs about element identity and ordering through iterator chains
//! while letting collection iterators stay on their existing `FMap` view model.

mod collections;
mod composite;
pub(crate) mod helpers;
mod range;
mod simple;

use std::{collections::HashMap, sync::Arc};

use collections::try_rewrite_collection_iter_method;
use composite::try_rewrite_composite_iter_method;
use range::try_rewrite_range_method;
use simple::try_rewrite_iter_method;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::parsing::ParsedContract;

/// Recursively rewrite `produces` and `completed` method calls on supported
/// iterator types to their Seq-based equivalents.
fn rewrite_expr(expr: &PureExpr) -> PureExpr {
    rewrite_expr_with_scope(expr, &HashMap::new())
}

fn rewrite_expr_with_scope(expr: &PureExpr, bound_sorts: &HashMap<String, ExprSort>) -> PureExpr {
    if let PureExpr::Var(name, None) = expr {
        if let Some(sort) = bound_sorts.get(name) {
            return PureExpr::Var(name.clone(), Some(sort.clone()));
        }
    }

    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    {
        let receiver = rewrite_expr_with_scope(receiver, bound_sorts);
        let args: Vec<PureExpr> = args
            .iter()
            .map(|arg| rewrite_expr_with_scope(arg, bound_sorts))
            .collect();
        if let Some(rewritten) = try_rewrite_iter_method(&receiver, method, &args) {
            return rewritten;
        }
        if let Some(rewritten) = try_rewrite_composite_iter_method(&receiver, method, &args) {
            return rewritten;
        }
        if let Some(rewritten) = try_rewrite_collection_iter_method(&receiver, method, &args) {
            return rewritten;
        }
        if let Some(rewritten) = try_rewrite_range_method(&receiver, method, &args) {
            return rewritten;
        }
        return PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: method.clone(),
            args,
        };
    }
    descend_children(expr, bound_sorts)
}

/// Rewrite trigger lists through `rewrite_expr`.
fn rewrite_triggers(
    triggers: &[Vec<PureExpr>],
    bound_sorts: &HashMap<String, ExprSort>,
) -> Vec<Vec<PureExpr>> {
    triggers
        .iter()
        .map(|trig| {
            trig.iter()
                .map(|expr| rewrite_expr_with_scope(expr, bound_sorts))
                .collect()
        })
        .collect()
}

/// Apply `rewrite_expr` recursively to all child expressions.
fn descend_children(expr: &PureExpr, bound_sorts: &HashMap<String, ExprSort>) -> PureExpr {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(rewrite_expr_with_scope(receiver, bound_sorts)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_expr_with_scope(arg, bound_sorts))
                .collect(),
        },
        PureExpr::BinOp(l, op, r) => PureExpr::BinOp(
            Arc::new(rewrite_expr_with_scope(l, bound_sorts)),
            *op,
            Arc::new(rewrite_expr_with_scope(r, bound_sorts)),
        ),
        PureExpr::UnOp(op, inner) => {
            PureExpr::UnOp(*op, Arc::new(rewrite_expr_with_scope(inner, bound_sorts)))
        }
        PureExpr::Ite(c, t, e) => PureExpr::Ite(
            Arc::new(rewrite_expr_with_scope(c, bound_sorts)),
            Arc::new(rewrite_expr_with_scope(t, bound_sorts)),
            Arc::new(rewrite_expr_with_scope(e, bound_sorts)),
        ),
        PureExpr::Old(inner) => {
            PureExpr::Old(Arc::new(rewrite_expr_with_scope(inner, bound_sorts)))
        }
        PureExpr::Deref(inner) => {
            PureExpr::Deref(Arc::new(rewrite_expr_with_scope(inner, bound_sorts)))
        }
        PureExpr::Final(inner) => {
            PureExpr::Final(Arc::new(rewrite_expr_with_scope(inner, bound_sorts)))
        }
        PureExpr::View(inner) => {
            PureExpr::View(Arc::new(rewrite_expr_with_scope(inner, bound_sorts)))
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let mut nested_sorts = bound_sorts.clone();
            if let Some(sort) = var_sort {
                nested_sorts.insert(var.clone(), sort.clone());
            } else {
                nested_sorts.remove(var);
            }
            PureExpr::Forall {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(rewrite_expr_with_scope(body, &nested_sorts)),
                triggers: rewrite_triggers(triggers, &nested_sorts),
            }
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let mut nested_sorts = bound_sorts.clone();
            if let Some(sort) = var_sort {
                nested_sorts.insert(var.clone(), sort.clone());
            } else {
                nested_sorts.remove(var);
            }
            PureExpr::Exists {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(rewrite_expr_with_scope(body, &nested_sorts)),
                triggers: rewrite_triggers(triggers, &nested_sorts),
            }
        }
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_expr_with_scope(arg, bound_sorts))
                .collect(),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(rewrite_expr_with_scope(scrutinee, bound_sorts)),
            arms: arms
                .iter()
                .map(|arm| trust_wp_core::formula::MatchArm {
                    pattern: arm.pattern.clone(),
                    body: rewrite_expr_with_scope(&arm.body, bound_sorts),
                })
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(rewrite_expr_with_scope(value, bound_sorts)),
            body: Arc::new(rewrite_expr_with_scope(body, bound_sorts)),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(rewrite_expr_with_scope(assumption, bound_sorts)),
            body: Arc::new(rewrite_expr_with_scope(body, bound_sorts)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(rewrite_expr_with_scope(obligation, bound_sorts)),
            body: Arc::new(rewrite_expr_with_scope(body, bound_sorts)),
        },
        PureExpr::Closure { params, body } => PureExpr::Closure {
            params: params.clone(),
            body: Arc::new(rewrite_expr_with_scope(body, bound_sorts)),
        },
        _ => expr.clone(), // PureExpr is #[non_exhaustive]; covers Bool, Int, Var
    }
}

/// Rewrite iterator spec method calls in a single expression (#2171).
///
/// Expression-level entry point for rewriting synthesized invariants that
/// bypass `ParsedContract` (e.g., auto-injected structural invariants from
/// `loop_verify`). Same transform as `rewrite_iterator_spec_methods` but
/// operates on a single `PureExpr` instead of a full `ParsedContract`.
pub(super) fn rewrite_iterator_spec_expr(expr: &PureExpr) -> PureExpr {
    rewrite_expr(expr)
}

/// Rewrite all iterator spec method calls in a parsed contract.
///
/// Must be called after `rewrite_parsed_contract_structure` (which resolves
/// logic method calls) and before SMT emission.
pub(super) fn rewrite_iterator_spec_methods(parsed: &mut ParsedContract) {
    parsed.rewrite_all_exprs(rewrite_expr);
}

#[cfg(test)]
mod tests;
