// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Seq pre-scan helpers (free functions).
//!
//! PureExpr walkers that identify variables needing Seq sort from their
//! usage context. No `AYEncoder` state — these are pure expression analysis.
//!
//! - `normalize_seq_receiver_for_scan` — wraps non-Seq receivers in `View(…)`
//! - `expr_produces_seq` — predicate: does this expression produce Seq?
//! - `collect_view_names_as_seq` — collect variable names that should be Seq-sorted

use std::{borrow::Cow, collections::HashSet, sync::Arc};

use trust_wp_core::formula::PureExpr;

use super::classification::method_produces_seq;
use crate::encoder::sort_context::resolve_view_var_name;

fn is_static_seq_empty_method(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall { receiver, method, args }
            if method == "empty"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "Seq")
    )
}

fn is_static_seq_singleton_method(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall { receiver, method, args }
            if method == "singleton"
                && args.len() == 1
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "Seq")
    )
}

/// Normalize a Seq method receiver — single source of truth.
///
/// Used by both the pre-scan path and `AYEncoder::normalize_seq_receiver` (which
/// delegates here). Wraps non-Seq receivers in `View(...)` so that downstream
/// encoding operates on the logical view.
pub(crate) fn normalize_seq_receiver_for_scan(receiver: &PureExpr) -> Cow<'_, PureExpr> {
    match receiver {
        PureExpr::View(_) => Cow::Borrowed(receiver),
        // Preserve wrapped Seq-producing receivers like `Final(seq_empty())`:
        // wrapping them again in `View(...)` forces the `view` placeholder path,
        // which collapses the Seq carrier to Int and later requires the
        // unsound Int→Seq bridge in `encode_seq_operation_impl`. (#994)
        _ if expr_produces_seq(receiver) => Cow::Borrowed(receiver),
        PureExpr::Old(inner)
            if matches!(inner.as_ref(), PureExpr::View(_))
                || matches!(inner.as_ref(), PureExpr::MethodCall { method, .. } if method_produces_seq(method)) =>
        {
            Cow::Borrowed(receiver)
        }
        _ => Cow::Owned(PureExpr::View(Arc::new(receiver.clone()))),
    }
}

/// Returns true if the expression produces a Seq-sorted result (e.g., `push_back`).
pub(crate) fn expr_produces_seq(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::MethodCall { method, .. } if method_produces_seq(method) => true,
        PureExpr::MethodCall { method, .. } if method == "into_seq" => true,
        PureExpr::MethodCall { .. } if is_static_seq_empty_method(expr) => true,
        PureExpr::MethodCall { .. } if is_static_seq_singleton_method(expr) => true,
        // Sequence constructor built-ins:
        // - seq![...]
        // - Seq::singleton(v)
        // - Seq::empty() / seq_empty()
        PureExpr::LogicFnCall { name, .. }
            if matches!(
                name.as_str(),
                "seq" | "Seq::singleton" | "seq_empty" | "Seq::empty"
            ) =>
        {
            true
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_produces_seq(inner),
        // Propagate through branches: if any branch produces Seq, the Ite/Match does too.
        PureExpr::Ite(_, then_br, else_br) => {
            expr_produces_seq(then_br) || expr_produces_seq(else_br)
        }
        PureExpr::Match { arms, .. } => arms.iter().any(|arm| expr_produces_seq(&arm.body)),
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => expr_produces_seq(body),
        _ => false,
    }
}

/// Collect all variable names from an expression that should be Seq-sorted.
/// Used for equality propagation: `var == seq_expr` means the var must be Seq.
/// Handles both View-wrapped vars (`View(Var("x"))` → `"x_view"`) and bare
/// vars (`Var("result")` → `"result"`), plus wrappers (Old, Deref) and
/// branches (Ite).
pub(crate) fn collect_view_names_as_seq(expr: &PureExpr, names: &mut HashSet<String>) {
    collect_view_names_as_seq_inner(expr, names, false);
}

/// Inner helper with `inside_view` flag to prevent over-tagging base variables.
///
/// When recursing through wrappers (Final, Deref) inside a View, the bare
/// Var at the bottom should NOT be tagged as Seq — only the View-resolved
/// name carries the Seq hint. The propagation chain in `register_sort_hints`
/// handles derived names (e.g., `"x_view"` → `"x"`) when appropriate. (#2057)
fn collect_view_names_as_seq_inner(
    expr: &PureExpr,
    names: &mut HashSet<String>,
    inside_view: bool,
) {
    if let Some(name) = resolve_view_var_name(expr, None) {
        names.insert(name);
    }
    // Also propagate Seq sort hint to bare Vars (#1581).
    // Ghost code invariants like `result == produced.reverse()` use bare Var
    // on one side and a Seq-producing expression on the other. Without this,
    // the bare Var defaults to Int, causing sort mismatch at encoding time.
    //
    // Skip when inside a View wrapper — the base variable of
    // View(Final(Deref(Var("x")))) should NOT be tagged as Seq directly.
    // The view-resolved name (e.g., "final_x_current_view") already carries
    // the hint, and the propagation chain handles derived names. (#2057)
    if !inside_view {
        if let PureExpr::Var(name, _) = expr {
            names.insert(name.clone());
        }
    }
    match expr {
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            collect_view_names_as_seq_inner(inner, names, inside_view);
        }
        PureExpr::View(inner) => {
            // Entering a View wrapper — set flag to prevent bare-Var collection
            // in descendant non-View wrappers (Final, Deref).
            collect_view_names_as_seq_inner(inner, names, true);
        }
        PureExpr::Ite(_, then_expr, else_expr) => {
            collect_view_names_as_seq_inner(then_expr, names, inside_view);
            collect_view_names_as_seq_inner(else_expr, names, inside_view);
        }
        // Match arms inherit Seq context from the enclosing expression
        PureExpr::Match { arms, .. } => {
            for arm in arms {
                collect_view_names_as_seq_inner(&arm.body, names, inside_view);
            }
        }
        // Let/LetAssume/LetObligation body inherits Seq context from the enclosing expression
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => {
            collect_view_names_as_seq_inner(body, names, inside_view);
        }
        _ => {}
    }
}

/// Recursively collect View variable names that appear in Seq contexts.
///
/// A View is "in Seq context" when:
/// 1. It is the receiver (after normalization) of a Seq method call, or
/// 2. It appears in an equality with a Seq-producing expression (type propagation).
///
/// The production code path uses [`sort_context::collect_all_sort_hints`] which
/// inlines this logic for a single-pass traversal. This standalone function is
/// retained for unit tests that verify Seq detection in isolation.
#[cfg(test)]
#[allow(clippy::too_many_lines)]
pub(crate) fn collect_seq_view_names(expr: &PureExpr, names: &mut HashSet<String>) {
    use trust_wp_core::formula::BinOp;

    use super::classification::is_seq_only_method;

    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let seq_only = is_seq_only_method(method);
            let is_ambiguous_seq_method = matches!(method.as_str(), "len" | "len_ghost" | "index" | "index_logic" | "get" | "get_ghost" | "get_mut_ghost" | "set")
                    // Keep test helper behavior aligned with production prescan
                    // (#756, #967): bare vars should not be auto-marked as Seq.
                    && !matches!(receiver.as_ref(), PureExpr::Var(_, _));
            if seq_only || is_ambiguous_seq_method {
                let normalized = normalize_seq_receiver_for_scan(receiver);
                if let Some(name) = resolve_view_var_name(normalized.as_ref(), None) {
                    names.insert(name);
                }
            }
            if method == "ext_eq" {
                let receiver_is_view = resolve_view_var_name(receiver, None).is_some();
                if let Some(name) = resolve_view_var_name(receiver, None) {
                    names.insert(name);
                }
                for arg in args {
                    if let Some(name) = resolve_view_var_name(arg, None) {
                        names.insert(name);
                    }
                }
                // ext_eq on a view-shaped receiver implies Seq context for the
                // counterpart operand, even when that operand is nested
                // (e.g., if-then-else over views). (#962)
                if receiver_is_view || expr_produces_seq(receiver) {
                    for arg in args {
                        collect_view_names_as_seq(arg, names);
                    }
                }
                for arg in args {
                    let arg_is_view = resolve_view_var_name(arg, None).is_some();
                    if arg_is_view || expr_produces_seq(arg) {
                        collect_view_names_as_seq(receiver, names);
                    }
                }
            }
            collect_seq_view_names(receiver, names);
            for arg in args {
                collect_seq_view_names(arg, names);
            }
        }
        PureExpr::BinOp(l, op, r) => {
            // Equality propagation: if one side produces Seq, the other side's
            // View variables must also be Seq.
            if matches!(op, BinOp::Eq | BinOp::Ne) {
                if expr_produces_seq(l) {
                    collect_view_names_as_seq(r, names);
                }
                if expr_produces_seq(r) {
                    collect_view_names_as_seq(l, names);
                }
            }
            collect_seq_view_names(l, names);
            collect_seq_view_names(r, names);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            collect_seq_view_names(inner, names);
        }
        PureExpr::Ite(c, t, e) => {
            collect_seq_view_names(c, names);
            collect_seq_view_names(t, names);
            collect_seq_view_names(e, names);
        }
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
            collect_seq_view_names(body, names);
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                collect_seq_view_names(arg, names);
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_seq_view_names(scrutinee, names);
            for arm in arms {
                collect_seq_view_names(&arm.body, names);
            }
        }
        PureExpr::Let { value, body, .. } => {
            collect_seq_view_names(value, names);
            collect_seq_view_names(body, names);
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_seq_view_names(assumption, names);
            collect_seq_view_names(body, names);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_seq_view_names(obligation, names);
            collect_seq_view_names(body, names);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests;
