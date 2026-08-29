// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Focus-variable analysis for ghost block assumption filtering.
//!
//! Determines which variables are "in focus" (mentioned in requires/ensures/body)
//! and filters ghost assumptions to retain only those connected to the focus set.

use std::collections::HashSet;

use trust_wp_core::formula::{BinOp, PureExpr};

pub(super) fn collect_expr_var_names(expr: &PureExpr, out: &mut HashSet<String>) {
    expr.for_each_recursive(|node| {
        if let PureExpr::Var(name, _) = node {
            out.insert(name.clone());
        }
    });
}

pub(in crate::callbacks) fn collect_focus_var_names(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
) -> HashSet<String> {
    let mut vars = HashSet::new();
    for req in requires {
        collect_expr_var_names(req, &mut vars);
    }
    for ens in ensures {
        collect_expr_var_names(ens, &mut vars);
    }
    if let Some(body) = return_expr {
        collect_expr_var_names(body, &mut vars);
    }
    vars
}

pub(in crate::callbacks) fn assumption_targets_focus_vars(
    assumption: &PureExpr,
    focus_vars: &HashSet<String>,
) -> bool {
    if focus_vars.is_empty() {
        return false;
    }

    fn lhs_targets_focus(lhs: &PureExpr, focus_vars: &HashSet<String>) -> bool {
        match lhs {
            PureExpr::Var(name, _) => focus_vars.contains(name),
            PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner)
            | PureExpr::Old(inner) => lhs_targets_focus(inner, focus_vars),
            // For complex LHS expressions (MethodCall, LogicFnCall, BinOp, etc.),
            // fall back to checking if any focus variable appears anywhere in the
            // expression. Returning false would silently drop the assumption. (#1711)
            _ => expr_references_focus_vars(lhs, focus_vars),
        }
    }

    match assumption {
        // Keep equality assumptions when either side targets focus variables.
        // This preserves alias chains like `tmp == focus` in addition to
        // direct assignments `focus == value`. (#1581)
        PureExpr::BinOp(lhs, BinOp::Eq, rhs) => {
            lhs_targets_focus(lhs, focus_vars) || lhs_targets_focus(rhs, focus_vars)
        }
        // For non-equality assumptions (And, Implies, Forall, etc.), check if any
        // focus variable appears anywhere. Returning false would silently drop
        // assumptions that may be needed for soundness. (#1711)
        _ => expr_references_focus_vars(assumption, focus_vars),
    }
}

/// Keep assumptions connected to the focus set through transitive equalities.
///
/// Example:
/// - focus: `{p1, p2}`
/// - assumptions: `own1 == p1`, `own2 == p2`, `own1 != own2`
///
/// A one-pass filter drops `own1 != own2` because it does not directly mention
/// `p1`/`p2`. This pass grows the focus set through selected assumptions so the
/// third fact is retained. (#1581)
pub(in crate::callbacks) fn select_focus_connected_assumptions(
    assumptions: &[PureExpr],
    focus_vars: &HashSet<String>,
) -> Vec<PureExpr> {
    if assumptions.is_empty() || focus_vars.is_empty() {
        return Vec::new();
    }

    let mut expanded_focus = focus_vars.clone();
    let mut selected = vec![false; assumptions.len()];

    loop {
        let mut changed = false;
        for (idx, assumption) in assumptions.iter().enumerate() {
            if selected[idx] || !assumption_targets_focus_vars(assumption, &expanded_focus) {
                continue;
            }
            selected[idx] = true;
            // Expand transitive reachability only through equalities to avoid
            // over-linking unrelated assumptions that share quantified locals.
            if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = assumption {
                collect_expr_var_names(lhs, &mut expanded_focus);
                collect_expr_var_names(rhs, &mut expanded_focus);
            }
            changed = true;
        }
        if !changed {
            break;
        }
    }

    assumptions
        .iter()
        .zip(selected)
        .filter_map(|(assumption, keep)| keep.then_some(assumption.clone()))
        .collect()
}

/// Check whether a `PureExpr` references any variable in the focus set.
///
/// Used to filter ghost block call assumptions: only inject assumptions that
/// mention variables appearing in the proof_assert or contract being verified.
pub(in crate::callbacks) fn expr_references_focus_vars(
    expr: &PureExpr,
    focus_vars: &HashSet<String>,
) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Var(name, _) if focus_vars.contains(name)))
}
