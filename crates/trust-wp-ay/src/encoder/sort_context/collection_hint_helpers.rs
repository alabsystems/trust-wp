// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use trust_wp_core::formula::PureExpr;

use super::resolve_view_var_name;

pub(super) fn collect_names_as_mapping(expr: &PureExpr, names: &mut HashSet<String>) {
    collect_names_as_mapping_inner(expr, names, false);
}

fn collect_names_as_mapping_inner(expr: &PureExpr, names: &mut HashSet<String>, inside_view: bool) {
    if let Some(name) = resolve_view_var_name(expr, None) {
        names.insert(name);
    }
    if !inside_view {
        if let PureExpr::Var(name, _) = expr {
            names.insert(name.clone());
        }
    }
    match expr {
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            collect_names_as_mapping_inner(inner, names, inside_view);
        }
        PureExpr::View(inner) => {
            collect_names_as_mapping_inner(inner, names, true);
        }
        PureExpr::Ite(_, then_expr, else_expr) => {
            collect_names_as_mapping_inner(then_expr, names, inside_view);
            collect_names_as_mapping_inner(else_expr, names, inside_view);
        }
        PureExpr::Match { arms, .. } => {
            for arm in arms {
                collect_names_as_mapping_inner(&arm.body, names, inside_view);
            }
        }
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => {
            collect_names_as_mapping_inner(body, names, inside_view);
        }
        _ => {}
    }
}

/// Check if a method name is exclusively used by FMap (not shared with Seq/FSet).
///
/// Note: `insert`/`insert_ghost` are excluded because they're ambiguous by
/// arity — 2-arg insert is FMap, 1-arg insert is FSet. Callers handle the
/// arity check separately.
pub(super) fn is_fmap_only_method(method: &str) -> bool {
    matches!(method, "lookup" | "merge")
}
