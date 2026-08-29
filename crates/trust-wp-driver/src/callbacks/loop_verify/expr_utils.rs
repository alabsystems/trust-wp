// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expression analysis utilities for loop verification.
//! Provides variable reference tracking and expression variable collection.

use trust_wp_core::formula::PureExpr;

/// Check if an expression tree references a variable by name.
pub(in crate::callbacks) fn expr_references_var(expr: &PureExpr, name: &str) -> bool {
    expr.any_free_var(|var_name, _| var_name == name)
}

/// Collect all free variable names referenced in an expression.
///
/// Delegates to `PureExpr::for_each_free_var` for exhaustive binder-aware
/// traversal — quantifier-bound variables, let bindings, match pattern
/// bindings, and closure parameters are excluded. (#2654)
pub(in crate::callbacks) fn collect_expr_vars(
    expr: &PureExpr,
    out: &mut std::collections::HashSet<String>,
) {
    expr.for_each_free_var(|name, _sort| {
        out.insert(name.to_string());
    });
}

pub(in crate::callbacks) fn expr_referenced_vars(
    expr: &PureExpr,
) -> std::collections::HashSet<String> {
    let mut vars = std::collections::HashSet::new();
    collect_expr_vars(expr, &mut vars);
    vars
}
