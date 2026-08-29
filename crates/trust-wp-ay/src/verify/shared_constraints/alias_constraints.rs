// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared alias-constraint helpers and result sort inference.
//!
//! Originally part of `shared_constraints.rs`. Extracted as part of #1988.

use ay_dpll::api::Sort;
use tracing::debug;
use trust_wp_core::formula::PureExpr;

use crate::{encoder::sort_context::DerivedKind, error::EncodingError};

/// Resolve the declaration sort to use for the synthetic `result` variable.
///
/// `infer_expr_sort` is intentionally conservative for variables and defaults
/// many forms to `Sort::Int` (including `Var(_, Some(ExprSort::Seq))`), which
/// can under-approximate the real SMT sort. For bare variables, prefer explicit
/// ExprSort annotations or an already-declared encoder sort before falling back
/// to syntactic sort inference.
pub(in crate::verify) fn infer_result_sort(
    encoder: &mut crate::encoder::AYEncoder,
    expr: &PureExpr,
) -> Sort {
    if let PureExpr::Var(_, Some(sort)) = expr {
        encoder.sort_from_expr_sort(sort.clone())
    } else if let PureExpr::Var(name, None) = expr {
        encoder
            .var_sort(name)
            .cloned()
            // Context-aware inference for non-declared vars. (#1965)
            .unwrap_or_else(|| encoder.infer_expr_sort_with_context(expr, None))
    } else {
        // Context-aware inference for non-Var expressions. (#1965)
        encoder.infer_expr_sort_with_context(expr, None)
    }
}

/// Assert only `_current` chain constraints for mutable-borrow verification.
///
/// Unlike `assert_by_value_alias_constraints`, this helper intentionally does
/// NOT assert base dereference identities such as `x_current = x` or
/// `x_final_current = x_final`. Mutable-borrow verification treats those base
/// symbols as distinct states, so equating them over-constrains tuples like
/// `(&mut T, &mut T)` (#1432).
///
/// This helper only asserts chain links where both sides are already
/// `_current`-suffixed (for example `x_current_current = x_current`).
pub(in crate::verify) fn assert_current_chain_alias_constraints(
    encoder: &mut crate::encoder::AYEncoder,
) -> Result<(), EncodingError> {
    fn current_base(name: &str) -> Option<&str> {
        match DerivedKind::strip_from(name) {
            Some((DerivedKind::Current, base)) => Some(base),
            _ => None,
        }
    }

    fn has_current_parent(name: &str) -> bool {
        current_base(name).is_some()
    }

    let mut var_names = encoder.var_names();
    var_names.sort();
    let var_set: std::collections::HashSet<&str> = var_names.iter().map(String::as_str).collect();

    let mut aliases: Vec<(String, String)> = Vec::new();
    // O(1) dedup check for alias names, replacing O(N) linear scan (#1937)
    let mut alias_names: std::collections::HashSet<String> = std::collections::HashSet::new();

    // Direct `_current`-to-`_current` links: x_current_current = x_current.
    for name in &var_names {
        if let Some(base) = current_base(name) {
            if has_current_parent(base) && var_set.contains(base) {
                alias_names.insert(name.clone());
                aliases.push((name.clone(), base.to_string()));
            }
        }
    }

    // For deeper chains (x_current_current_current), synthesize missing
    // intermediate `_current` hops only when we already have a `_current`
    // ancestor in scope.
    for name in &var_names {
        let mut remaining = name.as_str();
        let mut root_current: Option<&str> = None;
        while let Some(base) = current_base(remaining) {
            if has_current_parent(base) && var_set.contains(base) {
                root_current = Some(base);
            }
            remaining = base;
        }

        if let Some(root) = root_current {
            let mut chain_part = root.to_string();
            while chain_part != *name {
                let next = DerivedKind::Current.format_name(&chain_part);
                if alias_names.insert(next.clone()) {
                    aliases.push((next.clone(), chain_part.clone()));
                }
                chain_part = next;
            }
        }
    }

    aliases.sort();
    aliases.dedup();

    for (alias_name, target_name) in &aliases {
        // Use resolve_var_sort_or_int to check declared sorts, sort hints,
        // and suffix-derived base sorts before falling back to Int. (#1608)
        let sort = encoder.resolve_var_sort_or_int(target_name);
        let alias_var = encoder.get_or_declare_var(alias_name, sort.clone())?;
        let target_var = encoder.get_or_declare_var(target_name, sort.clone())?;
        if alias_var == target_var {
            continue;
        }
        encoder.assert_eq(alias_var, target_var);

        debug!("  alias(current-chain): {alias_name} = {target_name}");
    }

    Ok(())
}
