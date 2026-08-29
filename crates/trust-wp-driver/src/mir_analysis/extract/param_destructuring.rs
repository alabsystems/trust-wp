// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parameter destructuring substitution extraction.
//!
//! When a function uses tuple destructuring in parameters (e.g.,
//! `fn foo((x, _): (u32, u32))`), the HIR parameter name extraction
//! falls back to positional names like `arg0`. This module resolves
//! those to the actual source-level names via MIR `var_debug_info`.
//!
//! Extracted from `extract/mod.rs` as part of the decomposition in #1644.

use std::collections::{HashMap, HashSet};

use rustc_middle::mir::{BasicBlock, Body, Local, StatementKind};
use trust_wp_core::formula::PureExpr;

use super::{
    super::translate::{translate_rvalue, ty_to_expr_sort_enriched},
    helpers::{expr_mentions_any_fallback_arg, is_fallback_arg_name},
};

/// Extract name substitutions for destructured parameter bindings.
///
/// When a function uses tuple destructuring in parameters (e.g.,
/// `fn foo((x, _): (u32, u32))`), the HIR parameter name extraction
/// falls back to positional names like `arg0`. However, `var_debug_info`
/// contains entries mapping the destructured binding names (e.g., `x`)
/// to the locals that hold the projected values.
///
/// This function walks the first basic block of MIR to resolve
/// parameter field projections (e.g., `_2 = _1.0`), then uses
/// `var_debug_info` to map source names to the projected expressions.
///
/// Returns a substitution map (e.g., `{"x" => tuple_get_0(Var("arg0"))}`)
/// that should be applied to contracts before verification.
pub(crate) fn extract_param_destructuring_substitutions<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
) -> HashMap<String, PureExpr> {
    // Destructured parameters are represented with synthetic fallback names
    // like `arg0`, `arg1`, ... when HIR cannot recover source bindings.
    // If no fallback names exist, there is nothing to rewrite.
    let fallback_arg_names: HashSet<String> = arg_names
        .iter()
        .filter(|name| is_fallback_arg_name(name))
        .cloned()
        .collect();
    if fallback_arg_names.is_empty() {
        return HashMap::new();
    }

    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
    }

    // Walk bb0 to populate local_exprs for destructuring assignments.
    // These are typically `_2 = (_1.0: T)` — field projections on parameters.
    let bb0 = &body.basic_blocks[BasicBlock::from_u32(0)];
    for stmt in &bb0.statements {
        if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
            if place.projection.is_empty() {
                if let Some(expr) = translate_rvalue(rvalue, &local_exprs, Some(body)) {
                    local_exprs.insert(place.local, expr);
                }
            }
        }
    }

    // Build substitutions from var_debug_info: for each source name with a
    // known expression that differs from identity, emit a substitution.
    let mut substitutions = HashMap::new();
    for debug in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &debug.value {
            if place.projection.is_empty() {
                let Some(expr) = local_exprs.get(&place.local) else {
                    continue;
                };
                let name = debug.name.to_string();
                // Skip identity mappings (name == variable name)
                if matches!(expr, PureExpr::Var(var, _) if var == &name) {
                    continue;
                }
                // Skip parameter locals — their names come from arg_names
                let idx = place.local.as_u32() as usize;
                if idx >= 1 && idx <= arg_names.len() {
                    continue;
                }
                // Skip wildcard bindings
                if name == "_" {
                    continue;
                }
                // Only rewrite names that ultimately depend on a fallback
                // parameter symbol (`argN`). This prevents ordinary locals
                // initialized in the function body (for example `let i = 0`)
                // from being substituted into contracts. (#1137)
                if !expr_mentions_any_fallback_arg(expr, &fallback_arg_names) {
                    continue;
                }
                substitutions.insert(name, expr.clone());
            }
        }
    }
    substitutions
}
