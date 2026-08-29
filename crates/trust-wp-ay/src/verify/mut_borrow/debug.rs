// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Debug-only request logging for mut-borrow verification.

use std::collections::{HashMap, HashSet};

use tracing::debug;
use trust_wp_core::formula::PureExpr;

pub(super) fn debug_log_request(
    track: &impl std::fmt::Debug,
    requires: &[PureExpr],
    ensures: &[PureExpr],
    final_values: &HashMap<String, PureExpr>,
    return_expr: Option<&PureExpr>,
    ghost_context: Option<&[PureExpr]>,
    mutation_continued_params: Option<&HashSet<String>>,
) {
    debug!("=== verify_mut_borrow_function ===");
    debug!("  track: {track:?}");
    debug!("  requires ({}):", requires.len());
    for (i, req) in requires.iter().enumerate() {
        debug!("    [{i}]: {req:?}");
    }
    debug!("  ensures ({}):", ensures.len());
    for (i, ens) in ensures.iter().enumerate() {
        debug!("    [{i}]: {ens:?}");
    }
    debug!("  final_values ({}):", final_values.len());
    for (name, expr) in final_values {
        debug!("    {name}: {expr:?}");
    }
    debug!("  return_expr: {return_expr:?}");
    debug!(
        "  ghost_context ({}):",
        ghost_context.map_or(0, <[PureExpr]>::len)
    );
    if let Some(exprs) = ghost_context {
        for (i, expr) in exprs.iter().enumerate() {
            debug!("    [{i}] {expr}");
        }
    }
    if let Some(params) = mutation_continued_params {
        debug!("  mutation_continued_params: {params:?}");
    }
}
