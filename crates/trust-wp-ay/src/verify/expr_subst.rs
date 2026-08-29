// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Thin ay-scoped wrappers around trust-wp-core's capture-avoiding substitution.
//!
//! The substitution semantics now live in `trust-wp-core`. This module keeps the
//! existing ay entry points and applies the encoder depth limit as caller
//! policy.

use std::collections::HashMap;

#[cfg(test)]
use trust_wp_core::formula::rename_free_var as core_rename_free_var;
use trust_wp_core::formula::{CaptureAvoidingSubstOptions, PureExpr};

use crate::encoder::MAX_ENCODING_DEPTH;

fn depth_limited_options() -> CaptureAvoidingSubstOptions {
    CaptureAvoidingSubstOptions {
        depth_limit: Some(MAX_ENCODING_DEPTH),
    }
}

/// Check whether `name` appears as a free variable anywhere in `expr`.
/// Delegates to `crate::expr::expr_mentions_var` (same depth-limited core wrapper).
#[cfg(test)]
pub(crate) fn expr_has_free_occurrence(expr: &PureExpr, name: &str) -> bool {
    crate::expr::expr_mentions_var(expr, name)
}

/// Rename all free occurrences of `old_name` to `new_name`.
#[cfg(test)]
fn rename_free_var(expr: &PureExpr, old_name: &str, new_name: &str) -> PureExpr {
    core_rename_free_var(expr, old_name, new_name, &depth_limited_options())
}

/// Capture-avoiding substitution for `PureExpr`.
pub(crate) fn substitute_vars_in_expr(
    expr: &PureExpr,
    binding: &HashMap<String, PureExpr>,
) -> PureExpr {
    expr.substitute_capture_avoiding(binding, &depth_limited_options())
}

#[cfg(test)]
mod tests;
