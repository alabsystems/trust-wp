// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable analysis utilities for `PureExpr` trees.
//!
//! Thin wrapper around trust-wp-core's `expr_has_free_occurrence`, applying
//! the encoder depth limit as caller policy.

use trust_wp_core::formula::{expr_has_free_occurrence, CaptureAvoidingSubstOptions, PureExpr};

use crate::encoder::MAX_ENCODING_DEPTH;

/// Check whether a `PureExpr` mentions a free variable name.
///
/// Respects variable shadowing: quantifier-bound variables, let bindings,
/// match pattern bindings, and closure parameters all shadow outer names.
/// Fails closed at `MAX_ENCODING_DEPTH` (assumes variable is mentioned).
///
/// Delegates to `trust_wp_core::formula::expr_has_free_occurrence`. (#2654)
pub(crate) fn expr_mentions_var(expr: &PureExpr, var: &str) -> bool {
    expr_has_free_occurrence(
        expr,
        var,
        &CaptureAvoidingSubstOptions {
            depth_limit: Some(MAX_ENCODING_DEPTH),
        },
    )
}
