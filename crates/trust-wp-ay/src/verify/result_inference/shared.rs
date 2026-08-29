// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared walkers for `result` inference.

use trust_wp_core::formula::PureExpr;

/// Check whether `result` appears as a free variable anywhere in `expr`.
pub(crate) fn expr_contains_result_var(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Var(name, _) if name == "result"))
}
