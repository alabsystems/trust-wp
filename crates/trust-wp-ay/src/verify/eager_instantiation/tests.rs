// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for the eager existential instantiation subsystem.
//!
//! Kept as a thin root that wires focused submodules together so the test
//! family stays readable and easy to grow.

use std::{collections::HashMap, sync::Arc};

use ntest::timeout;
use trust_wp_core::formula::{ExprSort, Pattern, PureExpr};

use super::{
    collect_ground_postcondition_mut_calls, collect_ground_resolve_calls,
    collectors::{collect_body_postcondition_mut_calls, collect_body_resolve_calls},
    expr_mentions_bound_var, exprs_structurally_equal, flatten_nested_existentials,
    normalize_deref_final, try_match_expr, try_match_method_call, try_match_resolve_call,
    MethodCallPattern,
};
use crate::tests::helpers::*;

mod matching_collectors;
mod mentions_bound_var;
mod normalize;
mod perf_depth;
mod structural_eq;
