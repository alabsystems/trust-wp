// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Clause-generation and supporting utility tests for type invariants.

use std::sync::Arc;

use trust_wp_core::{
    closure::{CaptureField, CaptureKind, ClosureCaptureInfo},
    formula::{intern_sort_name, BinOp, ExprSort, Pattern, PureExpr},
};

use super::super::{
    build_closure_capture_invariant_requires, build_current_closure_self_invariant_requires,
};

#[path = "clauses/tuple_newtype_decomposition.rs"]
mod tuple_newtype_decomposition;

#[path = "clauses/result_option_structural_clauses.rs"]
mod result_option_structural_clauses;

#[path = "clauses/closure_capture_requires.rs"]
mod closure_capture_requires;

#[path = "clauses/helper_tail.rs"]
mod helper_tail;
