// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::ExprSort;

use super::*;
use crate::encoder::sort_context::{
    collect_all_sort_hints, mapping_expr_sort, SortHintAccumulator,
};

mod hint_propagation;
mod mapping_methods;
mod normalization;
mod returns;

/// Canonical FMap sort for sort-context tests.
fn fmap_sort_for_test() -> Sort {
    Sort::Uninterpreted("FMap".to_string())
}

/// Canonical Mapping sort for PredCell view tests.
fn mapping_sort_for_test() -> Sort {
    Sort::Uninterpreted("Mapping".to_string())
}
