// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mutable borrow verification tests for trust-wp-ay.
//!
//! Tests for `verify_mut_borrow_function` which handles RustHorn-style
//! mutable borrow verification.

pub(super) use super::{super::*, helpers::*};

mod bool_and_canonicalization;
mod collapse_old;
mod core_contracts;
mod pipeline_alias_regressions;
mod return_canonicalization;
mod return_paths;
mod tuple_field_tracking;
mod type_invariants;
