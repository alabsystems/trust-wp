// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Basic encoding tests for trust-wp-ay.
//!
//! Tests for primitive types, arithmetic operations, boolean operations,
//! and basic formula encoding.

use std::sync::Arc;

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
use ntest::timeout;

use super::{super::*, helpers::*};

#[cfg(test)]
mod basic_encodings;
#[cfg(test)]
mod bitwise_and_arithmetic;
#[cfg(test)]
mod boolean_models_and_diagnostics;
#[cfg(test)]
mod formula_and_borrow;
#[cfg(test)]
mod seq_regressions;
#[cfg(test)]
mod sort_hints_and_seq;
#[cfg(test)]
mod unop_and_bool_hints;
