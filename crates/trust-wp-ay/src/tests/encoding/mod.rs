// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Encoding tests for trust-wp-ay.
//!
//! Error display, deref/final encoding, view expression encoding, and Vec verification tests.
//! Quantifier, seq, heap, and logic function tests are split into separate modules per #395.

use std::sync::Arc;

use ntest::timeout;

pub(super) use super::{super::*, helpers::*};

mod closure_spec_methods;
mod deref_final_names;
mod error_display;
mod runtime_bool_hints;
mod vec_verification;
mod view_nested;

mod datatype_methods;
mod final_deref_logic_fn;

mod deref_final_ite;
mod method_call_fallback;
mod method_encoding;
