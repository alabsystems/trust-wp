// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq encoding (Part of #111).
//!
//! Includes sequence view, len, index, `push_back`, error handling, and axiom tests.
//! Split from encoding.rs per #395.

use std::sync::Arc;

use ntest::timeout;

use super::{super::*, helpers::*};

mod contains_and_array_ops;
mod error_pop_back_contract;
mod produces_seq_guards;
mod push_back_axioms_and_sort_propagation;
mod receiver_routing;
mod regression_edges_and_empty;
mod singleton_and_concat;
mod sum_get_and_completed;
mod target_patterns_and_reconstruction;
mod view_len_index_push_back;
