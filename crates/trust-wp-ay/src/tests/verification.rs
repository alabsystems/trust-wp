// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verification-oriented tests for trust-wp-ay.

use std::collections::HashMap;

use ntest::timeout;

use super::{super::*, helpers::*};

mod bool_iff_and_trivial_invariant;
mod callsite_tuple_bool;
mod checked_ops_signed;
mod cloned_ok_ok_postcondition_pipeline;
mod dedup_snapshot_slicing;
mod invariant_and_track_level;
mod iterator_produces_element_identity;
mod iterator_produces_precondition_satisfiability;
mod obligation_slicing_axiom_shortcuts;
mod panic_and_runtime_guards;
mod produces_modes_vec;
mod quantifier_box_option_closure_seq;
mod seq_iter_produces;
mod std_specs_collections;
mod type_invariant_arithmetic_preservation;
mod type_invariant_comprehensive;
mod type_invariant_nonzero_and_generated;
mod type_invariant_structural;
mod wrapping_and_invariant_preservation;
