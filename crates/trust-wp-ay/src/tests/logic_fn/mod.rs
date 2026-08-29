// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for logic function call encoding and registration with axioms.
//!
//! - Call encoding tests (Part of #174)
//! - Registration tests (Part of #174)
//! - Logic function verification tests (Issue #234)
//!
//! Split from encoding.rs per #395.

pub(super) use super::{super::*, helpers::*};

mod bool_and_mixed_params;
mod call_coercions;
mod call_routing;
mod filtering_and_cleanup;
mod float_int_builtins;
mod fn_closure_law_tests;
mod fn_mut_once_law_tests;
mod mode_tests;
mod param_sort_seq_inference;
mod param_sort_tests;
mod placeholder_and_pearlite;
mod postcondition_ay_integration;
mod postcondition_verification;
mod registration_basics;
mod registration_dependency_surface;
mod resolve_tests;
mod soundness_regressions;
mod spec_axiom_encoding;
mod type_invariants_and_mode_batch;
mod verification_axioms;
