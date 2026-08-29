// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop invariant verification tests for trust-wp-ay.
//!
//! Tests for `verify_loop_invariant` which handles:
//! - Loop initialization (precondition establishes invariant)
//! - Loop preservation (invariant + guard maintains invariant)
//! - Loop termination (invariant + !guard establishes postcondition)
//! - Loop counterexamples

// Degraded assertions (assert_verified_or_unknown, assert_failed_or_unknown) removed
// in #1992 — ay now returns definitive results for all call sites in this file.

pub(super) use std::collections::HashMap;

pub(super) use super::{super::*, helpers::*};

mod core_verification;
mod datatype_routing;
mod deref_and_seq_effects;
mod frame_preservation;
mod havoc_and_bool_conditions;
mod initialization;
mod issue_6214_diagnostics;
mod mode_parity_and_none_condition;
mod postcondition_outputs;
mod qflia_regressions;
mod results_and_counterexamples;
mod strict_inequality_preservation;
mod strict_inequality_variants;
mod variants;
mod vc_independence;
