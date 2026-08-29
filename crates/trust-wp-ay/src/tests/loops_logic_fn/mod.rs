// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop + logic function axiom integration tests (#739).
//!
//! Extracted from `loops.rs` to reduce file size and ownership collisions (#772).
//! Tests that logic function axioms, tuple axioms, and Option/Result axioms
//! are properly registered during all loop verification phases.

// Degraded assertions (assert_verified_or_unknown, assert_failed_or_unknown) removed
// in #1992 — ay now returns definitive results for all call sites in this file.

pub(super) use std::collections::HashMap;

pub(super) use super::{super::*, helpers::*};

mod closure_specs;
mod follow_up_integration;
mod initialization_and_filtering;
mod integration_init_post;
mod integration_variants;
mod option_and_postcondition;
mod preservation_foundations;
mod result_axioms_and_modes;
mod subresult_isolation;
