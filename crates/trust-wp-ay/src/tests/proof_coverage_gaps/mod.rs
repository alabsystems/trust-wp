// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof coverage gap tests for untested encoder functions.
//!
//! Targets functions identified with ZERO test coverage in the #901 coverage audit:
//!
//! 1. **`propagate_body_view_seq_value_to_result`** — bridges SeqValue from
//!    body result view to `result_view` for postcondition verification.
//!
//! 2. **`SwitchTarget::datatype`** — builds ay `DatatypeSort` for
//!    Option/Result/UserDefined variants. UserDefined branch untested.
//!
//! 3. **`is_constructor_exhaustive` → `check_flat_constructor_exhaustive`** —
//!    flat constructor exhaustiveness checking (tested via encoding API).
//!
//! 4. **`check_tuple_exhaustive` / `cross_product_covered`** — tuple-pattern
//!    exhaustiveness checking via encoding API (#1703).
//!
//! 5. **`safe_apply`** — sort-mismatch error recovery (error path untested).
//!
//! 6. **`scrutinee_existing_datatype`** — retrieves existing DatatypeSort for
//!    already-declared scrutinee variables (#1763).
//!
//! These tests are designed to NOT depend on ay UNSAT solving (which is
//! currently broken by the ay pin regression, see #1603). They verify
//! structural correctness, state mutations, and error paths.
//!
//! Part of #901
//! Re: #1603, #1667

use ay_dpll::api::Sort;
use ntest::timeout;

pub(super) use super::{
    super::{encoder::match_enc::SwitchTarget, AYEncoder},
    helpers::*,
};
use crate::Pattern;

mod domain_sort_hints;
mod flat_match_exhaustiveness;
mod recursive_adt_regressions;
mod result_view_propagation;
mod safe_apply_and_scrutinee;
mod seq_arity_errors;
mod switch_target_datatypes;
mod tuple_match_exhaustiveness;
