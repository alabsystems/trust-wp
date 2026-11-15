// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expansion logic for `ghost!`, `snapshot!`, `ghost_let!`, and `proof_assert!` proc macros.
//!
//! This module is decomposed by concern:
//! - `ident_capture`: Test-only free variable extraction and quantifier binding analysis
//! - `proof_assert`: `proof_assert`! and `trusted_proof_assert`! expansion
//! - `snapshot`: snapshot! expansion
//! - `snapshot_expr_kind`: syntactic classification of the snapshot! argument
//!   (spec-only calls, place/reference expressions)
//! - `ghost_block`: ghost! expansion
//! - `ghost_let`: `ghost_let`! expansion and parsing

mod ghost_block;
mod ghost_let;
#[cfg(test)]
pub(crate) mod ident_capture;
mod proof_assert;
mod proof_by;
mod snapshot;
mod snapshot_expr_kind;

#[cfg(test)]
mod tests;

pub(crate) use ghost_block::expand_ghost;
pub(crate) use ghost_let::expand_ghost_let;
pub(crate) use proof_assert::{expand_proof_assert, expand_trusted_proof_assert};
pub(crate) use proof_by::expand_proof;
pub(crate) use snapshot::expand_snapshot;
