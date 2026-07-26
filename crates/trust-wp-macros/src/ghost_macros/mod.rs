// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expansion logic for `ghost!`, `snapshot!`, `ghost_let!`, and `proof_assert!` proc macros.
//!
//! This module is decomposed by concern:
//! - `ident_capture`: Test-only free variable extraction and quantifier binding analysis
//! - `proof_assert`: `proof_assert`! and `trusted_proof_assert`! expansion
//! - `snapshot`: snapshot! expansion and spec-only call detection
//! - `ghost_block`: ghost! expansion
//! - `ghost_let`: `ghost_let`! expansion and parsing

mod ghost_block;
mod ghost_let;
#[cfg(test)]
pub(crate) mod ident_capture;
mod proof_assert;
mod proof_by;
mod snapshot;

#[cfg(test)]
mod tests;

pub(crate) use ghost_block::expand_ghost;
pub(crate) use ghost_let::expand_ghost_let;
pub(crate) use proof_assert::{expand_proof_assert, expand_trusted_proof_assert};
pub(crate) use proof_by::expand_proof;
pub(crate) use snapshot::expand_snapshot;
