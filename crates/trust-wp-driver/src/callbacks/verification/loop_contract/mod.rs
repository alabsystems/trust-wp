// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop-with-invariant verification path and trait refinement checks.
//!
//! Decomposed from a single `loop_contract.rs` into submodules per #2321:
//! - `obligation`: call-site obligation verification under loop invariants
//! - `exit_assumptions`: loop-exit assumption builders
//! - `dispatch`: loop path dispatch, trait refinement, `ContinueWithAssumptions`

mod dispatch;
mod exit_assumptions;
mod obligation;

// Re-export all public items at the original `loop_contract::` path so
// existing imports in verification.rs and tests continue to work unchanged.
pub(crate) use dispatch::{check_trait_refinement, verify_contract_loop_path, LoopPathOutcome};
#[cfg(test)]
pub(crate) use exit_assumptions::{
    build_loop_exit_assumptions, should_continue_with_loop_exit_assumptions,
};
#[cfg(test)]
pub(crate) use obligation::{
    classify_obligation_outcome, classify_obligation_result, record_encoding_error,
    verify_loop_call_obligations, worse_result, LoopCallObligationContext, ObligationOutcome,
};
