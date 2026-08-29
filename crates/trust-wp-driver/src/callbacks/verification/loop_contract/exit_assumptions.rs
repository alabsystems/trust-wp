// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop-exit assumption builders for compositional post-loop verification.
//!
//! Extracted from `loop_contract.rs` per #2321.

use std::sync::Arc;

use trust_wp_ay::{LoopVerificationResult, VerificationResult};
use trust_wp_core::formula::PureExpr;

/// Build loop-exit assumptions from invariants and negated loop condition.
///
/// At loop exit, we know `invariants ∧ ¬condition` holds. This function
/// constructs that conjunction as a `Vec<PureExpr>` suitable for injection
/// into `effective_requires` for post-loop function-level verification.
///
/// Used by `verify_contract_loop_path` when returning `ContinueWithAssumptions`.
/// Extracted as a standalone function for testability (#2085).
pub(crate) fn build_loop_exit_assumptions(
    invariants: &[PureExpr],
    loop_condition: Option<&PureExpr>,
) -> Vec<PureExpr> {
    let mut assumptions = Vec::with_capacity(invariants.len() + 1);
    assumptions.extend(invariants.iter().cloned());
    if let Some(cond) = loop_condition {
        assumptions.push(PureExpr::UnOp(
            trust_wp_core::formula::UnOp::Not,
            Arc::new(cond.clone()),
        ));
    }
    assumptions
}

/// Returns true when compositional post-loop verification can safely reuse
/// loop-exit assumptions.
///
/// This is sound only after the inductive proof has been verified, not merely
/// assumed. In that case, a loop-local postcondition `Failed` or `Unknown`
/// result means the loop exit facts are established but insufficient for the
/// loop-only VC, so the driver should continue with the full function-level
/// path. (#2085, #2171)
pub(crate) fn should_continue_with_loop_exit_assumptions(result: &LoopVerificationResult) -> bool {
    result.induction_passed()
        && matches!(
            &result.postcondition,
            VerificationResult::Failed(_) | VerificationResult::Unknown(_)
        )
}
