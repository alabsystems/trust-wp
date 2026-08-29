// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Top-level path-condition propagation for `LetAssume` chains.
//!
//! Originally part of `shared_constraints.rs`. Extracted as part of #1988.

use trust_wp_core::formula::PureExpr;

use crate::{encoder::unsoundness, error::EncodingError};

/// Assert top-level `LetAssume` assumptions from a return expression.
///
/// When the return_expr is encoded for side effects only (postconditions
/// do not reference `result`), the Bool-body `LetAssume` encoding produces
/// `assumption => body` (an implication) whose return value is discarded.
/// The assumption itself is never asserted as a standalone fact, so
/// postconditions cannot use branch conditions, let-binding equalities,
/// or pattern-match discriminant constraints.
///
/// This function walks the TOP-LEVEL LetAssume chain in return_expr,
/// collects their assumptions, encodes each one, and asserts it directly
/// on the encoder. Only assumptions in the sequential LetAssume/LetObligation
/// chain are collected — NOT those nested inside Ite branches, which must
/// remain branch-scoped per #815. (#1457)
pub(in crate::verify) fn assert_body_let_assume_path_conditions(
    encoder: &mut crate::encoder::AYEncoder,
    return_expr: &PureExpr,
) -> Result<(), EncodingError> {
    // Walk the sequential LetAssume/LetObligation chain at the top level.
    // Stop at any other node (Ite, BinOp, Var, etc.) to preserve branch
    // scoping: LetAssume nodes inside Ite branches must not leak globally (#815).
    let mut assumptions = Vec::new();
    let mut current = return_expr;
    loop {
        match current {
            PureExpr::LetAssume { assumption, body } => {
                assumptions.push(assumption.as_ref());
                current = body.as_ref();
            }
            PureExpr::LetObligation { body, .. } => {
                // LetObligation doesn't introduce an assumption, but its body
                // may continue the chain with more LetAssume nodes.
                current = body.as_ref();
            }
            _ => break,
        }
    }

    // Process all assumptions: assert successful ones, collect first error.
    // We assert all successful assumptions before returning any error so that
    // the solver has maximum context. The error is propagated as EncodingError
    // instead of silently dropping the assumption (#2663 Phase 2a).
    let mut first_error: Option<EncodingError> = None;
    for assumption in &assumptions {
        // Assumption position: shift-amount range obligations embedded in the
        // fact are owned by the body VALUE encoding — see
        // `with_assumption_position`. (ledger int-shift-full)
        match encoder.with_assumption_position(|encoder| encoder.encode_pure(assumption)) {
            Ok(term) => {
                let bool_term = encoder.coerce_bool_operand(term);
                encoder.assert_term(bool_term);
            }
            Err(e) => {
                // Assumption encoding failed (sort mismatch, etc.). Previously
                // silently dropped with LetAssumeDropped increment (#1291, #1457).
                // Now propagates as EncodingError per #2663 Phase 2a — turns
                // false proofs into Unknown, which is the safe direction.
                unsoundness::increment(unsoundness::UnsoundnessCategory::LetAssumeDropped);
                tracing::warn!(
                    assumption = ?assumption,
                    error = %e,
                    "path-condition assumption encoding failed — will propagate as error"
                );
                if first_error.is_none() {
                    first_error = Some(e);
                }
            }
        }
    }

    match first_error {
        Some(e) => Err(e),
        None => Ok(()),
    }
}
