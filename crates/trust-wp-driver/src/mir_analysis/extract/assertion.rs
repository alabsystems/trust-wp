// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Assertion terminator helpers shared by extraction variants.

use std::sync::Arc;

use rustc_middle::mir::{AssertKind, BinOp as MirBinOp, Operand};
use trust_wp_core::formula::{PureExpr, UnOp};

use super::super::{effects::CallEffects, spanned::SpannedBodyExpr, translate::ExprLookup};
use crate::mir_analysis::translate::translate_operand;

pub(super) fn assert_fact_from_condition<'tcx>(
    cond: &Operand<'tcx>,
    expected: bool,
    msg: &AssertKind<Operand<'tcx>>,
    local_exprs: &impl ExprLookup,
) -> Option<PureExpr> {
    // Shift-overflow asserts guard exactly the `0 <= amount < BITS` range
    // that the shift lowering emits as a PROOF obligation (the
    // `__trust_wp_shift_amount_in_range_{bits}` marker, ledger
    // int-shift-full). Assuming the assert condition here would inject the
    // very fact under proof into the VC context — for an over-wide shift the
    // "fact" is false (e.g. `8 < 8` for `1u8 >> 8`), which makes the whole
    // context inconsistent and every obligation, including the shift-range
    // obligation itself, pass vacuously. Skip the fact: the range knowledge
    // is re-derivable from the proved obligation, so downstream reasoning
    // loses nothing that was soundly available.
    if matches!(msg, AssertKind::Overflow(MirBinOp::Shl | MirBinOp::Shr, ..)) {
        return None;
    }
    translate_operand(cond, local_exprs).map(|cond_expr| {
        if expected {
            cond_expr
        } else {
            PureExpr::UnOp(UnOp::Not, Arc::new(cond_expr))
        }
    })
}

/// Wrap a continuation with an assert fact as `LetAssume`.
///
/// When continuation extraction fails (`None`) but the assert condition was
/// translated successfully, we still push the fact into the explicit
/// `CallEffects` so it constrains downstream verification context.
pub(super) fn wrap_continuation_with_assert_fact(
    assert_fact: Option<PureExpr>,
    continuation: Option<PureExpr>,
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    match (assert_fact, continuation) {
        (Some(fact), Some(body)) => Some(PureExpr::LetAssume {
            assumption: Arc::new(fact),
            body: Arc::new(body),
        }),
        (Some(fact), None) => {
            effects.assumptions.push(fact);
            None
        }
        (None, continuation) => continuation,
    }
}

pub(super) fn wrap_spanned_continuation_with_assert_fact(
    assert_fact: Option<PureExpr>,
    continuation: Option<SpannedBodyExpr>,
) -> Option<SpannedBodyExpr> {
    match assert_fact {
        Some(fact) => continuation.map(|mut spanned| {
            spanned.expr = PureExpr::LetAssume {
                assumption: Arc::new(fact),
                body: Arc::new(spanned.expr),
            };
            spanned
        }),
        None => continuation,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bool_var(name: &str) -> PureExpr {
        PureExpr::Var(
            name.to_string(),
            Some(trust_wp_core::formula::ExprSort::Bool),
        )
    }

    // --- wrap_continuation_with_assert_fact ---

    #[test]
    fn test_wrap_both_some_creates_let_assume() {
        let fact = bool_var("cond");
        let body = PureExpr::Int(42);
        let mut effects = CallEffects::new();

        let result = wrap_continuation_with_assert_fact(
            Some(fact.clone()),
            Some(body.clone()),
            &mut effects,
        );

        match result {
            Some(PureExpr::LetAssume {
                assumption,
                body: inner,
            }) => {
                assert_eq!(*assumption, fact);
                assert_eq!(*inner, body);
            }
            other => panic!("expected LetAssume, got {other:?}"),
        }
        // No side effects on CallEffects
        assert!(effects.assumptions.is_empty());
    }

    #[test]
    fn test_wrap_fact_some_continuation_none_pushes_to_effects() {
        let fact = bool_var("precondition");
        let mut effects = CallEffects::new();

        let result = wrap_continuation_with_assert_fact(Some(fact.clone()), None, &mut effects);

        assert!(result.is_none());
        assert_eq!(effects.assumptions.len(), 1);
        assert_eq!(effects.assumptions[0], fact);
    }

    #[test]
    fn test_wrap_fact_none_returns_continuation_unchanged() {
        let body = PureExpr::Int(7);
        let mut effects = CallEffects::new();

        let result = wrap_continuation_with_assert_fact(None, Some(body.clone()), &mut effects);

        assert_eq!(result, Some(body));
        assert!(effects.assumptions.is_empty());
    }

    #[test]
    fn test_wrap_both_none_returns_none() {
        let mut effects = CallEffects::new();

        let result = wrap_continuation_with_assert_fact(None, None, &mut effects);

        assert!(result.is_none());
        assert!(effects.assumptions.is_empty());
    }

    #[test]
    fn test_wrap_accumulates_multiple_facts() {
        let mut effects = CallEffects::new();

        // First call: fact without continuation pushes to effects
        wrap_continuation_with_assert_fact(Some(bool_var("a")), None, &mut effects);
        wrap_continuation_with_assert_fact(Some(bool_var("b")), None, &mut effects);

        assert_eq!(effects.assumptions.len(), 2);
        assert_eq!(effects.assumptions[0], bool_var("a"));
        assert_eq!(effects.assumptions[1], bool_var("b"));
    }
}
