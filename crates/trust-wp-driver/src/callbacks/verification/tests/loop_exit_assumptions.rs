// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_ay::{Counterexample, LoopVerificationResult, UnknownReason, VerificationResult};
use trust_wp_core::formula::{BinOp, PureExpr};

use crate::callbacks::verification::loop_contract::{
    build_loop_exit_assumptions, should_continue_with_loop_exit_assumptions,
};

#[test]
fn build_loop_exit_assumptions_with_condition_appends_negated() {
    let inv1 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let inv2 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Le,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );

    let assumptions = build_loop_exit_assumptions(&[inv1.clone(), inv2.clone()], Some(&cond));

    assert_eq!(
        assumptions.len(),
        3,
        "should have 2 invariants + 1 negated condition"
    );
    assert_eq!(assumptions[0], inv1);
    assert_eq!(assumptions[1], inv2);
    assert!(
        matches!(
            &assumptions[2],
            PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, inner) if **inner == cond
        ),
        "third element should be Not(condition)"
    );
}

#[test]
fn build_loop_exit_assumptions_no_condition_omits_negation() {
    let inv = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );

    let assumptions = build_loop_exit_assumptions(std::slice::from_ref(&inv), None);

    assert_eq!(assumptions.len(), 1, "no condition means invariants only");
    assert_eq!(assumptions[0], inv);
}

#[test]
fn build_loop_exit_assumptions_empty_invariants_with_condition() {
    let cond = PureExpr::Bool(true);

    let assumptions = build_loop_exit_assumptions(&[], Some(&cond));

    assert_eq!(
        assumptions.len(),
        1,
        "no invariants but condition present means just negated condition"
    );
    assert!(
        matches!(
            &assumptions[0],
            PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, _)
        ),
        "should be Not(condition)"
    );
}

#[test]
fn build_loop_exit_assumptions_empty_both() {
    let assumptions = build_loop_exit_assumptions(&[], None);

    assert!(
        assumptions.is_empty(),
        "no invariants and no condition means empty assumptions"
    );
}

#[test]
fn continue_with_loop_exit_assumptions_when_only_postcondition_unknown() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Unknown(UnknownReason::Timeout),
        variant_nonneg: None,
        variant_decrease: None,
    };

    assert!(
        should_continue_with_loop_exit_assumptions(&result),
        "postcondition-only unknown should still preserve loop-exit assumptions"
    );
}

#[test]
fn continue_with_loop_exit_assumptions_when_only_postcondition_failed() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Failed(Counterexample {
            values: vec![],
            violated_postcondition: None,
        }),
        variant_nonneg: None,
        variant_decrease: None,
    };

    assert!(
        should_continue_with_loop_exit_assumptions(&result),
        "existing postcondition-failed deferral should remain enabled"
    );
}

#[test]
fn do_not_continue_with_loop_exit_assumptions_when_induction_is_incomplete() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Unknown(UnknownReason::SolverMessage(
            "preservation timeout".to_string(),
        )),
        postcondition: VerificationResult::Unknown(UnknownReason::SolverMessage(
            "postcondition timeout".to_string(),
        )),
        variant_nonneg: None,
        variant_decrease: None,
    };

    assert!(
        !should_continue_with_loop_exit_assumptions(&result),
        "loop-exit assumptions are unsound when induction itself is incomplete"
    );
}

#[test]
fn should_continue_with_loop_exit_assumptions_rejects_assumed_induction() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Assumed("trusted invariant".to_string()),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Unknown(UnknownReason::SolverMessage(
            "postcondition timeout".to_string(),
        )),
        variant_nonneg: None,
        variant_decrease: None,
    };

    assert!(
        !should_continue_with_loop_exit_assumptions(&result),
        "assumed induction must not authorize loop-exit assumptions"
    );
}
