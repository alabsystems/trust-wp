// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the solver-side vacuity guard extracted from `solver.rs` (#1988).

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use super::super::{AYEncoder, AssertionPhase};

/// Contradictory base assertions make the negated goal irrelevant.
/// The vacuity guard must detect this.
#[test]
#[timeout(30000)]
fn test_vacuity_contradictory_base() {
    let mut encoder = AYEncoder::new_pure();

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);

    // Contradictory base: x > 0 AND x < 0
    encoder.with_assertion_phase(AssertionPhase::Precondition, |encoder| {
        let pos = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(pos);
        let neg = encoder.solver_mut().lt(x, zero);
        encoder.assert_term(neg);
    });

    // Name an unrelated assertion as the "negated goal"
    let y = encoder.solver_mut().declare_const("y", Sort::Int);
    let five = encoder.solver_mut().int_const(5);
    let (result, core, vacuity_result) = encoder.with_negated_goal_label_prefix(
        "__trust_wp_negated_goal_slice_0".to_string(),
        |encoder| {
            encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |encoder| {
                let unrelated = encoder.solver_mut().gt(y, five);
                encoder.assert_term(unrelated);
            });
            (
                encoder.check_sat(),
                encoder.solver().try_get_unsat_core(),
                encoder.is_vacuous_unsat(),
            )
        },
    );

    assert_eq!(result, SolveResult::unsat());
    assert!(
        matches!(vacuity_result, Ok(true)),
        "should detect vacuous proof when base assertions are contradictory, got: {vacuity_result:?}, core: {core:?}"
    );
}

/// When the negated goal IS needed for the contradiction, the proof
/// is genuine (not vacuous).
#[test]
#[timeout(30000)]
fn test_vacuity_genuine_proof() {
    let mut encoder = AYEncoder::new_pure();

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let ten = encoder.solver_mut().int_const(10);

    // Consistent base: x > 0 AND x < 10
    encoder.with_assertion_phase(AssertionPhase::Precondition, |encoder| {
        let lower = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(lower);
        let upper = encoder.solver_mut().lt(x, ten);
        encoder.assert_term(upper);
    });

    // Negated goal that creates contradiction: x <= 0
    let (result, vacuity_result) = encoder.with_negated_goal_label_prefix(
        "__trust_wp_negated_goal_slice_1".to_string(),
        |encoder| {
            encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |encoder| {
                let negated_goal = encoder.solver_mut().le(x, zero);
                encoder.assert_term(negated_goal);
            });
            (encoder.check_sat(), encoder.is_vacuous_unsat())
        },
    );

    assert_eq!(result, SolveResult::unsat());
    assert!(
        matches!(vacuity_result, Ok(false)),
        "should NOT detect vacuity when negated goal participates in the proof"
    );
}

/// When no label is set (legacy path), is_vacuous_unsat returns false.
#[test]
#[timeout(30000)]
fn test_vacuity_no_label_legacy() {
    let mut encoder = AYEncoder::new_pure();

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);

    // Contradictory assertions but no negated goal label
    let pos = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(pos);
    let neg = encoder.solver_mut().lt(x, zero);
    encoder.assert_term(neg);

    let result = encoder.check_sat();
    assert_eq!(result, SolveResult::unsat());
    assert!(
        matches!(encoder.is_vacuous_unsat(), Ok(false)),
        "legacy path (no label) should return non-vacuous"
    );
}
