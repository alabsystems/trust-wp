// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Edge coverage for `encoder/solver.rs:is_vacuous_unsat` (#2514).
//!
//! The production file already has inline tests for the main vacuous vs.
//! genuine proof split. This crate test module covers the remaining edge
//! behavior: exact-label matches, near-miss superstrings, and SAT fail-closed
//! handling when no unsat core exists.

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use crate::encoder::{AYEncoder, AssertionPhase};

#[test]
#[timeout(30000)]
fn vacuity_exact_goal_label_match_is_non_vacuous() {
    let mut encoder = AYEncoder::new_pure();

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let one = encoder.solver_mut().int_const(1);

    let precondition = encoder.solver_mut().eq(x, zero);
    encoder
        .solver_mut()
        .try_assert_named(precondition, "precondition")
        .expect("named precondition");

    let exact_goal = encoder.solver_mut().eq(x, one);
    encoder
        .solver_mut()
        .try_assert_named(exact_goal, "goal_exact")
        .expect("exact goal label");

    assert_eq!(encoder.check_sat(), SolveResult::unsat());
    let vacuity = encoder.with_negated_goal_label_prefix("goal_exact".to_string(), |encoder| {
        encoder.is_vacuous_unsat()
    });
    assert!(
        matches!(vacuity, Ok(false)),
        "exact label match should count as non-vacuous, got {vacuity:?}"
    );
}

#[test]
#[timeout(30000)]
fn vacuity_rejects_non_separator_superstring() {
    let mut encoder = AYEncoder::new_pure();

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let one = encoder.solver_mut().int_const(1);

    let precondition = encoder.solver_mut().eq(x, zero);
    encoder
        .solver_mut()
        .try_assert_named(precondition, "precondition")
        .expect("named precondition");

    let mismatched_goal = encoder.solver_mut().eq(x, one);
    encoder
        .solver_mut()
        .try_assert_named(mismatched_goal, "goalextra")
        .expect("near-miss goal label");

    assert_eq!(encoder.check_sat(), SolveResult::unsat());
    let vacuity = encoder.with_negated_goal_label_prefix(
        "goal".to_string(),
        crate::encoder::AYEncoder::is_vacuous_unsat,
    );
    assert!(
        matches!(vacuity, Ok(true)),
        "non-separator superstring should stay vacuous, got {vacuity:?}"
    );
}

#[test]
#[timeout(30000)]
fn vacuity_sat_result_propagates_unsat_core_error() {
    let mut encoder = AYEncoder::new_pure();

    let (result, vacuity_result) = encoder.with_negated_goal_label_prefix(
        "__trust_wp_negated_goal_slice_sat".to_string(),
        |encoder| {
            encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |encoder| {
                let tautology = encoder.solver_mut().bool_const(true);
                encoder.assert_term(tautology);
            });
            (encoder.check_sat(), encoder.is_vacuous_unsat())
        },
    );

    assert_eq!(result, SolveResult::Sat);
    assert!(
        vacuity_result.is_err(),
        "SAT result must fail closed when unsat core is unavailable, got {vacuity_result:?}"
    );
}
