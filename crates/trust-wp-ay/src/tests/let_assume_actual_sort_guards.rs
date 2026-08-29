// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Actual-sort regression tests for LetAssume/LetObligation guards.

use ntest::timeout;

use super::{super::*, helpers::*};

#[test]
#[timeout(30000)]
fn let_assume_bool_hint_body_actual_int_avoids_implies_sort_panic() {
    let mut encoder = AYEncoder::new();
    let x_name = "__let_assume_bool_hint_x";
    let x = encoder
        .solver
        .declare_const(x_name, ay_dpll::api::Sort::Int);
    encoder.vars_mut_for_test().insert(x_name.to_string(), x);
    encoder
        .var_sorts_mut_for_test()
        .insert(x_name.to_string(), ay_dpll::api::Sort::Int);
    encoder.record_sort_hint(x_name.to_string(), ExprSort::Bool);

    let expr = let_assume(bool_expr(true), var(x_name));
    let term = encoder
        .encode_pure(&expr)
        .expect("Bool-inferred LetAssume body should encode without implies sort panic");
    assert_eq!(encoder.solver.get_sort(term), ay_dpll::api::Sort::Int);
    assert!(
        encoder.solver_panic_reason().is_none(),
        "actual-sort guard should skip implies(Bool, Int) in LetAssume"
    );

    let term_differs = encoder.solver.neq(term, x);
    encoder.solver.assert_term(term_differs);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "LetAssume with an Int-valued body should return the original Int term"
    );
}

#[test]
#[timeout(30000)]
fn let_assume_actual_int_assumption_with_bool_body_stays_implication() {
    let mut encoder = AYEncoder::new();
    let a_name = "__let_assume_int_assumption";
    let a = encoder
        .solver
        .declare_const(a_name, ay_dpll::api::Sort::Int);
    encoder.vars_mut_for_test().insert(a_name.to_string(), a);
    encoder
        .var_sorts_mut_for_test()
        .insert(a_name.to_string(), ay_dpll::api::Sort::Int);
    encoder.record_sort_hint(a_name.to_string(), ExprSort::Bool);

    let expr = let_assume(var(a_name), bool_expr(true));
    let term = encoder
        .encode_pure(&expr)
        .expect("Bool-bodied LetAssume should encode even when the assumption term is Int");
    assert_eq!(encoder.solver.get_sort(term), ay_dpll::api::Sort::Bool);
    assert!(
        encoder.solver_panic_reason().is_none(),
        "actual-sort guard should avoid implies(Int, Bool) in LetAssume"
    );

    let zero = encoder.solver.int_const(0);
    let a_eq_zero = encoder.solver.eq(a, zero);
    encoder.solver.assert_term(a_eq_zero);
    encoder.solver.assert_term(term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "a == 0 should satisfy (a => true); LetAssume must not assert the Int fallback antecedent globally"
    );
}
