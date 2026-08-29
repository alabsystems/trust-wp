// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_option_none_is_none_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_none_none = method_call(logic_fn_call("None", vec![]), "is_none", vec![]);

    let is_none_term = encoder
        .encode_pure(&is_none_none)
        .expect("None.is_none() should encode");
    encoder.assert_option_result_axioms();

    let negated = {
        let solver = encoder.solver_mut();
        solver.not(is_none_term)
    };
    encoder.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "negation of None.is_none() should be unsat after Option axioms"
    );
}

#[test]
#[timeout(30000)]
fn test_option_some_is_some_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_some_some = method_call(logic_fn_call("Some", vec![int(42)]), "is_some", vec![]);

    let is_some_term = encoder
        .encode_pure(&is_some_some)
        .expect("Some(42).is_some() should encode");
    encoder.assert_option_result_axioms();

    let negated = {
        let solver = encoder.solver_mut();
        solver.not(is_some_term)
    };
    encoder.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "negation of Some(42).is_some() should be unsat after Option axioms"
    );
}

#[test]
#[timeout(30000)]
fn test_option_some_unwrap_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let unwrap_some = method_call(logic_fn_call("Some", vec![int(42)]), "unwrap", vec![]);

    let unwrap_term = encoder
        .encode_pure(&unwrap_some)
        .expect("Some(42).unwrap() should encode");
    let forty_two = encoder.encode_pure(&int(42)).unwrap();
    encoder.assert_option_result_axioms();

    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(unwrap_term, forty_two);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Some(42).unwrap() != 42 should be unsat after Option axioms"
    );
}
