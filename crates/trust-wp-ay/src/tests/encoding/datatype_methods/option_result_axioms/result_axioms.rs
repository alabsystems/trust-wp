// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_result_ok_is_ok_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_ok_ok = method_call(logic_fn_call("Ok", vec![int(1)]), "is_ok", vec![]);

    let is_ok_term = encoder
        .encode_pure(&is_ok_ok)
        .expect("Ok(1).is_ok() should encode");
    encoder.assert_option_result_axioms();

    let negated = {
        let solver = encoder.solver_mut();
        solver.not(is_ok_term)
    };
    encoder.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "negation of Ok(1).is_ok() should be unsat after Result axioms"
    );
}

#[test]
#[timeout(30000)]
fn test_result_err_is_err_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_err_err = method_call(logic_fn_call("Err", vec![int(99)]), "is_err", vec![]);

    let is_err_term = encoder
        .encode_pure(&is_err_err)
        .expect("Err(99).is_err() should encode");
    encoder.assert_option_result_axioms();

    let negated = {
        let solver = encoder.solver_mut();
        solver.not(is_err_term)
    };
    encoder.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "negation of Err(99).is_err() should be unsat after Result axioms"
    );
}

#[test]
#[timeout(30000)]
fn test_result_ok_unwrap_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let unwrap_ok = method_call(logic_fn_call("Ok", vec![int(42)]), "unwrap", vec![]);

    let unwrap_term = encoder
        .encode_pure(&unwrap_ok)
        .expect("Ok(42).unwrap() should encode");
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
        "Ok(42).unwrap() != 42 should be unsat after Result axioms"
    );
}

#[test]
#[timeout(30000)]
fn test_result_err_unwrap_err_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let unwrap_err_err = method_call(logic_fn_call("Err", vec![int(77)]), "unwrap_err", vec![]);

    let unwrap_err_term = encoder
        .encode_pure(&unwrap_err_err)
        .expect("Err(77).unwrap_err() should encode");
    let seventy_seven = encoder.encode_pure(&int(77)).unwrap();
    encoder.assert_option_result_axioms();

    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(unwrap_err_term, seventy_seven);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Err(77).unwrap_err() != 77 should be unsat after Result axioms"
    );
}

#[test]
#[timeout(30000)]
fn test_result_err_is_not_ok_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_ok_err = method_call(logic_fn_call("Err", vec![int(1)]), "is_ok", vec![]);

    let is_ok_term = encoder
        .encode_pure(&is_ok_err)
        .expect("Err(1).is_ok() should encode");
    encoder.assert_option_result_axioms();

    encoder.assert_term(is_ok_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Err(1).is_ok() should be unsat after Result axioms"
    );
}

#[test]
#[timeout(30000)]
fn test_result_ok_is_not_err_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_err_ok = method_call(logic_fn_call("Ok", vec![int(1)]), "is_err", vec![]);

    let is_err_term = encoder
        .encode_pure(&is_err_ok)
        .expect("Ok(1).is_err() should encode");
    encoder.assert_option_result_axioms();

    encoder.assert_term(is_err_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Ok(1).is_err() should be unsat after Result axioms"
    );
}
