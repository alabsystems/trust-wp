// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── Placeholder-backed Option/Result axiom regressions (#2274) ──
//
// Standard constructors now stay under signature-keyed placeholder names.
// These tests verify the Option/Result axiom layer still finds the Int-model
// family semantically, without reintroducing raw-name aliases.

#[test]
#[timeout(30000)]
fn test_placeholder_encoded_some_supports_is_some_axiom_without_raw_alias() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_some_term = encoder
        .encode_pure(&method_call(
            logic_fn_call("Some", vec![int(42)]),
            "is_some",
            vec![],
        ))
        .expect("Some(42).is_some() should encode through the placeholder path");

    encoder.assert_option_result_axioms();
    let negated = {
        let solver = encoder.solver_mut();
        solver.not(is_some_term)
    };
    encoder.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "!is_some(Some(42)) should be UNSAT after placeholder-backed axiom lookup"
    );
}

#[test]
#[timeout(30000)]
fn test_placeholder_encoded_some_supports_unwrap_axiom_without_raw_alias() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let unwrap_term = encoder
        .encode_pure(&method_call(
            logic_fn_call("Some", vec![int(42)]),
            "unwrap",
            vec![],
        ))
        .expect("Some(42).unwrap() should encode through the placeholder path");
    let forty_two = encoder.encode_pure(&int(42)).expect("42 should encode");

    encoder.assert_option_result_axioms();
    let neq = {
        let solver = encoder.solver_mut();
        solver.neq(unwrap_term, forty_two)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unwrap(Some(42)) != 42 should be UNSAT after placeholder-backed axiom lookup"
    );
}

#[test]
#[timeout(30000)]
fn test_placeholder_encoded_ok_supports_is_ok_axiom_without_raw_alias() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_ok_term = encoder
        .encode_pure(&method_call(
            logic_fn_call("Ok", vec![int(7)]),
            "is_ok",
            vec![],
        ))
        .expect("Ok(7).is_ok() should encode through the placeholder path");

    encoder.assert_option_result_axioms();
    let negated = {
        let solver = encoder.solver_mut();
        solver.not(is_ok_term)
    };
    encoder.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "!is_ok(Ok(7)) should be UNSAT after placeholder-backed axiom lookup"
    );
}

#[test]
#[timeout(30000)]
fn test_placeholder_encoded_err_supports_unwrap_err_axiom_without_raw_alias() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let unwrap_err_term = encoder
        .encode_pure(&method_call(
            logic_fn_call("Err", vec![int(7)]),
            "unwrap_err",
            vec![],
        ))
        .expect("Err(7).unwrap_err() should encode through the placeholder path");
    let seven = encoder.encode_pure(&int(7)).expect("7 should encode");

    encoder.assert_option_result_axioms();
    let neq = {
        let solver = encoder.solver_mut();
        solver.neq(unwrap_err_term, seven)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unwrap_err(Err(7)) != 7 should be UNSAT after placeholder-backed axiom lookup"
    );
}
