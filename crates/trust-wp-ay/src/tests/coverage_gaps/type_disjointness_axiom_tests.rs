// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Type disjointness: is_some(Ok(v)) must be false.
///
/// Without this axiom, the solver could conflate Ok(v) with Some(v)
/// since both share the spec_unwrap UF (#599).
#[test]
#[timeout(30000)]
fn test_is_some_of_ok_is_false() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode is_some(Ok(7)) — must register both Option and Result symbols
    let ok_val = logic_fn_call("Ok", vec![int(7)]);
    let is_some_ok = method_call(ok_val, "is_some", vec![]);
    let is_some_ok_term = encoder
        .encode_pure(&is_some_ok)
        .expect("is_some(Ok(7)) should encode");

    encoder.assert_option_result_axioms();

    // Assert is_some(Ok(7)) — should be UNSAT by disjointness axiom
    encoder.assert_term(is_some_ok_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_some(Ok(v)) must be false (type disjointness)"
    );
}

/// Type disjointness: is_some(Err(v)) must be false.
#[test]
#[timeout(30000)]
fn test_is_some_of_err_is_false() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let err_val = logic_fn_call("Err", vec![int(7)]);
    let is_some_err = method_call(err_val, "is_some", vec![]);
    let is_some_err_term = encoder
        .encode_pure(&is_some_err)
        .expect("is_some(Err(7)) should encode");

    encoder.assert_option_result_axioms();

    encoder.assert_term(is_some_err_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_some(Err(v)) must be false (type disjointness)"
    );
}

/// Type disjointness: is_ok(Some(v)) must be false.
#[test]
#[timeout(30000)]
fn test_is_ok_of_some_is_false() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let some_val = logic_fn_call("Some", vec![int(7)]);
    let is_ok_some = method_call(some_val, "is_ok", vec![]);
    let is_ok_some_term = encoder
        .encode_pure(&is_ok_some)
        .expect("is_ok(Some(7)) should encode");

    encoder.assert_option_result_axioms();

    encoder.assert_term(is_ok_some_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_ok(Some(v)) must be false (type disjointness)"
    );
}

/// Type disjointness: is_ok(None) must be false.
#[test]
#[timeout(30000)]
fn test_is_ok_of_none_is_false() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let none = logic_fn_call("None", vec![]);
    let is_ok_none = method_call(none, "is_ok", vec![]);
    let is_ok_none_term = encoder
        .encode_pure(&is_ok_none)
        .expect("is_ok(None) should encode");

    encoder.assert_option_result_axioms();

    encoder.assert_term(is_ok_none_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_ok(None) must be false (type disjointness)"
    );
}

/// Mutual exclusion: is_some(x) && is_ok(x) must be false for any x.
///
/// This prevents the solver from assigning a value to x that satisfies
/// both Option and Result testers simultaneously.
#[test]
#[timeout(30000)]
fn test_mutual_exclusion_is_some_and_is_ok() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode both testers on the same variable
    let is_some_x = method_call(var("x"), "is_some", vec![]);
    let is_some_term = encoder
        .encode_pure(&is_some_x)
        .expect("x.is_some() should encode");

    let is_ok_x = method_call(var("x"), "is_ok", vec![]);
    let is_ok_term = encoder
        .encode_pure(&is_ok_x)
        .expect("x.is_ok() should encode");

    encoder.assert_option_result_axioms();

    // Assert both: is_some(x) AND is_ok(x)
    let both = {
        let solver = encoder.solver_mut();
        solver.and(is_some_term, is_ok_term)
    };
    encoder.assert_term(both);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_some(x) && is_ok(x) must be UNSAT (mutual exclusion axiom)"
    );
}

/// Err accessor axiom: unwrap_err(Err(v)) == v.
///
/// This is the Result error-side analog of unwrap(Ok(v)) == v.
#[test]
#[timeout(30000)]
fn test_err_accessor_unwrap_err_of_err() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let err_42 = logic_fn_call("Err", vec![int(42)]);
    let unwrap_err = method_call(err_42, "unwrap_err", vec![]);
    let unwrap_term = encoder
        .encode_pure(&unwrap_err)
        .expect("Err(42).unwrap_err() should encode");
    let forty_two = encoder.encode_pure(&int(42)).unwrap();

    encoder.assert_option_result_axioms();

    // Assert unwrap_err(Err(42)) != 42 — should be UNSAT by accessor axiom
    let neq = {
        let solver = encoder.solver_mut();
        let eq = solver.eq(unwrap_term, forty_two);
        solver.not(eq)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unwrap_err(Err(42)) must equal 42 (Err accessor axiom)"
    );
}
