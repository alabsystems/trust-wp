// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// Test that Option and Result using shared `spec_unwrap` do not conflate
/// `Some` and `Ok` values when both are present in the same query.
///
/// The axiom system uses a single `spec_unwrap` UF for both `Option::unwrap`
/// and `Result::unwrap`. This test verifies that `Some(42).unwrap()` still
/// correctly returns 42 even when Result axioms are also loaded.
#[test]
#[timeout(30000)]
fn test_option_result_shared_spec_unwrap_no_conflation() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode Some(42).unwrap() == 42
    let unwrap_some = method_call(logic_fn_call("Some", vec![int(42)]), "unwrap", vec![]);
    let some_unwrap_term = encoder
        .encode_pure(&unwrap_some)
        .expect("Some(42).unwrap() should encode");

    // Encode Ok(99).unwrap() — forces Result axioms to also be registered
    let _ok_unwrap_term = encoder
        .encode_pure(&method_call(
            logic_fn_call("Ok", vec![int(99)]),
            "unwrap",
            vec![],
        ))
        .expect("Ok(99).unwrap() should encode");

    // Assert all axioms (both Option and Result use spec_unwrap)
    encoder.assert_option_result_axioms();

    // Assert: Some(42).unwrap() != 42 — should be UNSAT
    let forty_two = encoder.encode_pure(&int(42)).unwrap();
    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(some_unwrap_term, forty_two);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Some(42).unwrap() should equal 42 even with Result axioms loaded"
    );
}

/// Test that `is_some` and `is_ok` are mutually exclusive — the disjointness
/// axiom `forall x. !(is_some(x) && is_ok(x))` prevents the solver from
/// making a single value satisfy both Option and Result predicates (#599).
#[test]
#[timeout(30000)]
fn test_option_result_type_disjointness() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode: is_some(logic_Ok(42))
    let is_some_of_ok = method_call(logic_fn_call("Ok", vec![int(42)]), "is_some", vec![]);

    let term = encoder
        .encode_pure(&is_some_of_ok)
        .expect("is_some(Ok(42)) should encode");
    encoder.assert_option_result_axioms();

    // Assert is_some(Ok(42)) — UNSAT because disjointness axiom prevents
    // any value from being both is_some and is_ok.
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "is_some(Ok(42)) should be UNSAT — disjointness axiom prevents \
             Option/Result type conflation (#599): got {result:?}"
    );
}
