// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── Qualified constructor axiom tests (#1766) ──
//
// These tests verify that user-defined enums with qualified constructor names
// (e.g., `OwnResult::Ok`) receive the same axioms as standard `Ok`/`Err`/`Some`/`None`.

#[test]
#[timeout(30000)]
fn test_qualified_ok_is_ok_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register qualified Ok constructor via UF path and the is_ok tester.
    // Using "OwnResult::Ok" produces SMT name "logic_OwnResult_P__P_Ok".
    let is_ok_qok = method_call(
        logic_fn_call("OwnResult::Ok", vec![int(1)]),
        "is_ok",
        vec![],
    );

    let is_ok_term = encoder
        .encode_pure(&is_ok_qok)
        .expect("OwnResult::Ok(1).is_ok() should encode");
    encoder.assert_option_result_axioms();

    // Negate: !is_ok(OwnResult::Ok(1)) should be UNSAT
    let negated = {
        let solver = encoder.solver_mut();
        solver.not(is_ok_term)
    };
    encoder.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "negation of OwnResult::Ok(1).is_ok() should be UNSAT — \
             qualified constructor gets tester axiom (#1766)"
    );
}

#[test]
#[timeout(30000)]
fn test_qualified_ok_unwrap_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // OwnResult::Ok(42).unwrap() should equal 42
    let unwrap_qok = method_call(
        logic_fn_call("OwnResult::Ok", vec![int(42)]),
        "unwrap",
        vec![],
    );

    let unwrap_term = encoder
        .encode_pure(&unwrap_qok)
        .expect("OwnResult::Ok(42).unwrap() should encode");
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
        "OwnResult::Ok(42).unwrap() != 42 should be UNSAT — \
             qualified constructor gets accessor axiom (#1766)"
    );
}

#[test]
#[timeout(30000)]
fn test_qualified_err_is_err_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_err_qerr = method_call(
        logic_fn_call("OwnResult::Err", vec![int(99)]),
        "is_err",
        vec![],
    );

    let is_err_term = encoder
        .encode_pure(&is_err_qerr)
        .expect("OwnResult::Err(99).is_err() should encode");
    encoder.assert_option_result_axioms();

    let negated = {
        let solver = encoder.solver_mut();
        solver.not(is_err_term)
    };
    encoder.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "negation of OwnResult::Err(99).is_err() should be UNSAT — \
             qualified Err constructor gets tester axiom (#1766)"
    );
}

#[test]
#[timeout(30000)]
fn test_qualified_err_unwrap_err_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let unwrap_err_qerr = method_call(
        logic_fn_call("OwnResult::Err", vec![int(7)]),
        "unwrap_err",
        vec![],
    );

    let unwrap_err_term = encoder
        .encode_pure(&unwrap_err_qerr)
        .expect("OwnResult::Err(7).unwrap_err() should encode");
    let seven = encoder.encode_pure(&int(7)).unwrap();
    encoder.assert_option_result_axioms();

    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(unwrap_err_term, seven);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "OwnResult::Err(7).unwrap_err() != 7 should be UNSAT — \
             qualified Err constructor gets accessor axiom (#1766)"
    );
}

#[test]
#[timeout(30000)]
fn test_qualified_ok_not_is_some_disjointness() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_some_qok = method_call(
        logic_fn_call("OwnResult::Ok", vec![int(1)]),
        "is_some",
        vec![],
    );
    let is_some_qok_term = encoder
        .encode_pure(&is_some_qok)
        .expect("OwnResult::Ok(1).is_some() should encode");

    encoder.assert_option_result_axioms();

    // Assert the semantic surface directly instead of depending on the
    // internal constructor placeholder family that happened to back it.
    encoder.assert_term(is_some_qok_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_some(OwnResult::Ok(1)) should be UNSAT — \
             qualified Ok gets cross-type disjointness axiom (#1766)"
    );
}

#[test]
#[timeout(30000)]
fn test_qualified_err_not_is_ok_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // OwnResult::Err(5) should not be Ok
    let is_ok_qerr = method_call(
        logic_fn_call("OwnResult::Err", vec![int(5)]),
        "is_ok",
        vec![],
    );

    let is_ok_term = encoder
        .encode_pure(&is_ok_qerr)
        .expect("OwnResult::Err(5).is_ok() should encode");
    encoder.assert_option_result_axioms();

    // Assert is_ok(OwnResult::Err(5)) — should be UNSAT
    encoder.assert_term(is_ok_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_ok(OwnResult::Err(5)) should be UNSAT — \
             qualified Err gets tester axiom (#1766)"
    );
}

/// Regression for #1787: `OwnResult::Ok(v).is_some()` must NOT trigger
/// `assert_is_option`. Before the fix, `is_result_constructor` only
/// matched unqualified `Ok`/`Err`, so qualified names like `OwnResult::Ok`
/// fell through and `assert_is_option` was spuriously called.
#[test]
#[timeout(30000)]
fn test_qualified_result_constructor_skips_is_option_assertion() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // OwnResult::Ok(1).is_some() — the receiver is a qualified Result constructor.
    // is_result_constructor must return true to skip the is_option assertion.
    let is_some_qok = method_call(
        logic_fn_call("OwnResult::Ok", vec![int(1)]),
        "is_some",
        vec![],
    );
    let result = encoder.encode_pure(&is_some_qok);
    assert!(
        result.is_ok(),
        "OwnResult::Ok(1).is_some() should encode without error: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "qualified Result constructor should not cause solver panic: {:?}",
        encoder.solver_panic_reason()
    );

    // Verify the same for is_none with qualified Err
    let is_none_qerr = method_call(
        logic_fn_call("OwnResult::Err", vec![int(99)]),
        "is_none",
        vec![],
    );
    let result2 = encoder.encode_pure(&is_none_qerr);
    assert!(
        result2.is_ok(),
        "OwnResult::Err(99).is_none() should encode without error: {result2:?}"
    );
}
