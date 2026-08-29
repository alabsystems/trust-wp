// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// None reconstruction via encoding path: when `x.is_some()` is encoded,
/// `is_option(x)` is asserted automatically (#1211). Combined with the
/// None reconstruction axiom, `!is_some(x) && x != None` becomes UNSAT.
///
/// Previously this was a documented gap (SAT). Now closed because
/// `encode_datatype_spec_method` asserts `is_option(receiver)` for
/// `is_some`/`is_none` calls, which activates the reconstruction axiom.
#[test]
#[timeout(30000)]
fn test_option_none_reconstruction_gap_closed() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode x.is_some() via the encoding path — this asserts is_option(x).
    let is_some_x = method_call(var("x"), "is_some", vec![]);
    let is_some_x_term = encoder
        .encode_pure(&is_some_x)
        .expect("x.is_some() should encode");

    let none_expr = logic_fn_call("None", vec![]);
    let none_term = encoder.encode_pure(&none_expr).expect("None should encode");

    encoder.assert_option_result_axioms();

    // Assert !is_some(x) && x != None
    let not_some_x = encoder.solver_mut().not(is_some_x_term);
    let x_term = encoder.encode_pure(&var("x")).expect("x should encode");
    let neq_none = {
        let solver = encoder.solver_mut();
        let eq = solver.eq(x_term, none_term);
        solver.not(eq)
    };
    let conjunction = encoder.solver_mut().and(not_some_x, neq_none);
    encoder.assert_term(conjunction);

    // UNSAT: is_option(x) + !is_some(x) triggers None reconstruction => x = None
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "!is_some(x) && x != None should be UNSAT — gap closed by #1211: \
             is_option(x) asserted during is_some encoding"
    );
}

/// Soundness guard: a native Result witness remains consistent with the
/// wrong-family Option tester.
///
/// The native stdlib transition keeps `Ok(42)` and `None` in distinct
/// carrier sorts, so the meaningful regression check here is that
/// `Ok(42)` can satisfy `is_ok` while also satisfying `!is_some`
/// without triggering any contradiction.
#[test]
#[timeout(30000)]
fn test_none_reconstruction_does_not_collapse_result_to_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode Ok(42) and both relevant datatype-spec methods.
    let ok_expr = logic_fn_call("Ok", vec![int(42)]);
    let is_ok_ok = method_call(ok_expr.clone(), "is_ok", vec![]);
    let is_some_ok = method_call(ok_expr.clone(), "is_some", vec![]);
    let is_ok_ok_term = encoder
        .encode_pure(&is_ok_ok)
        .expect("is_ok(Ok(42)) should encode");
    let is_some_ok_term = encoder
        .encode_pure(&is_some_ok)
        .expect("is_some(Ok(42)) should encode");

    encoder.assert_term(is_ok_ok_term);
    let not_is_some_ok = encoder.solver_mut().not(is_some_ok_term);
    encoder.assert_term(not_is_some_ok);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Ok(42) should remain consistent with !is_some even when None axioms \
             are loaded: got {result:?}"
    );
}

/// Native Option carriers still reconstruct `None` from `!is_some(x)`.
///
/// With `x : OptionInt`, `!x.is_some() && x != None` should be UNSAT
/// because the native datatype is fully covered by `Some(_) | None`.
#[test]
#[timeout(30000)]
fn test_option_none_reconstruction_with_native_option_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let none_expr = logic_fn_call("None", vec![]);
    let none_term = encoder.encode_pure(&none_expr).expect("None should encode");
    let none_sort = encoder.solver.get_sort(none_term);
    let x_name = "test_x_native_option";
    let x_term = encoder
        .get_or_declare_var(x_name, none_sort.clone())
        .expect("native option witness should declare");

    let is_some_x = method_call(var(x_name), "is_some", vec![]);
    let is_some_x_term = encoder
        .encode_pure(&is_some_x)
        .expect("x.is_some() should encode for native Option sort");

    encoder.assert_option_result_axioms();

    let not_some_x = encoder.solver_mut().not(is_some_x_term);
    encoder.assert_term(not_some_x);

    // Assert x != None
    let neq_none = {
        let solver = encoder.solver_mut();
        let eq = solver.eq(x_term, none_term);
        solver.not(eq)
    };
    encoder.assert_term(neq_none);

    // UNSAT: Option coverage plus !is_some(x) forces x = None.
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "!x.is_some() && x != None should be UNSAT for native Option carriers"
    );
}
