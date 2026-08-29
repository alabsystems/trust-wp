// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// Nullary constructor equality: x == None AND x == Some(1) should be UNSAT.
#[test]
#[timeout(30000)]
fn test_nullary_constructor_equality_contradiction() {
    let mut encoder = AYEncoder::new_all();
    let dt = register_option_int(&mut encoder);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(dt));

    let x_none = eq(var("x"), logic_fn_call("OptionInt::None", vec![]));
    let x_some = eq(var("x"), logic_fn_call("OptionInt::Some", vec![int(1)]));

    let t1 = encoder.encode_pure(&x_none).unwrap();
    let t2 = encoder.encode_pure(&x_some).unwrap();
    encoder.assert_term(t1);
    encoder.assert_term(t2);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x == None AND x == Some(1) should be UNSAT"
    );
}

/// Reversed equality: `exists<v> Some(v) == x` should also detect the pattern.
#[test]
#[timeout(30000)]
fn test_reversed_equality_orientation() {
    let mut encoder = AYEncoder::new_all();
    let dt = register_option_int(&mut encoder);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(dt));

    // exists<v> Some(v) == x (reversed)
    let some_v = logic_fn_call("OptionInt::Some", vec![var("v")]);
    let body = eq(some_v, var("x"));
    let existential = exists("v", body);

    let term = encoder.encode_pure(&existential).unwrap();
    encoder.assert_term(term);

    // x == None creates contradiction.
    let x_none = eq(var("x"), logic_fn_call("OptionInt::None", vec![]));
    let t2 = encoder.encode_pure(&x_none).unwrap();
    encoder.assert_term(t2);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "exists<v> Some(v)==x AND x==None should be UNSAT"
    );
}
