// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── detect_constructor_eq integration tests (via quantifier encoding) ──

/// Existential with constructor equality: `exists<v> x == Some(v)` should be
/// eliminated to `is_Some(x)` when the Option datatype is declared.
///
/// We test this by encoding the existential through the encoder's quantifier path
/// and verifying the semantic result: asserting `exists<v> x == Some(v)` and
/// then `x == None` should be UNSAT if elimination is correct.
#[test]
#[timeout(30000)]
fn test_detect_and_eliminate_exists_some_pattern() {
    let mut encoder = AYEncoder::new_all();
    let dt = register_option_int(&mut encoder);

    // Pre-seed x as OptionInt-sorted so the tester can fire.
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(dt.clone()));

    // Encode: exists<v> x == OptionInt::Some(v)
    let some_v = logic_fn_call("OptionInt::Some", vec![var("v")]);
    let body = eq(var("x"), some_v);
    let existential = exists("v", body);

    let term = encoder
        .encode_pure(&existential)
        .expect("exists<v> x == Some(v) should encode");
    encoder.assert_term(term);

    // Assert x == None to create contradiction — x can't be both Some and None.
    let none_x = eq(var("x"), logic_fn_call("OptionInt::None", vec![]));
    let none_term = encoder.encode_pure(&none_x).unwrap();
    encoder.assert_term(none_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "exists<v> x == Some(v) AND x == None should be UNSAT"
    );
}

/// Forall with constructor equality guard: `forall<v> x == Some(v) ==> P(v)`
/// should eliminate to `is_Some(x) ==> P(selector(x))`.
///
/// Semantic test: assert the forall, then assert x == Some(5). The eliminated
/// form should instantiate P to the selector's value (5), and with P(v) = (v > 0),
/// the result should be SAT.
#[test]
#[timeout(30000)]
fn test_detect_and_eliminate_forall_implies_some_pattern() {
    let mut encoder = AYEncoder::new_all();
    let dt = register_option_int(&mut encoder);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(dt.clone()));

    // Encode: forall<v> (x == OptionInt::Some(v)) ==> (v > 0)
    let some_v = logic_fn_call("OptionInt::Some", vec![var("v")]);
    let guard = eq(var("x"), some_v);
    let consequent = gt(var("v"), int(0));
    let body = implies(guard, consequent);
    let universal = forall("v", body);

    let term = encoder
        .encode_pure(&universal)
        .expect("forall<v> x==Some(v) ==> v>0 should encode");
    encoder.assert_term(term);

    // Assert x == Some(5). The eliminated form is: is_Some(x) ==> selector(x) > 0.
    // With x = Some(5), selector(x) = 5 > 0 is true, so SAT.
    let some_5 = logic_fn_call("OptionInt::Some", vec![int(5)]);
    let x_eq_5 = eq(var("x"), some_5);
    let term5 = encoder.encode_pure(&x_eq_5).unwrap();
    encoder.assert_term(term5);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "forall<v> x==Some(v)==>v>0 with x=Some(5) should be SAT"
    );
}

/// Forall with constructor equality guard that is violated: assert
/// `forall<v> x == Some(v) ==> v > 0` then `x == Some(-1)` should be UNSAT
/// because the consequent v > 0 fails for v = -1.
#[test]
#[timeout(30000)]
fn test_forall_implies_some_violated_consequent_unsat() {
    let mut encoder = AYEncoder::new_all();
    let dt = register_option_int(&mut encoder);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(dt));

    let some_v = logic_fn_call("OptionInt::Some", vec![var("v")]);
    let guard = eq(var("x"), some_v);
    let consequent = gt(var("v"), int(0));
    let body = implies(guard, consequent);
    let universal = forall("v", body);

    let term = encoder.encode_pure(&universal).unwrap();
    encoder.assert_term(term);

    // x == Some(-1): the consequent -1 > 0 is false.
    let some_neg1 = logic_fn_call("OptionInt::Some", vec![int(-1)]);
    let x_eq_neg1 = eq(var("x"), some_neg1);
    let term_neg1 = encoder.encode_pure(&x_eq_neg1).unwrap();
    encoder.assert_term(term_neg1);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "forall<v> x==Some(v)==>v>0 with x=Some(-1) should be UNSAT"
    );
}
