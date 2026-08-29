// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// Integration: detection + elimination round-trip via encoder
// ════════════════════════════════════════════════════════════════════════

/// Nested exists: `exists<k> exists<v> x == Pair(k, v)` — encoder flattens
/// and eliminates. Single-constructor datatype → reconstruction equality.
#[test]
#[timeout(30000)]
fn test_nested_exists_pair_round_trip_sat() {
    let mut encoder = AYEncoder::new_all();
    let dt = pair_int_bool_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(dt));

    let body = eq(
        var("x"),
        logic_fn_call("PairIntBool::Pair", vec![var("k"), var("v")]),
    );
    let inner = exists("v", body);
    let outer = exists("k", inner);

    let term = encoder
        .encode_pure(&outer)
        .expect("nested exists Pair should encode");
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "single-constructor exists should be SAT"
    );
}

/// Forall Implies with multi-constructor datatype: `forall<v> x == Ok(v) ==> v > 0`.
/// With x = Ok(5), SAT. With x = Ok(-1), UNSAT.
#[test]
#[timeout(30000)]
fn test_forall_result_ok_sat_and_unsat() {
    // SAT case: x = Ok(5)
    {
        let mut encoder = AYEncoder::new_all();
        let dt = result_int_int_datatype();
        encoder.ensure_datatype_declared(&dt);
        encoder
            .var_sorts_mut_for_test()
            .insert("x".to_string(), Sort::Datatype(dt));

        let guard = eq(var("x"), logic_fn_call("OwnResult::Ok", vec![var("v")]));
        let body = implies(guard, gt(var("v"), int(0)));
        let universal = forall("v", body);

        let term = encoder.encode_pure(&universal).expect("forall Ok encode");
        encoder.assert_term(term);

        let ok5 = eq(var("x"), logic_fn_call("OwnResult::Ok", vec![int(5)]));
        let t5 = encoder.encode_pure(&ok5).unwrap();
        encoder.assert_term(t5);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::Sat,
            "forall<v> x==Ok(v)==>v>0 with x=Ok(5) should be SAT"
        );
    }

    // UNSAT case: x = Ok(-1)
    {
        let mut encoder = AYEncoder::new_all();
        let dt = result_int_int_datatype();
        encoder.ensure_datatype_declared(&dt);
        encoder
            .var_sorts_mut_for_test()
            .insert("x".to_string(), Sort::Datatype(dt));

        let guard = eq(var("x"), logic_fn_call("OwnResult::Ok", vec![var("v")]));
        let body = implies(guard, gt(var("v"), int(0)));
        let universal = forall("v", body);

        let term = encoder.encode_pure(&universal).expect("forall Ok encode");
        encoder.assert_term(term);

        let ok_neg = eq(var("x"), logic_fn_call("OwnResult::Ok", vec![int(-1)]));
        let t_neg = encoder.encode_pure(&ok_neg).unwrap();
        encoder.assert_term(t_neg);

        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "forall<v> x==Ok(v)==>v>0 with x=Ok(-1) should be UNSAT"
        );
    }
}

/// Exists with multi-constructor datatype: `exists<v> x == Ok(v)` AND `x == Err(0)`
/// should be UNSAT (x cannot be both Ok and Err).
#[test]
#[timeout(30000)]
fn test_exists_result_ok_and_err_contradiction() {
    let mut encoder = AYEncoder::new_all();
    let dt = result_int_int_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(dt));

    let exists_ok = exists(
        "v",
        eq(var("x"), logic_fn_call("OwnResult::Ok", vec![var("v")])),
    );
    let x_err = eq(var("x"), logic_fn_call("OwnResult::Err", vec![int(0)]));

    let t1 = encoder.encode_pure(&exists_ok).expect("exists Ok");
    let t2 = encoder.encode_pure(&x_err).expect("x Err");
    encoder.assert_term(t1);
    encoder.assert_term(t2);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "exists<v> x==Ok(v) AND x==Err(0) should be UNSAT"
    );
}
