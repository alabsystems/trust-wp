// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use ntest::timeout;

use super::*;

/// Multi-variable pattern: `exists<a, b> x == Pair(a, b)` with a 2-field
/// datatype should eliminate correctly to `is_Pair(x)`.
#[test]
#[timeout(30000)]
fn test_multi_variable_constructor_elimination() {
    let mut encoder = AYEncoder::new_all();

    // Register a Pair<Int, Int> datatype.
    let pair_dt = DatatypeSort {
        name: "PairIntInt".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "pair_fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "pair_snd".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    encoder.ensure_datatype_declared(&pair_dt);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(pair_dt.clone()));

    // exists<a> exists<b> x == Pair(a, b)
    // Note: we nest single-var existentials since trust-wp's AST uses single-var
    // quantifiers. The encoder's multi-var elimination handles this via
    // flatten_nested_existentials or falls back to normal quantifier encoding.
    let pair_ab = logic_fn_call("PairIntInt::Pair", vec![var("a"), var("b")]);
    let body = eq(var("x"), pair_ab);
    let inner = exists("b", body);
    let outer = exists("a", inner);

    let term = encoder
        .encode_pure(&outer)
        .expect("exists<a,b> x == Pair(a,b) should encode");
    encoder.assert_term(term);

    // The single-constructor datatype always satisfies is_Pair(x), so SAT.
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "exists<a,b> x == Pair(a,b) for single-constructor type should be SAT"
    );
}

/// Constructor argument with Deref wrapper: `exists<v> x == Some(*v)` should
/// still detect via `arg_is_qvar_reference` unwrapping Deref.
#[test]
#[timeout(30000)]
fn test_constructor_arg_through_deref_wrapper() {
    let mut encoder = AYEncoder::new_all();
    let dt = register_option_int(&mut encoder);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(dt));

    // exists<v> x == Some(Deref(v))
    let some_deref_v = logic_fn_call("OptionInt::Some", vec![deref(var("v"))]);
    let body = eq(var("x"), some_deref_v);
    let existential = exists("v", body);

    // The encoder should still detect the pattern because arg_is_qvar_reference
    // unwraps Deref. Whether elimination actually fires depends on the encoder's
    // handling of the Deref wrapper in the var_field_map — but encoding should
    // not crash.
    let result = encoder.encode_pure(&existential);
    assert!(
        result.is_ok(),
        "encoding exists<v> x == Some(Deref(v)) should not crash: {result:?}"
    );
}

/// 3-variable existential: `exists<a, b, c> x == Triple(a, b, c)` with a
/// 3-field datatype should eliminate to `is_Triple(x)`.
#[test]
#[timeout(30000)]
fn test_three_variable_constructor_elimination() {
    let mut encoder = AYEncoder::new_all();

    let triple_dt = DatatypeSort {
        name: "TripleInt".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Triple".to_string(),
            fields: vec![
                DatatypeField {
                    name: "triple_fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "triple_snd".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "triple_trd".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    encoder.ensure_datatype_declared(&triple_dt);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(triple_dt.clone()));

    // exists<a> exists<b> exists<c> x == Triple(a, b, c)
    let triple_abc = logic_fn_call("TripleInt::Triple", vec![var("a"), var("b"), var("c")]);
    let body = eq(var("x"), triple_abc);
    let inner2 = exists("c", body);
    let inner1 = exists("b", inner2);
    let outer = exists("a", inner1);

    let term = encoder
        .encode_pure(&outer)
        .expect("exists<a,b,c> x == Triple(a,b,c) should encode");
    encoder.assert_term(term);

    // Single-constructor datatype: is_Triple(x) is always true, so SAT.
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "exists<a,b,c> x == Triple(a,b,c) for single-constructor type should be SAT"
    );
}

/// Forall multi-variable: `forall<a, b> x == Pair(a, b) ==> a + b > 0` should
/// eliminate to `is_Pair(x) ==> sel_fst(x) + sel_snd(x) > 0`. With x = Pair(3, 5),
/// the consequent 3 + 5 > 0 holds, so SAT.
#[test]
#[timeout(30000)]
fn test_forall_multi_variable_constructor_elimination() {
    let mut encoder = AYEncoder::new_all();

    let pair_dt = DatatypeSort {
        name: "PairIntInt".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "pair_fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "pair_snd".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    encoder.ensure_datatype_declared(&pair_dt);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(pair_dt.clone()));

    // forall<a> forall<b> (x == Pair(a, b)) ==> (a + b > 0)
    let pair_ab = logic_fn_call("PairIntInt::Pair", vec![var("a"), var("b")]);
    let guard = eq(var("x"), pair_ab);
    let consequent = gt(add(var("a"), var("b")), int(0));
    let body = implies(guard, consequent);
    let inner = forall("b", body);
    let outer = forall("a", inner);

    let term = encoder
        .encode_pure(&outer)
        .expect("forall<a,b> x==Pair(a,b)==>a+b>0 should encode");
    encoder.assert_term(term);

    // Assert x == Pair(3, 5). sel_fst(x) + sel_snd(x) = 8 > 0, so SAT.
    let pair_3_5 = logic_fn_call("PairIntInt::Pair", vec![int(3), int(5)]);
    let x_eq = eq(var("x"), pair_3_5);
    let x_term = encoder.encode_pure(&x_eq).unwrap();
    encoder.assert_term(x_term);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "forall<a,b> x==Pair(a,b)==>a+b>0 with x=Pair(3,5) should be SAT"
    );
}

/// Forall multi-variable violation: with x = Pair(3, -5), a + b = -2 which is
/// not > 0, so the implication is violated and should be UNSAT.
#[test]
#[timeout(30000)]
fn test_forall_multi_variable_violation_unsat() {
    let mut encoder = AYEncoder::new_all();

    let pair_dt = DatatypeSort {
        name: "PairIntInt".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "pair_fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "pair_snd".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    encoder.ensure_datatype_declared(&pair_dt);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(pair_dt.clone()));

    // forall<a> forall<b> (x == Pair(a, b)) ==> (a + b > 0)
    let pair_ab = logic_fn_call("PairIntInt::Pair", vec![var("a"), var("b")]);
    let guard = eq(var("x"), pair_ab);
    let consequent = gt(add(var("a"), var("b")), int(0));
    let body = implies(guard, consequent);
    let inner = forall("b", body);
    let outer = forall("a", inner);

    let term = encoder.encode_pure(&outer).unwrap();
    encoder.assert_term(term);

    // Assert x == Pair(3, -5). sel_fst + sel_snd = -2, not > 0.
    let pair_neg = logic_fn_call("PairIntInt::Pair", vec![int(3), int(-5)]);
    let x_eq = eq(var("x"), pair_neg);
    let x_term = encoder.encode_pure(&x_eq).unwrap();
    encoder.assert_term(x_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "forall<a,b> x==Pair(a,b)==>a+b>0 with x=Pair(3,-5) should be UNSAT"
    );
}

/// Mixed-variable pattern: `exists<a, b, c> x == Pair(a, b) && c > 0 && c < 0`
/// where variable `c` does NOT appear in the constructor. The elimination must
/// not drop the contradictory `c` constraints when not all quantified variables
/// appear in the constructor. If mixed-variable elimination regressed to only
/// `is_Pair(x)`, this single-constructor datatype would become SAT, so UNSAT
/// here distinguishes the fallback path from unsound partial elimination.
#[test]
#[timeout(30000)]
fn test_mixed_variable_falls_back_to_normal_encoding() {
    let mut encoder = AYEncoder::new_all();

    let pair_dt = DatatypeSort {
        name: "PairIntInt".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "pair_fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "pair_snd".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    encoder.ensure_datatype_declared(&pair_dt);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Datatype(pair_dt.clone()));

    // exists<a> exists<b> exists<c> (x == Pair(a, b) && c > 0 && c < 0)
    // Variable c is not in the constructor, so elimination cannot fire for all 3 vars.
    let pair_ab = logic_fn_call("PairIntInt::Pair", vec![var("a"), var("b")]);
    let eq_pair = eq(var("x"), pair_ab);
    let c_positive = gt(var("c"), int(0));
    let c_negative = lt(var("c"), int(0));
    let body = and(eq_pair, and(c_positive, c_negative));
    let inner2 = exists("c", body);
    let inner1 = exists("b", inner2);
    let outer = exists("a", inner1);

    let term = encoder
        .encode_pure(&outer)
        .expect("mixed-variable pattern should encode without crashing");
    encoder.assert_term(term);

    // Single-constructor type means `is_Pair(x)` alone would be SAT, so UNSAT
    // proves the encoder preserved the contradictory `c` constraints.
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "mixed-variable exists<a,b,c> x==Pair(a,b) && c>0 && c<0 should be UNSAT, got {result:?}"
    );
}
