// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
#[test]
#[timeout(30000)]
fn test_encode_bool_const() {
    let mut encoder = AYEncoder::new();
    let t = encoder.solver.bool_const(true);
    let f = encoder.solver.bool_const(false);

    // Semantic: true AND NOT(false) should be SAT
    encoder.solver.assert_term(t);
    let not_f = encoder.solver.not(f);
    encoder.solver.assert_term(not_f);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "true AND NOT(false) should be SAT"
    );

    // Semantic: true AND false should be UNSAT
    let mut encoder2 = AYEncoder::new();
    let t2 = encoder2.solver.bool_const(true);
    let f2 = encoder2.solver.bool_const(false);
    encoder2.solver.assert_term(t2);
    encoder2.solver.assert_term(f2);
    assert!(
        matches!(encoder2.check_sat(), SolveResult::Unsat(_)),
        "true AND false should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_int_const() {
    let mut encoder = AYEncoder::new();
    let zero = encoder.solver.int_const(0);
    let pos = encoder.solver.int_const(42);
    let neg = encoder.solver.int_const(-17);

    // Semantic: 0 != 42 (distinct constants)
    let zero_neq_pos = encoder.solver.neq(zero, pos);
    encoder.solver.assert_term(zero_neq_pos);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "0 != 42 should be SAT"
    );

    // Semantic: 42 + (-17) == 25
    let sum = encoder.solver.add(pos, neg);
    let twenty_five = encoder.solver.int_const(25);
    let sum_neq_25 = encoder.solver.neq(sum, twenty_five);
    encoder.solver.assert_term(sum_neq_25);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "42 + (-17) != 25 should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_simple_comparison() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver.declare_const("x", Sort::Int);
    let zero = encoder.solver.int_const(0);
    let x_gt_zero = encoder.solver.gt(x, zero);
    encoder.solver.assert_term(x_gt_zero);

    // Should be SAT (x can be positive)
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "x > 0 should be SAT (x can be any positive integer)"
    );
}

#[test]
#[timeout(30000)]
#[allow(clippy::similar_names)] // x_gt_zero/x_lt_zero are intentionally parallel
fn test_encode_unsatisfiable() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver.declare_const("x", Sort::Int);
    let zero = encoder.solver.int_const(0);

    // x > 0 AND x < 0 is unsatisfiable
    let x_gt_zero = encoder.solver.gt(x, zero);
    let x_lt_zero = encoder.solver.lt(x, zero);
    encoder.solver.assert_term(x_gt_zero);
    encoder.solver.assert_term(x_lt_zero);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x > 0 AND x < 0 should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_pure_var() {
    let mut encoder = AYEncoder::new();
    let expr = var("x");
    let term = encoder.encode_pure(&expr).unwrap();

    // Same variable should return same term
    let term2 = encoder.encode_pure(&expr).unwrap();
    assert_eq!(
        term, term2,
        "encoding the same variable twice should return the same SMT term"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_pure_var_reuses_existing_datatype_sort_when_unannotated() {
    let mut encoder = AYEncoder::new();
    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };

    let declared = encoder
        .get_or_declare_var("call_56", Sort::Datatype(option_int))
        .expect("datatype declaration should succeed");
    let encoded = encoder
        .encode_pure(&var("call_56"))
        .expect("unannotated var should reuse existing datatype sort");

    assert_eq!(
        declared, encoded,
        "unannotated var should reuse the existing datatype sort term"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_pure_binop() {
    let mut encoder = AYEncoder::new();
    let expr = add(var("x"), int(1)); // x + 1
    let term = encoder.encode_pure(&expr).unwrap();

    // Semantic: when x = 5, x + 1 = 6
    let x = *encoder.vars_for_test().get("x").unwrap();
    let five = encoder.solver.int_const(5);
    let six = encoder.solver.int_const(6);
    let x_eq_5 = encoder.solver.eq(x, five);
    let term_eq_6 = encoder.solver.eq(term, six);
    encoder.assert_term(x_eq_5);
    encoder.assert_term(term_eq_6);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "x=5, x+1=6 should be SAT"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_pure_binop_ne() {
    let mut encoder = AYEncoder::new();
    let expr = ne(var("x"), var("y")); // x != y
    let term = encoder.encode_pure(&expr).unwrap();

    // Semantic: x != y should be UNSAT when x == y
    let x = *encoder.vars_for_test().get("x").unwrap();
    let y = *encoder.vars_for_test().get("y").unwrap();
    let x_eq_y = encoder.solver.eq(x, y);
    encoder.assert_term(x_eq_y); // force x == y
    encoder.assert_term(term); // assert x != y
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x == y AND x != y should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_pure_bitwise_binops_use_uf_fallback() {
    let cases = [
        ("shl", BinOp::Shl, "__trust_wp_bit_shl"),
        ("shr", BinOp::Shr, "__trust_wp_bit_shr"),
        ("bitand", BinOp::BitAnd, "__trust_wp_bit_and"),
        ("bitxor", BinOp::BitXor, "__trust_wp_bit_xor"),
        ("bitor", BinOp::BitOr, "__trust_wp_bit_or"),
    ];

    for (name, op, expected_uf) in cases {
        let mut encoder = AYEncoder::new();
        encoder.set_bitwise_proof_mode(false); // Test legacy UF path
        let expr = PureExpr::BinOp(Arc::new(int(5)), op, Arc::new(int(1)));
        let term1 = encoder.encode_pure(&expr).unwrap();
        let term2 = encoder.encode_pure(&expr).unwrap();

        // UF fallback must still be deterministic for identical inputs.
        let eq_self = encoder.solver.eq(term1, term2);
        let neq_self = encoder.solver.not(eq_self);
        encoder.assert_term(neq_self);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "{name} fallback should be deterministic for same arguments"
        );

        // Verify the expected UF name was registered in the declaration state.
        assert!(
            encoder.decls().has_spec_func(expected_uf),
            "{name}: expected UF '{expected_uf}' not found in spec_functions; \
             registered: {:?}",
            encoder.decls().spec_func_names().collect::<Vec<_>>()
        );
    }
}
