// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── set with unexpected arity dispatch (#1667) ──────────────────────

/// `set` called with 0 args (unexpected arity) falls through to Int UF.
/// Verifies the guard-less "set" arm in method_call/mod.rs.
#[test]
#[timeout(30000)]
fn test_set_unexpected_arity_zero_args_falls_to_uf() {
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("m"), "set", vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("set() with 0 args should fall through to Int UF");

    // Verify it declared an Int UF with 1 param (receiver only)
    assert!(
        encoder.decls().has_logic_func("method_set_1_i"),
        "set() with 0 args should declare method_set_1_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );

    // Semantic check: the UF result participates in Int equalities
    let five = encoder.solver.int_const(5);
    let eq5 = encoder.solver.eq(term, five);
    encoder.assert_term(eq5);
    let three = encoder.solver.int_const(3);
    let neq3 = encoder.solver.neq(term, three);
    encoder.assert_term(neq3);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "set() UF == 5 AND != 3 should be SAT (non-trivial constraint on UF), got {result:?}"
    );
}

/// `set` called with 3 args (unexpected arity) falls through to Int UF.
#[test]
#[timeout(30000)]
fn test_set_unexpected_arity_three_args_falls_to_uf() {
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("m"), "set", vec![var("a"), var("b"), var("c")]);
    let _term = encoder
        .encode_pure(&expr)
        .expect("set() with 3 args should fall through to Int UF");

    // 4 params: receiver + 3 args, all Int-sorted
    assert!(
        encoder.decls().has_logic_func("method_set_4_i_i_i_i"),
        "set() with 3 args should declare method_set_4_i_i_i_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

/// `set` called with 1 arg (unexpected arity) falls through to Int UF.
#[test]
#[timeout(30000)]
fn test_set_unexpected_arity_one_arg_falls_to_uf() {
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("m"), "set", vec![var("k")]);
    let term = encoder
        .encode_pure(&expr)
        .expect("set() with 1 arg should fall through to Int UF");

    // 2 params: receiver + 1 arg
    assert!(
        encoder.decls().has_logic_func("method_set_2_i_i"),
        "set(k) should declare method_set_2_i_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );

    // Semantic: two calls with different args should be distinguishable
    let expr2 = method_call(var("m"), "set", vec![var("j")]);
    let term2 = encoder.encode_pure(&expr2).expect("set(j) should encode");

    // With k != j, the UF applications can be different (SAT)
    let k_neq_j = encoder
        .encode_pure(&ne(var("k"), var("j")))
        .expect("k != j");
    encoder.assert_term(k_neq_j);
    let terms_neq = encoder.solver.neq(term, term2);
    encoder.assert_term(terms_neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "set(k) != set(j) with k != j should be SAT — UF is not constant, got {result:?}"
    );
}
