// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::SolveResult;

use super::*;
use crate::AYEncoder;

/// `map.get(k) && b` should encode without sort panic.
///
/// When `get` appears under `&&`, `encode_bool_context_operand` routes it
/// to `encode_bool_method_predicate` (Bool-sorted UF) instead of the
/// default Int-sorted `fmap_lookup` path. Without this, the `and(Int, Bool)`
/// call would cause a ay sort mismatch.
///
/// Strengthened from trivial unconstrained SAT (#1685): now verifies the
/// Bool term participates in Boolean reasoning via UNSAT contradiction.
#[test]
#[timeout(30000)]
fn bool_context_operand_get_under_and_encodes_as_bool() {
    let mut encoder = AYEncoder::new();

    // map.get(k) && true
    // `get` on a non-Seq receiver under `&&` should be redirected to
    // Bool-sorted predicate encoding.
    let expr = binop(
        method_call(var("map"), "get", vec![var("k")]),
        BinOp::And,
        bool_expr(true),
    );

    let term1 = encoder
        .encode_pure(&expr)
        .expect("get under && should encode without sort panic");
    let term2 = encoder
        .encode_pure(&expr)
        .expect("second encoding should succeed");

    // UNSAT dual: term AND NOT(term) must be UNSAT (Bool contradiction)
    encoder.solver.assert_term(term1);
    let neg = encoder.solver.not(term2);
    encoder.solver.assert_term(neg);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "map.get(k) && true AND NOT(map.get(k) && true) must be UNSAT, got: {result:?}"
    );
}

/// `map.get(k) ==> q` should encode with Bool-sorted get.
#[test]
#[timeout(30000)]
fn bool_context_operand_get_under_implies_encodes_as_bool() {
    let mut encoder = AYEncoder::new();

    // map.get(k) ==> false
    let implies_expr = binop(
        method_call(var("map"), "get", vec![var("k")]),
        BinOp::Implies,
        bool_expr(false),
    );
    // map.get(k) && true (forces Bool-context encoding for get)
    let get_bool_expr = binop(
        method_call(var("map"), "get", vec![var("k")]),
        BinOp::And,
        bool_expr(true),
    );

    let implies_term = encoder
        .encode_pure(&implies_expr)
        .expect("get under ==> should encode without sort panic");
    let get_bool_term = encoder
        .encode_pure(&get_bool_expr)
        .expect("get under && should encode as Bool context operand");

    // If both code paths route through Bool-context encoding, then
    // (get(k) && true) AND (get(k) ==> false) is contradictory.
    encoder.assert_term(get_bool_term);
    encoder.assert_term(implies_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Bool-context get under && and ==> should be logically consistent and contradictory here"
    );

    // Regression guard: Bool-context get should use method_get_* predicate, not fmap_lookup.
    assert!(
        encoder.decls().has_logic_func("method_get_2_i_i"),
        "Bool-context get should declare method_get_2_i_i"
    );
    assert!(
        !encoder.decls().has_spec_func("fmap_lookup"),
        "Bool-context get should not route through Int-valued fmap_lookup"
    );
}

/// Non-get method calls under `&&` fall through to normal encoding.
///
/// Strengthened from trivial SAT (#1685): now verifies the Bool encoding
/// by checking UNSAT when len==0 contradicts len>0.
#[test]
#[timeout(30000)]
fn bool_context_operand_non_get_method_uses_default_path() {
    let mut encoder = AYEncoder::new();

    // v.len() > 0 && true
    let expr = binop(
        gt(method_call(var("v"), "len", vec![]), int(0)),
        BinOp::And,
        bool_expr(true),
    );

    let and_term = encoder
        .encode_pure(&expr)
        .expect("non-get method under && should encode normally");

    // Assert the conjunction (forces len(v) > 0)
    encoder.solver.assert_term(and_term);

    // UNSAT dual: len(v) == 0 contradicts len(v) > 0
    let len_call = method_call(var("v"), "len", vec![]);
    let len_eq_0 = eq(len_call, int(0));
    let constraint = encoder
        .encode_pure(&len_eq_0)
        .expect("len == 0 should encode");
    encoder.solver.assert_term(constraint);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "(v.len() > 0 && true) AND v.len() == 0 must be UNSAT, got: {result:?}"
    );
}
