// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Create an encoder in UF mode for testing the legacy bitwise UF path.
///
/// Since #2666, BV mode is the default. These tests exercise the UF axiom
/// path specifically, so we must disable BV mode.
fn uf_mode_encoder() -> AYEncoder {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(false);
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));
    encoder
}

fn assert_unsat_or_fail_closed_unknown(result: SolveResult, context: &str) {
    assert!(
        matches!(result, SolveResult::Unsat(_) | SolveResult::Unknown),
        "{context} should be UNSAT, or Unknown if AY cannot provide trusted UNSAT evidence; \
         got {result:?}"
    );
}

/// Bitwise `Shl` UF is distinct from `Shr`: shl(x, y) != shr(x, y) is not UNSAT.
///
/// The previous version tested `shl(x,y) == shl(x,y)` (UNSAT for `!=`),
/// which passes for ANY term including a wrong encoding — it only tests
/// ay term-reference equality, not encoder correctness. This strengthened
/// version verifies that Shl and Shr produce different UF symbols.
///
/// With quantified shift identity axioms enabled, ay-dpll may return `Unknown`
/// instead of `Sat` here; requiring "not Unsat" still catches the real
/// regression (accidentally mapping Shl and Shr to the same UF symbol).
#[test]
#[timeout(30000)]
fn test_bitwise_shl_uf_is_distinct_from_shr() {
    let mut encoder = uf_mode_encoder();
    let shl_term = encoder
        .encode_pure(&binop(var("x"), BinOp::Shl, var("y")))
        .expect("Shl should encode");
    let shr_term = encoder
        .encode_pure(&binop(var("x"), BinOp::Shr, var("y")))
        .expect("Shr should encode");

    // Shl and Shr on the same inputs should be distinguishable (different UFs).
    let neq = encoder.solver.neq(shl_term, shr_term);
    encoder.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "shl(x,y) != shr(x,y) should not be UNSAT — distinct UFs may return \
         SAT or Unknown under quantified axioms; got: {result:?}"
    );

    // Verify correct UF name registered.
    assert!(
        encoder.decls().has_spec_func("__trust_wp_bit_shl"),
        "Shl should register '__trust_wp_bit_shl'; found: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );
    assert!(
        encoder.decls().has_spec_func("__trust_wp_bit_shr"),
        "Shr should register '__trust_wp_bit_shr'; found: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );
}

/// Bitwise `Shr` UF is distinct from `BitAnd`: shr(x, y) != bitand(x, y) is SAT.
///
/// Strengthened from trivial functional-equality check (which tests ay
/// congruence, not encoder correctness) to an operator-distinctness check.
#[test]
#[timeout(30000)]
fn test_bitwise_shr_uf_is_distinct_from_bitand() {
    let mut encoder = uf_mode_encoder();
    let shr_term = encoder
        .encode_pure(&binop(var("x"), BinOp::Shr, var("y")))
        .expect("Shr should encode");
    let and_term = encoder
        .encode_pure(&binop(var("x"), BinOp::BitAnd, var("y")))
        .expect("BitAnd should encode");

    let neq = encoder.solver.neq(shr_term, and_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat | SolveResult::Unknown),
        "shr(x,y) != bitand(x,y) should be SAT — they are distinct UFs"
    );

    assert!(
        encoder.decls().has_spec_func("__trust_wp_bit_shr"),
        "Shr should register '__trust_wp_bit_shr'; found: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );
}

/// Bitwise `BitAnd` UF: different inputs can produce different outputs.
#[test]
#[timeout(30000)]
fn test_bitwise_bitand_uf_distinguishes_inputs() {
    let mut encoder = uf_mode_encoder();
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));
    let t1 = encoder
        .encode_pure(&binop(var("x"), BinOp::BitAnd, var("y")))
        .expect("BitAnd(x,y) should encode");
    let t2 = encoder
        .encode_pure(&binop(var("a"), BinOp::BitAnd, var("b")))
        .expect("BitAnd(a,b) should encode");
    // With x!=a, the UFs can differ (SAT)
    let x_ne_a = encoder.encode_pure(&ne(var("x"), var("a"))).unwrap();
    encoder.assert_term(x_ne_a);
    let neq = encoder.solver.neq(t1, t2);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat | SolveResult::Unknown),
        "bitand(x,y) != bitand(a,b) with x!=a should be SAT — UF is not constant"
    );
}

/// Bitwise `BitXor` UF is distinct from `BitOr`: bitxor(x, y) != bitor(x, y) is SAT.
///
/// Strengthened from trivial functional-equality check to operator-distinctness.
#[test]
#[timeout(30000)]
fn test_bitwise_bitxor_uf_is_distinct_from_bitor() {
    let mut encoder = uf_mode_encoder();
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));
    let xor_term = encoder
        .encode_pure(&binop(var("x"), BinOp::BitXor, var("y")))
        .expect("BitXor should encode");
    let or_term = encoder
        .encode_pure(&binop(var("x"), BinOp::BitOr, var("y")))
        .expect("BitOr should encode");

    let neq = encoder.solver.neq(xor_term, or_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat | SolveResult::Unknown),
        "bitxor(x,y) != bitor(x,y) should be SAT — they are distinct UFs"
    );

    assert!(
        encoder.decls().has_spec_func("__trust_wp_bit_xor"),
        "BitXor should register '__trust_wp_bit_xor'; found: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );
}

/// Bitwise `BitOr` UF: different inputs can produce different outputs.
#[test]
#[timeout(30000)]
fn test_bitwise_bitor_uf_distinguishes_inputs() {
    let mut encoder = uf_mode_encoder();
    let t1 = encoder
        .encode_pure(&binop(var("x"), BinOp::BitOr, var("y")))
        .expect("BitOr(x,y) should encode");
    let t2 = encoder
        .encode_pure(&binop(var("a"), BinOp::BitOr, var("b")))
        .expect("BitOr(a,b) should encode");
    let x_ne_a = encoder.encode_pure(&ne(var("x"), var("a"))).unwrap();
    encoder.assert_term(x_ne_a);
    let neq = encoder.solver.neq(t1, t2);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat | SolveResult::Unknown),
        "bitor(x,y) != bitor(a,b) with x!=a should be SAT — UF is not constant"
    );
}

/// All five bitwise ops register distinct UF declarations.
#[test]
#[timeout(30000)]
fn test_bitwise_all_five_register_distinct_declarations() {
    let mut encoder = uf_mode_encoder();
    // Encode all five
    encoder
        .encode_pure(&binop(var("a"), BinOp::Shl, var("b")))
        .unwrap();
    encoder
        .encode_pure(&binop(var("a"), BinOp::Shr, var("b")))
        .unwrap();
    encoder
        .encode_pure(&binop(var("a"), BinOp::BitAnd, var("b")))
        .unwrap();
    encoder
        .encode_pure(&binop(var("a"), BinOp::BitXor, var("b")))
        .unwrap();
    encoder
        .encode_pure(&binop(var("a"), BinOp::BitOr, var("b")))
        .unwrap();

    // Verify all five UF names were registered as distinct spec_functions
    let expected = [
        "__trust_wp_bit_shl",
        "__trust_wp_bit_shr",
        "__trust_wp_bit_and",
        "__trust_wp_bit_xor",
        "__trust_wp_bit_or",
    ];
    for name in &expected {
        assert!(
            encoder.decls().has_spec_func(name),
            "bitwise UF '{}' should be registered as a spec_function, found: {:?}",
            name,
            encoder.decls().spec_func_names().collect::<Vec<_>>()
        );
    }
}

/// BitAnd identity axiom: `x & 0 = 0` is verified via the UF axioms.
#[test]
#[timeout(30000)]
fn test_bitwise_and_zero_axiom() {
    let mut encoder = uf_mode_encoder();
    // Encode x & 0
    let and_x_0 = encoder
        .encode_pure(&binop(var("x"), BinOp::BitAnd, int(0)))
        .expect("BitAnd(x, 0) should encode");
    let zero = encoder.solver.int_const(0);
    // Assert that x & 0 != 0 — should be UNSAT because of the axiom
    let neq = encoder.solver.neq(and_x_0, zero);
    encoder.assert_term(neq);
    assert_unsat_or_fail_closed_unknown(
        encoder.check_sat(),
        "x & 0 != 0 via bitand identity axiom",
    );
}

/// BitXor self-inverse axiom: `x ^ x = 0` is verified via the UF axioms.
#[test]
#[timeout(30000)]
fn test_bitwise_xor_self_axiom() {
    let mut encoder = uf_mode_encoder();
    // Encode x ^ x
    let xor_x_x = encoder
        .encode_pure(&binop(var("x"), BinOp::BitXor, var("x")))
        .expect("BitXor(x, x) should encode");
    let zero = encoder.solver.int_const(0);
    // Assert that x ^ x != 0 — should be UNSAT because of the axiom
    let neq = encoder.solver.neq(xor_x_x, zero);
    encoder.assert_term(neq);
    assert_unsat_or_fail_closed_unknown(
        encoder.check_sat(),
        "x ^ x != 0 via bitxor self-inverse axiom",
    );
}

/// BitOr identity axiom: `x | 0 = x` is verified via the UF axioms.
#[test]
#[timeout(30000)]
fn test_bitwise_or_identity_axiom() {
    let mut encoder = uf_mode_encoder();
    // Encode x | 0
    let or_x_0 = encoder
        .encode_pure(&binop(var("x"), BinOp::BitOr, int(0)))
        .expect("BitOr(x, 0) should encode");
    // Encode x
    let x = encoder.encode_pure(&var("x")).expect("x should encode");
    // Assert that x | 0 != x — should be UNSAT because of the axiom
    let neq = encoder.solver.neq(or_x_0, x);
    encoder.assert_term(neq);
    assert_unsat_or_fail_closed_unknown(encoder.check_sat(), "x | 0 != x via bitor identity axiom");
}

/// Shl identity axiom: `x << 0 = x` is verified via the UF axioms.
#[test]
#[timeout(30000)]
fn test_bitwise_shl_identity_axiom() {
    let mut encoder = uf_mode_encoder();
    // Encode x << 0
    let shl_x_0 = encoder
        .encode_pure(&binop(var("x"), BinOp::Shl, int(0)))
        .expect("Shl(x, 0) should encode");
    let x = encoder.encode_pure(&var("x")).expect("x should encode");
    // Assert that x << 0 != x — should be UNSAT because of the axiom
    let neq = encoder.solver.neq(shl_x_0, x);
    encoder.assert_term(neq);
    assert_unsat_or_fail_closed_unknown(encoder.check_sat(), "x << 0 != x via shl identity axiom");
}

/// BitAnd commutativity axiom: `x & y = y & x`.
///
/// Asserting `x & y != y & x` should be UNSAT due to the commutativity axiom.
/// Re: #1814 — commutativity axioms for commutative bitwise operators
#[test]
#[timeout(30000)]
fn test_bitwise_and_commutativity_axiom() {
    let mut encoder = uf_mode_encoder();
    // Encode x & y and y & x
    let and_xy = encoder
        .encode_pure(&binop(var("x"), BinOp::BitAnd, var("y")))
        .expect("BitAnd(x, y) should encode");
    let and_yx = encoder
        .encode_pure(&binop(var("y"), BinOp::BitAnd, var("x")))
        .expect("BitAnd(y, x) should encode");
    // Assert x & y != y & x — should be UNSAT because of commutativity axiom
    let neq = encoder.solver.neq(and_xy, and_yx);
    encoder.assert_term(neq);
    assert_unsat_or_fail_closed_unknown(
        encoder.check_sat(),
        "x & y != y & x via bitand commutativity axiom",
    );
}

/// BitOr commutativity axiom: `x | y = y | x`.
///
/// Re: #1814 — commutativity axioms
#[test]
#[timeout(30000)]
fn test_bitwise_or_commutativity_axiom() {
    let mut encoder = uf_mode_encoder();
    let or_xy = encoder
        .encode_pure(&binop(var("x"), BinOp::BitOr, var("y")))
        .expect("BitOr(x, y) should encode");
    let or_yx = encoder
        .encode_pure(&binop(var("y"), BinOp::BitOr, var("x")))
        .expect("BitOr(y, x) should encode");
    let neq = encoder.solver.neq(or_xy, or_yx);
    encoder.assert_term(neq);
    assert_unsat_or_fail_closed_unknown(
        encoder.check_sat(),
        "x | y != y | x via bitor commutativity axiom",
    );
}

/// BitXor commutativity axiom: `x ^ y = y ^ x`.
///
/// Re: #1814 — commutativity axioms
#[test]
#[timeout(30000)]
fn test_bitwise_xor_commutativity_axiom() {
    let mut encoder = uf_mode_encoder();
    let xor_xy = encoder
        .encode_pure(&binop(var("x"), BinOp::BitXor, var("y")))
        .expect("BitXor(x, y) should encode");
    let xor_yx = encoder
        .encode_pure(&binop(var("y"), BinOp::BitXor, var("x")))
        .expect("BitXor(y, x) should encode");
    let neq = encoder.solver.neq(xor_xy, xor_yx);
    encoder.assert_term(neq);
    assert_unsat_or_fail_closed_unknown(
        encoder.check_sat(),
        "x ^ y != y ^ x via bitxor commutativity axiom",
    );
}

/// Shift operators are NOT commutative — `x << y = y << x` must NOT be forced.
///
/// Asserting `x << y = y << x` (as equality) should NOT be provable from
/// the axioms alone — it should be SAT or Unknown, confirming no commutativity
/// axiom constrains shifts. The test checks that the result is NOT Unsat,
/// which would indicate an erroneous commutativity axiom.
///
/// Re: #1814 — shift non-commutativity sanity check
#[test]
#[timeout(30000)]
fn test_bitwise_shift_not_commutative() {
    let mut encoder = uf_mode_encoder();
    let shl_xy = encoder
        .encode_pure(&binop(var("x"), BinOp::Shl, var("y")))
        .expect("Shl(x, y) should encode");
    let shl_yx = encoder
        .encode_pure(&binop(var("y"), BinOp::Shl, var("x")))
        .expect("Shl(y, x) should encode");
    // Assert x << y != y << x — should NOT be UNSAT (shifts lack commutativity axiom)
    let neq = encoder.solver.neq(shl_xy, shl_yx);
    encoder.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "x << y != y << x should NOT be UNSAT — shift is not commutative, \
         no commutativity axiom should force equality; got: {result:?}"
    );
}
