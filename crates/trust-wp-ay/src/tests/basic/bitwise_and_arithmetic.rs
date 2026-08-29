// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
/// Verify that different bitwise operators produce distinguishable UFs.
///
/// If the encoder accidentally mapped all bitwise ops to the same UF name,
/// the above test would still pass (same inputs → same output via congruence).
/// This test encodes two different bitwise ops and asserts they CAN differ. (#784)
#[test]
#[timeout(30000)]
fn test_encode_bitwise_ops_are_distinguishable() {
    let mut encoder = AYEncoder::new();
    encoder.set_bitwise_proof_mode(false); // Test legacy UF path
    let x = PureExpr::Var("x".to_string(), None);

    let and_expr = PureExpr::BinOp(Arc::new(x.clone()), BinOp::BitAnd, Arc::new(int(0xFF)));
    let or_expr = PureExpr::BinOp(Arc::new(x.clone()), BinOp::BitOr, Arc::new(int(0xFF)));
    let and_term = encoder.encode_pure(&and_expr).unwrap();
    let or_term = encoder.encode_pure(&or_expr).unwrap();

    // If BitAnd and BitOr share a UF, they would always return the same value
    // for the same arguments, making and_term == or_term a tautology.
    // With distinct UFs, and_term != or_term should be satisfiable.
    let neq = encoder.solver.neq(and_term, or_term);
    encoder.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "BitAnd(x, 0xFF) != BitOr(x, 0xFF) should be satisfiable \
         (different UFs can produce different values), got: {result:?}"
    );

    // Also verify both UFs are registered.
    assert!(
        encoder.decls().has_spec_func("__trust_wp_bit_and"),
        "BitAnd UF '__trust_wp_bit_and' should be registered in spec_functions; \
         found: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );
    assert!(
        encoder.decls().has_spec_func("__trust_wp_bit_or"),
        "BitOr UF '__trust_wp_bit_or' should be registered in spec_functions; \
         found: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );
}

/// Verify UF congruence: equal inputs to the same bitwise operator yield equal
/// outputs. This confirms the encoder uses proper UF declarations (where
/// congruence is a solver axiom) rather than ad-hoc term construction. (#982)
#[test]
#[timeout(30000)]
fn test_bitwise_uf_congruence() {
    let cases = [
        ("shl", BinOp::Shl),
        ("shr", BinOp::Shr),
        ("bitand", BinOp::BitAnd),
        ("bitxor", BinOp::BitXor),
        ("bitor", BinOp::BitOr),
    ];

    for (name, op) in cases {
        let mut encoder = AYEncoder::new();

        // Encode op(a, b) and op(a', b') using distinct variable names.
        let expr_ab = PureExpr::BinOp(Arc::new(var("a")), op, Arc::new(var("b")));
        let expr_ab2 = PureExpr::BinOp(Arc::new(var("a2")), op, Arc::new(var("b2")));
        let term_ab = encoder.encode_pure(&expr_ab).unwrap();
        let term_ab2 = encoder.encode_pure(&expr_ab2).unwrap();

        // Assert a == a' and b == b'.
        let a = *encoder.vars_for_test().get("a").unwrap();
        let a2 = *encoder.vars_for_test().get("a2").unwrap();
        let b = *encoder.vars_for_test().get("b").unwrap();
        let b2 = *encoder.vars_for_test().get("b2").unwrap();
        let a_eq = encoder.solver.eq(a, a2);
        let b_eq = encoder.solver.eq(b, b2);
        encoder.assert_term(a_eq);
        encoder.assert_term(b_eq);

        // Assert op(a,b) != op(a',b') — must be UNSAT by UF congruence.
        let neq = encoder.solver.neq(term_ab, term_ab2);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "{name}: a==a2 AND b==b2 AND {name}(a,b) != {name}(a2,b2) \
             should be UNSAT (UF congruence)"
        );
    }
}

#[test]
#[timeout(30000)]
fn test_encode_pure_binop_div() {
    // Test BinOp::Div encoding: x / 2 (integer division)
    let mut encoder = AYEncoder::new();
    let expr = div(var("x"), int(2));
    let term = encoder.encode_pure(&expr).unwrap();

    // Semantic: 10 / 2 == 5 (redundant with companion div tests but ensures this
    // test is not trivially passing)
    let x = *encoder.vars_for_test().get("x").unwrap();
    let ten = encoder.solver.int_const(10);
    let five = encoder.solver.int_const(5);
    let x_eq_10 = encoder.solver.eq(x, ten);
    let term_eq_5 = encoder.solver.eq(term, five);
    encoder.assert_term(x_eq_10);
    encoder.assert_term(term_eq_5);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "10 / 2 == 5 should be SAT"
    );
}

#[test]
#[timeout(30000)]
fn test_binop_div_semantic_correctness() {
    // Verify integer division semantics: 5 / 2 == 2 (not 2.5)
    let mut encoder = AYEncoder::new();

    // Create: 5 / 2
    let five_div_two = div(int(5), int(2));
    let div_term = encoder.encode_pure(&five_div_two).unwrap();

    // Assert: 5 / 2 != 2 (should be UNSAT since 5 / 2 == 2 in integer division)
    let two = encoder.solver.int_const(2);
    let eq_term = encoder.solver.eq(div_term, two);
    let neq = encoder.solver.not(eq_term);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Integer division should give 5 / 2 == 2"
    );
}

#[test]
#[timeout(30000)]
fn test_binop_div_negative_dividend() {
    // Verify negative dividend behavior: SMT-LIB div is Euclidean/floor division.
    // -5 div 2 = -3 (floor), not -2 (truncation toward zero).
    // SMT-LIB guarantees: 0 <= remainder < |divisor|, so (-5) mod 2 = 1.
    let mut encoder = AYEncoder::new();

    // Create: -5 / 2
    let neg_five_div_two = div(int(-5), int(2));
    let div_term = encoder.encode_pure(&neg_five_div_two).unwrap();

    // Assert: -5 / 2 != -3 (should be UNSAT since ay's int_div is SMT-LIB floor division)
    let neg_three = encoder.solver.int_const(-3);
    let eq_term = encoder.solver.eq(div_term, neg_three);
    let neq = encoder.solver.not(eq_term);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "ay integer division: -5 div 2 == -3 (SMT-LIB floor division)"
    );
}

#[test]
#[timeout(30000)]
fn test_binop_mod_semantic_correctness() {
    // Verify modulo semantics: 5 % 2 == 1
    let mut encoder = AYEncoder::new();

    // Create: 5 % 2
    let five_mod_two = mod_expr(int(5), int(2));
    let mod_term = encoder.encode_pure(&five_mod_two).unwrap();

    // Assert: 5 % 2 != 1 (should be UNSAT since 5 % 2 == 1)
    let one = encoder.solver.int_const(1);
    let eq_term = encoder.solver.eq(mod_term, one);
    let neq = encoder.solver.not(eq_term);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Modulo should give 5 % 2 == 1"
    );
}

#[test]
#[timeout(30000)]
fn test_binop_mod_negative_dividend() {
    // Verify negative dividend behavior: -5 mod 2 = 1
    let mut encoder = AYEncoder::new();

    // Create: -5 % 2
    let neg_five_mod_two = mod_expr(int(-5), int(2));
    let mod_term = encoder.encode_pure(&neg_five_mod_two).unwrap();

    let one = encoder.solver.int_const(1);
    let eq_term = encoder.solver.eq(mod_term, one);
    let neq = encoder.solver.not(eq_term);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "SMT-LIB modulo: -5 mod 2 == 1 (non-negative result)"
    );
}

#[test]
#[timeout(30000)]
fn test_binop_mod_larger_dividend() {
    // Verify modulo with larger dividend: 17 % 5 == 2
    let mut encoder = AYEncoder::new();

    let seventeen_mod_five = mod_expr(int(17), int(5));
    let mod_term = encoder.encode_pure(&seventeen_mod_five).unwrap();

    let two = encoder.solver.int_const(2);
    let eq_term = encoder.solver.eq(mod_term, two);
    let neq = encoder.solver.not(eq_term);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Modulo should give 17 % 5 == 2"
    );
}

// ── Truncated machine div/mod (Rust signed `/`/`%`) — sort-aware fix ──────────
//
// `BinOp::DivTrunc`/`RemTrunc` model Rust's signed `/`/`%` (TRUNCATED toward
// zero), kept DISTINCT from `BinOp::Div`/`Mod` (Euclidean — for mathematical
// `Int`, unsigned, wrapping, `rem_euclid`, and the contract `%`).
// See trust-wp-divmod-semantics.

/// True iff `expr == expected` is PROVED (its negation is Unsat).
fn proved_ground_int_eq(expr: &PureExpr, expected: i64) -> bool {
    let mut encoder = AYEncoder::new();
    let t = encoder.encode_pure(expr).unwrap();
    let exp = encoder.solver.int_const(expected);
    let eq_term = encoder.solver.eq(t, exp);
    let neq = encoder.solver.not(eq_term);
    encoder.solver.assert_term(neq);
    matches!(encoder.check_sat(), SolveResult::Unsat(_))
}

/// True iff Bool `goal` is PROVED under `premises`.
fn proved_under(premises: &[PureExpr], goal: &PureExpr) -> bool {
    let mut encoder = AYEncoder::new();
    for p in premises {
        let pt = encoder.encode_pure(p).unwrap();
        encoder.solver.assert_term(pt);
    }
    let g = encoder.encode_pure(goal).unwrap();
    let ng = encoder.solver.not(g);
    encoder.solver.assert_term(ng);
    matches!(encoder.check_sat(), SolveResult::Unsat(_))
}

#[test]
#[timeout(30000)]
fn divtrunc_truncates_toward_zero_all_signs() {
    for (a, b, e) in [
        (-7, 2, -3),
        (-7, -2, 3),
        (7, -2, -3),
        (7, 2, 3),
        (-1, 5, 0),
        (-1, 2, 0),
    ] {
        assert!(
            proved_ground_int_eq(&div_trunc(int(a), int(b)), e),
            "DivTrunc: {a} / {b} should truncate toward zero to {e}"
        );
    }
}

#[test]
#[timeout(30000)]
fn remtrunc_takes_sign_of_dividend_all_signs() {
    for (a, b, e) in [
        (-1, 5, -1),
        (-7, 2, -1),
        (-7, -2, -1),
        (7, -2, 1),
        (7, 2, 1),
        (5, 3, 2),
    ] {
        assert!(
            proved_ground_int_eq(&rem_trunc(int(a), int(b)), e),
            "RemTrunc: {a} % {b} should be {e} (sign of dividend)"
        );
    }
}

#[test]
#[timeout(30000)]
fn euclidean_div_mod_unchanged_for_negatives() {
    // The sort-aware fix leaves BinOp::Div/Mod EUCLIDEAN (mathematical Int,
    // unsigned, wrapping, and rem_euclid all depend on this).
    assert!(
        proved_ground_int_eq(&div(int(-7), int(2)), -4),
        "Div stays Euclidean: -7 div 2 == -4"
    );
    assert!(
        proved_ground_int_eq(&mod_expr(int(-1), int(5)), 4),
        "Mod stays Euclidean: -1 mod 5 == 4"
    );
    assert!(
        proved_ground_int_eq(&mod_expr(int(-5), int(2)), 1),
        "Mod stays Euclidean: -5 mod 2 == 1"
    );
}

#[test]
#[timeout(30000)]
fn truncated_differs_from_euclidean_on_negatives() {
    assert!(proved_ground_int_eq(&div_trunc(int(-7), int(2)), -3)); // truncated
    assert!(proved_ground_int_eq(&div(int(-7), int(2)), -4)); // euclidean
    assert!(proved_ground_int_eq(&rem_trunc(int(-1), int(5)), -1)); // truncated
    assert!(proved_ground_int_eq(&mod_expr(int(-1), int(5)), 4)); // euclidean
}

#[test]
#[timeout(30000)]
fn remtrunc_soundness_no_false_nonneg() {
    // SOUNDNESS: the demonstrated false-accept must be gone. Truncated `-1 % 5`
    // is -1 (negative), NOT the Euclidean 4.
    assert!(
        !proved_ground_int_eq(&rem_trunc(int(-1), int(5)), 4),
        "must NOT prove -1 %trunc 5 == 4"
    );
    assert!(
        proved_ground_int_eq(&rem_trunc(int(-1), int(5)), -1),
        "must prove -1 %trunc 5 == -1"
    );
}

/// The symbolic-divisor truncated quotient must be PINNED, not free.
///
/// `__trust_wp_int_div_trunc` used to carry no axiom at all when the divisor
/// was not a literal, so `a / b` for symbolic `b` was an arbitrary integer and
/// nothing about it could be proved — not even `(a / b) * b <= a` for
/// `a >= 0, b >= 1`. The defining identity
/// `b != 0 ==> a == nlmul(b, a /trunc b) + a %trunc b` closes that, sharing the
/// truncated remainder UF so `/` and `%` agree on the same operands.
#[test]
#[timeout(30000)]
fn divtrunc_symbolic_keystone_and_soundness() {
    let prem = [ge(var("n"), int(0)), ge(var("m"), int(1))];

    // The keystone: truncation never overshoots the dividend.
    assert!(
        proved_under(
            &prem,
            &le(mul(div_trunc(var("n"), var("m")), var("m")), var("n"))
        ),
        "n>=0, m>=1 ==> (n /trunc m) * m <= n"
    );

    // The div/mod identity, which only holds because both share `rem_trunc`.
    assert!(
        proved_under(
            &prem,
            &eq(
                var("n"),
                add(
                    mul(div_trunc(var("n"), var("m")), var("m")),
                    rem_trunc(var("n"), var("m"))
                )
            )
        ),
        "n>=0, m>=1 ==> n == (n /trunc m) * m + (n %trunc m)"
    );

    // SOUNDNESS: truncation LOSES the remainder, so exactness must NOT follow.
    // If this ever starts proving, the identity has been over-strengthened.
    assert!(
        !proved_under(
            &prem,
            &eq(mul(div_trunc(var("n"), var("m")), var("m")), var("n"))
        ),
        "must NOT prove (n /trunc m) * m == n — 7/2*2 is 6, not 7"
    );

    // SOUNDNESS: the quotient is not bounded below by the dividend.
    assert!(
        !proved_under(&prem, &ge(div_trunc(var("n"), var("m")), var("n"))),
        "must NOT prove n /trunc m >= n"
    );

    // SOUNDNESS: nothing may be concluded when the divisor can be zero, which
    // is the guard the identity is asserted under.
    assert!(
        !proved_under(
            &[ge(var("n"), int(0))],
            &le(mul(div_trunc(var("n"), var("m")), var("m")), var("n"))
        ),
        "must NOT prove the keystone without a nonzero divisor"
    );
}

/// The quotient itself must be bounded, not only its product.
///
/// The defining identity pins the quotient only THROUGH the opaque `nlmul`
/// product, so with that alone `0 / 1 == 3` stayed a model — and
/// `requires(a == 0 && b > 0) ensures(result == 0)` came back FAILED with a
/// counterexample, which is a verifier calling correct code wrong. The linear
/// sign/magnitude bounds close it for every sign combination.
#[test]
#[timeout(30000)]
fn divtrunc_symbolic_quotient_is_bounded_in_every_sign_case() {
    let pos_divisor = [ge(var("m"), int(1))];

    // a >= 0, b > 0  ==>  0 <= q <= a   (the case that used to report FAILED)
    let nonneg = [ge(var("n"), int(0)), ge(var("m"), int(1))];
    assert!(
        proved_under(&nonneg, &ge(div_trunc(var("n"), var("m")), int(0))),
        "n>=0, m>=1 ==> n /trunc m >= 0"
    );
    assert!(
        proved_under(&nonneg, &le(div_trunc(var("n"), var("m")), var("n"))),
        "n>=0, m>=1 ==> n /trunc m <= n"
    );

    // a <= 0, b > 0  ==>  a <= q <= 0
    let nonpos = [le(var("n"), int(0)), ge(var("m"), int(1))];
    assert!(
        proved_under(&nonpos, &le(div_trunc(var("n"), var("m")), int(0))),
        "n<=0, m>=1 ==> n /trunc m <= 0"
    );
    assert!(
        proved_under(&nonpos, &ge(div_trunc(var("n"), var("m")), var("n"))),
        "n<=0, m>=1 ==> n /trunc m >= n"
    );

    // a >= 0, b < 0  ==>  -a <= q <= 0
    let neg_divisor = [ge(var("n"), int(0)), le(var("m"), int(-1))];
    assert!(
        proved_under(&neg_divisor, &le(div_trunc(var("n"), var("m")), int(0))),
        "n>=0, m<=-1 ==> n /trunc m <= 0"
    );

    // SOUNDNESS: the bounds are not equalities. `7 /trunc 2` is 3, not 7 and
    // not 0, so neither endpoint may be provable in general.
    assert!(
        !proved_under(&nonneg, &eq(div_trunc(var("n"), var("m")), var("n"))),
        "must NOT prove n /trunc m == n"
    );
    assert!(
        !proved_under(&nonneg, &eq(div_trunc(var("n"), var("m")), int(0))),
        "must NOT prove n /trunc m == 0"
    );
    // SOUNDNESS: with no constraint on the dividend's sign, neither bound holds.
    assert!(
        !proved_under(&pos_divisor, &ge(div_trunc(var("n"), var("m")), int(0))),
        "must NOT prove the quotient is non-negative for a possibly-negative dividend"
    );
}

#[test]
#[timeout(30000)]
fn remtrunc_symbolic_keystone_and_soundness() {
    let prem = [ge(var("n"), int(0)), ge(var("m"), int(1))];
    assert!(
        proved_under(&prem, &lt(rem_trunc(var("n"), var("m")), var("m"))),
        "n>=0, m>=1 ==> n %trunc m < m"
    );
    assert!(
        proved_under(&prem, &ge(rem_trunc(var("n"), var("m")), int(0))),
        "n>=0, m>=1 ==> n %trunc m >= 0"
    );
    // SOUNDNESS: without n>=0, non-negativity must NOT be provable.
    assert!(
        !proved_under(
            &[ge(var("m"), int(1))],
            &ge(rem_trunc(var("n"), var("m")), int(0))
        ),
        "must NOT prove n %trunc m >= 0 for possibly-negative n"
    );
}
