// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── Bool-valued Ite encoding ─────────────────────────────────────────

/// When both branches of an Ite are Bool-sorted, the encoder uses
/// implication form `(c => t) AND (!c => e)` instead of SMT `ite`.
///
/// Semantic: `if (p) then true else false` is equivalent to `p`.
#[test]
#[timeout(30000)]
fn bool_ite_both_branches_bool_uses_implication_encoding() {
    let mut encoder = AYEncoder::new();

    let expr = ite(var("p"), bool_expr(true), bool_expr(false));
    let term = encoder
        .encode_pure(&expr)
        .expect("Bool-valued Ite should encode");

    let p = encoder.get_or_declare_var("p", Sort::Bool).expect("p");
    let t = encoder.solver.bool_const(true);
    let p_is_true = encoder.solver.eq(p, t);
    encoder.solver.assert_term(p_is_true);

    let neg_ite = encoder.solver.not(term);
    encoder.solver.assert_term(neg_ite);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "p=true AND NOT(ite(p, true, false)) must be UNSAT"
    );
}

/// Bool Ite with comparison branches: `ite(c, a > 0, b > 0)`.
#[test]
#[timeout(30000)]
fn bool_ite_comparison_branches_semantic() {
    let mut encoder = AYEncoder::new();

    let expr = ite(var("c"), gt(var("a"), int(0)), gt(var("b"), int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("Bool-valued Ite with comparison branches should encode");

    let c = encoder.get_or_declare_var("c", Sort::Bool).expect("c");
    encoder.solver.assert_term(c);

    let a = encoder.get_or_declare_var("a", Sort::Int).expect("a");
    let zero = encoder.solver.int_const(0);
    let a_gt = encoder.solver.gt(a, zero);
    encoder.solver.assert_term(a_gt);

    let neg = encoder.solver.not(term);
    encoder.solver.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "c=true AND a>0 AND NOT(ite(c, a>0, b>0)) must be UNSAT"
    );
}

/// Non-Bool Ite uses standard SMT ite.
#[test]
#[timeout(30000)]
fn non_bool_ite_uses_standard_smt_ite() {
    let mut encoder = AYEncoder::new();

    let expr = ite(var("c"), int(1), int(2));
    let term = encoder
        .encode_pure(&expr)
        .expect("Int-valued Ite should encode");

    let c = encoder.get_or_declare_var("c", Sort::Bool).expect("c");
    encoder.solver.assert_term(c);

    let one = encoder.solver.int_const(1);
    let neq = encoder.solver.neq(term, one);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "c=true AND ite(c,1,2)!=1 must be UNSAT"
    );
}
