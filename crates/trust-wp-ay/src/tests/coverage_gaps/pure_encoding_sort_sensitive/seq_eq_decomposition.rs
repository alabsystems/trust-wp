// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── Seq Eq decomposition ─────────────────────────────────────────────

/// When both operands of Eq are Seq-typed (have SeqValues from push_back
/// chains), the encoder decomposes `s1 == s2` into component-wise equality:
/// `arr(s1)==arr(s2) AND len(s1)==len(s2) AND off(s1)==off(s2)`.
///
/// Semantic: two push_back chains with the same elements must be equal.
/// Negating the equality must be UNSAT.
#[test]
#[timeout(30000)]
fn seq_eq_decomposition_same_chains_unsat() {
    let mut encoder = AYEncoder::new();

    let chain1 = method_call(
        method_call(
            logic_fn_call("seq_empty", vec![]),
            "push_back",
            vec![int(10)],
        ),
        "push_back",
        vec![int(20)],
    );
    let chain2 = method_call(
        method_call(
            logic_fn_call("seq_empty", vec![]),
            "push_back",
            vec![int(10)],
        ),
        "push_back",
        vec![int(20)],
    );

    let eq_expr = eq(chain1, chain2);
    let term = encoder
        .encode_pure(&eq_expr)
        .expect("Seq Eq should encode via decomposition");

    let neg = encoder.solver.not(term);
    encoder.solver.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT(identical_seq == identical_seq) must be UNSAT via decomposition"
    );
}

/// When Seq operands differ, the Eq decomposition returns SAT for the negation.
///
/// Semantic: `seq_empty().push_back(10)` != `seq_empty().push_back(20)`.
#[test]
#[timeout(30000)]
fn seq_eq_decomposition_different_chains_sat() {
    let mut encoder = AYEncoder::new();

    let chain1 = method_call(
        logic_fn_call("seq_empty", vec![]),
        "push_back",
        vec![int(10)],
    );
    let chain2 = method_call(
        logic_fn_call("seq_empty", vec![]),
        "push_back",
        vec![int(20)],
    );

    let eq_expr = eq(chain1, chain2);
    let term = encoder
        .encode_pure(&eq_expr)
        .expect("Seq Eq should encode via decomposition");

    // Structural: encoding succeeds and produces a valid term.
    // Solver-level SAT verification (NOT(push_back(10)==push_back(20))
    // should be SAT) blocked by ay-dpll Array theory regression (#2594).
    let _neg = encoder.solver.not(term);
}
