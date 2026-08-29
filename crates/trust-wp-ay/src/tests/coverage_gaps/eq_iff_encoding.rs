// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// `eq_or_iff` is now a compatibility wrapper over the native `eq_term`
/// helper, so Bool and Int equality both flow through solver equality while
/// retaining sort-repair/panic-isolation behavior (#1179).
#[test]
#[timeout(30000)]
fn test_eq_or_iff_bool_vs_int_sort_behavior() {
    let mut encoder = AYEncoder::new();

    // For Bool sort: equality between `true` and `false` must be UNSAT when asserted.
    let t = encoder.solver_mut().bool_const(true);
    let f = encoder.solver_mut().bool_const(false);
    let bool_eq = encoder.eq_or_iff(t, f, &Sort::Bool);
    encoder.assert_term(bool_eq);
    assert!(
        encoder.check_sat().is_unsat(),
        "eq_or_iff(true, false, Bool) must be UNSAT"
    );

    // Fresh encoder for Int sort test
    let mut encoder2 = AYEncoder::new();
    let a = encoder2
        .get_or_declare_var("a", Sort::Int)
        .expect("a should declare");
    let b = encoder2
        .get_or_declare_var("b", Sort::Int)
        .expect("b should declare");
    let int_eq = encoder2.eq_or_iff(a, b, &Sort::Int);
    encoder2.assert_term(int_eq);
    // a == b is SAT (both can be 0)
    assert!(
        encoder2.check_sat().is_sat(),
        "eq_or_iff(a, b, Int) must be SAT — standard eq with unconstrained vars"
    );
}

/// `eq_or_iff` with mismatched sorts (Int vs Seq(Int)) coerces (#2080)
/// the Int operand to a fresh unconstrained constant of the other sort,
/// preventing ay sort-mismatch panics. (#2077)
///
/// Before coercion: `eq_or_iff` would panic at `mk_eq` on sort mismatch.
/// After Unit-only coercion (#1663): panic caught, result = Unknown.
/// After generalized coercion (#2077): no panic, result is normal SAT/UNSAT.
#[test]
#[timeout(30000)]
fn test_eq_or_iff_sort_mismatch_coerced_no_panic() {
    let mut encoder = AYEncoder::new();

    let int_var = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("x should declare");

    let seq_sort = Sort::seq(Sort::Int);
    let seq_var = encoder
        .get_or_declare_var("s", seq_sort)
        .expect("s should declare");

    // eq_or_iff(Int, Seq, Int) — sort mismatch coerced by #2077.
    let eq_term = encoder.eq_or_iff(int_var, seq_var, &Sort::Int);

    // No panic should be recorded — coercion prevents the mismatch.
    assert!(
        encoder.solver_panic_reason().is_none(),
        "Sort coercion in eq_or_iff should prevent solver panic"
    );

    // check_sat should return a normal result (not Unknown from panic).
    encoder.assert_term(eq_term);
    let result = encoder.check_sat();
    assert!(
        !result.is_unknown(),
        "check_sat after sort coercion should not return Unknown, got: {result:?}"
    );
}

/// `eq_or_iff(p, p, Bool)` must remain a tautology.
#[test]
#[timeout(30000)]
fn test_eq_or_iff_bool_reflexive_is_tautology() {
    let mut encoder = AYEncoder::new();

    let p = encoder
        .get_or_declare_var("p", Sort::Bool)
        .expect("p should declare");

    // Equality of a term with itself is trivially true.
    let eq_term = encoder.eq_or_iff(p, p, &Sort::Bool);
    let negated = encoder.solver_mut().not(eq_term);
    encoder.assert_term(negated);

    assert!(
        encoder.check_sat().is_unsat(),
        "NOT(eq_or_iff(p, p, Bool)) must be UNSAT"
    );
}

/// `eq_or_iff(p, q, Bool)` must still reject disagreement.
#[test]
#[timeout(30000)]
fn test_eq_or_iff_bool_distinct_variables_constraining() {
    let mut encoder = AYEncoder::new();

    let p = encoder
        .get_or_declare_var("p", Sort::Bool)
        .expect("p should declare");
    let q = encoder
        .get_or_declare_var("q", Sort::Bool)
        .expect("q should declare");

    // Assert p ↔ q
    let iff_term = encoder.eq_or_iff(p, q, &Sort::Bool);
    encoder.assert_term(iff_term);

    // Also assert p = true
    let p2 = encoder
        .get_or_declare_var("p", Sort::Bool)
        .expect("p redeclare");
    let t = encoder.solver_mut().bool_const(true);
    let p_true = encoder.solver_mut().eq(p2, t);
    encoder.assert_term(p_true);

    // Also assert q = false
    let q2 = encoder
        .get_or_declare_var("q", Sort::Bool)
        .expect("q redeclare");
    let f = encoder.solver_mut().bool_const(false);
    let q_false = encoder.solver_mut().eq(q2, f);
    encoder.assert_term(q_false);

    assert!(
        encoder.check_sat().is_unsat(),
        "p=q AND p=true AND q=false must be UNSAT"
    );
}

/// `eq_or_iff` with Bool-vs-Int coerces Bool to Int via `ite(b,1,0)`,
/// preserving the boolean value as 0/1 instead of discarding it. (#2077)
///
/// Without this fix, Bool-vs-Int hit the generic Int→fresh path, which
/// would create a fresh unconstrained Bool constant, losing the boolean
/// value entirely.
#[test]
#[timeout(30000)]
fn test_eq_or_iff_bool_vs_int_coercion_preserves_value() {
    let mut encoder = AYEncoder::new();

    let bool_var = encoder
        .get_or_declare_var("b", Sort::Bool)
        .expect("b should declare");
    let int_var = encoder
        .get_or_declare_var("n", Sort::Int)
        .expect("n should declare");

    // eq_or_iff(Bool, Int, Int) — Bool→Int coercion via ite(b,1,0).
    let eq_term = encoder.eq_or_iff(bool_var, int_var, &Sort::Int);

    // No panic should occur — coercion handles the mismatch.
    assert!(
        encoder.solver_panic_reason().is_none(),
        "Bool vs Int coercion should prevent solver panic"
    );

    // Assert b=true, n=1, and b==n — this should be SAT because
    // ite(true,1,0) = 1 = n.
    let t = encoder.solver_mut().bool_const(true);
    let b_true = encoder.solver_mut().eq(bool_var, t);
    encoder.assert_term(b_true);
    let one = encoder.solver_mut().int_const(1);
    let n_one = encoder.solver_mut().eq(int_var, one);
    encoder.assert_term(n_one);
    encoder.assert_term(eq_term);

    let result = encoder.check_sat();
    assert!(
        result.is_sat(),
        "b=true, n=1, ite(b,1,0)==n should be SAT, got: {result:?}"
    );
}

/// Bool→Int coercion must use the *original* Bool variable, not a fresh
/// constant. With b=false and n=1, `ite(b,1,0)==n` is UNSAT because
/// ite(false,1,0)=0≠1. If coercion created a fresh unconstrained Bool, ay
/// could satisfy it by setting fresh=true, making this SAT — which would
/// be unsound. (#2077)
#[test]
#[timeout(30000)]
fn test_eq_or_iff_bool_int_coercion_uses_original_variable() {
    let mut encoder = AYEncoder::new();

    let bool_var = encoder
        .get_or_declare_var("b", Sort::Bool)
        .expect("b should declare");
    let int_var = encoder
        .get_or_declare_var("n", Sort::Int)
        .expect("n should declare");

    // Coerce Bool→Int via eq_or_iff.
    let eq_term = encoder.eq_or_iff(bool_var, int_var, &Sort::Int);

    // Assert b=false → ite(b,1,0)=0.
    let f = encoder.solver_mut().bool_const(false);
    let b_false = encoder.solver_mut().eq(bool_var, f);
    encoder.assert_term(b_false);

    // Assert n=1.
    let one = encoder.solver_mut().int_const(1);
    let n_one = encoder.solver_mut().eq(int_var, one);
    encoder.assert_term(n_one);

    // Assert the equality: ite(b,1,0)==n → ite(false,1,0)==1 → 0==1 → UNSAT.
    encoder.assert_term(eq_term);

    let result = encoder.check_sat();
    assert!(
        result.is_unsat(),
        "b=false, n=1, ite(b,1,0)==n must be UNSAT — coercion uses original b, \
         not a fresh constant. Got: {result:?}"
    );
}

// ── get_model success-path behavior (#1502 follow-up) ─────────────────

/// Successful `get_model()` calls must not set `solver_panic_reason`.
/// The panic path is validated in encoder/solver.rs unit tests using a
/// synthetic panic injection hook.
#[test]
#[timeout(30000)]
fn get_model_success_keeps_panic_reason_empty() {
    let mut encoder = AYEncoder::new();

    // Assert a nontrivial SAT formula and check through the raw solver so a
    // model is materialized; the encoder wrapper may short-circuit trivial SAT.
    let x = encoder.solver_mut().declare_const("model_x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_zero = encoder.solver_mut().gt(x, zero);
    encoder.assert_term(x_gt_zero);
    let result = encoder.solver_mut().check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "trivially true formula should be SAT"
    );

    // Verify no panic reason yet.
    assert!(
        encoder.solver_panic_reason().is_none(),
        "no panic should have occurred yet"
    );

    // get_model() on a valid SAT should return Some.
    let model = encoder.get_model();
    assert!(
        model.is_some(),
        "get_model after SAT on a valid formula should return Some"
    );

    // Successful model extraction should keep panic reason empty.
    assert!(
        encoder.solver_panic_reason().is_none(),
        "successful get_model call should not set panic reason"
    );
}

// ── Bool-context operand encoding coverage (#1647) ───────────────────

/// Bool-context fallback path: a bare variable under `&&` should be declared
/// as Bool on first use, without requiring pre-registered sort hints.
#[test]
#[timeout(30000)]
fn test_bool_context_operand_seeds_bool_hint_for_var() {
    let mut encoder = AYEncoder::new();

    // `flag && true` forces `flag` through encode_bool_context_operand.
    let expr = and(var("flag"), bool_expr(true));
    let _term = encoder
        .encode_pure(&expr)
        .expect("Bool-context variable should encode without sort mismatch");

    assert_eq!(
        encoder.var_sort("flag"),
        Some(&Sort::Bool),
        "encode_bool_context_operand must seed Bool sort for bare vars in Bool contexts"
    );
}

/// Bool-context `get` on non-Seq receiver must use Bool-predicate encoding,
/// not Int-valued fmap lookup.
///
/// Strengthened from trivial SAT (#1685): now verifies the Bool predicate
/// participates in Boolean reasoning via UNSAT contradiction.
#[test]
#[timeout(30000)]
fn test_bool_context_fmap_get_routes_to_bool_method_predicate() {
    let mut encoder = AYEncoder::new();

    // `m.get(1) && true` exercises the `method == "get" && !is_seq_receiver`
    // branch in encode_bool_context_operand.
    let expr = and(method_call(var("m"), "get", vec![int(1)]), bool_expr(true));
    let term1 = encoder
        .encode_pure(&expr)
        .expect("Bool-context FMap get should encode as Bool predicate");

    assert!(
        encoder.decls().has_logic_func("method_get_2_i_i"),
        "Bool-context get must declare Bool UF method_get_2_i_i; declared logic funcs: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
    assert!(
        !encoder.decls().has_spec_func("fmap_lookup"),
        "Bool-context get should not route through Int-valued fmap_lookup"
    );

    // UNSAT dual: term AND NOT(term) must be UNSAT (Bool contradiction)
    let term2 = encoder
        .encode_pure(&expr)
        .expect("second encoding should succeed");
    encoder.assert_term(term1);
    let neg = encoder.solver_mut().not(term2);
    encoder.assert_term(neg);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Bool-context get AND NOT(Bool-context get) must be UNSAT"
    );
}
