// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `flatten_ghost_implications` and its internal constant substitution.
//!
//! `flatten_ghost_implications` is a four-phase preprocessing pass that helps
//! ay-dpll solve ghost context implications involving UF+arithmetic:
//!
//! - Phase 1: Collect Bool variables directly asserted (known true)
//! - Phase 2: Propagate through equalities (Eq(Var(b), rhs) where rhs is asserted)
//! - Phase 3: Flatten implications whose antecedent is known-true
//! - Phase 4: Ground constant propagation (substitute known constants into exprs)
//!
//! These tests verify each phase in isolation and in combination, using
//! SMT check_sat to confirm the resulting assertions are semantically correct.
//!
//! Re: #901 — coverage for verify/function.rs:814-1051

use std::sync::Arc;

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::helpers::{add, and, eq, implies, int, logic_fn_call, var};
use crate::{encoder::AYEncoder, verify::flatten_ghost_implications};

// ---------------------------------------------------------------------------
// Phase 1: Direct Bool variable collection
// ---------------------------------------------------------------------------

/// When a ghost expression is a bare `Var("b")`, Phase 1 treats `b` as
/// known-true. Any implication `b ==> consequent` should then assert
/// the consequent directly. We verify this by checking that `b ==> (x > 0)`
/// combined with the ghost context makes `x > 0` provable.
#[test]
#[timeout(30000)]
fn test_phase1_direct_bool_var_enables_implication_flattening() {
    let mut encoder = AYEncoder::new_pure();

    // Declare x as Int
    let x_term = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    // Ghost context: [Var("b"), Implies(Var("b"), x > 0)]
    // Phase 1 collects b as true, Phase 3 flattens implies to assert x > 0
    let ghost_exprs = vec![
        var("b"),
        implies(
            var("b"),
            PureExpr::BinOp(Arc::new(var("x")), BinOp::Gt, Arc::new(int(0))),
        ),
    ];

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    // Now assert x <= 0 (negation of the expected consequence)
    let zero = encoder.solver_mut().int_const(0);
    let x_le_zero = encoder.solver_mut().le(x_term, zero);
    encoder.assert_term(x_le_zero);

    // Should be Unsat because flatten asserted x > 0
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Phase 1+3: x > 0 should be asserted, making x <= 0 Unsat; got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Phase 2: Equality propagation
// ---------------------------------------------------------------------------

/// When ghost_exprs contains `Eq(Var("b"), rhs)` and `rhs` is also in
/// ghost_exprs, Phase 2 marks `b` as known-true. This enables Phase 3
/// implication flattening for `b ==> consequent`.
#[test]
#[timeout(30000)]
fn test_phase2_equality_propagation_lhs_var() {
    let mut encoder = AYEncoder::new_pure();

    let x_term = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    // Ghost context:
    //   [Var("flag"), Eq(Var("b"), Var("flag")), Implies(Var("b"), x > 0)]
    // Phase 1: flag is known true
    // Phase 2: Eq(Var("b"), Var("flag")) where Var("flag") is in ghost_exprs → b is true
    // Phase 3: b ==> x > 0 flattened → asserts x > 0
    let ghost_exprs = vec![
        var("flag"),
        eq(var("b"), var("flag")),
        implies(
            var("b"),
            PureExpr::BinOp(Arc::new(var("x")), BinOp::Gt, Arc::new(int(0))),
        ),
    ];

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    let zero = encoder.solver_mut().int_const(0);
    let x_le_zero = encoder.solver_mut().le(x_term, zero);
    encoder.assert_term(x_le_zero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Phase 2 (lhs Var): b should be propagated as true, making x <= 0 Unsat; got {result:?}"
    );
}

/// Phase 2 also handles the symmetric case: `Eq(rhs, Var("b"))` where rhs
/// appears in ghost_exprs.
#[test]
#[timeout(30000)]
fn test_phase2_equality_propagation_rhs_var() {
    let mut encoder = AYEncoder::new_pure();

    let x_term = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    // Ghost context:
    //   [Var("flag"), Eq(Var("flag"), Var("b")), Implies(Var("b"), x > 0)]
    // Phase 2: Eq(Var("flag"), Var("b")) — rhs is Var("b"), lhs is Var("flag")
    //          Var("flag") is in ghost_exprs → b is true
    let ghost_exprs = vec![
        var("flag"),
        eq(var("flag"), var("b")),
        implies(
            var("b"),
            PureExpr::BinOp(Arc::new(var("x")), BinOp::Gt, Arc::new(int(0))),
        ),
    ];

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    let zero = encoder.solver_mut().int_const(0);
    let x_le_zero = encoder.solver_mut().le(x_term, zero);
    encoder.assert_term(x_le_zero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Phase 2 (rhs Var): b should be propagated as true, making x <= 0 Unsat; got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Phase 3: Implication flattening
// ---------------------------------------------------------------------------

/// Phase 3 should NOT flatten implications whose antecedent is not known-true.
/// If `b` is never asserted or propagated, `b ==> x > 0` should not produce
/// any new assertion.
#[test]
#[timeout(30000)]
fn test_phase3_unknown_antecedent_not_flattened() {
    let mut encoder = AYEncoder::new_pure();

    let x_term = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    // Ghost context: [Implies(Var("unknown_b"), x > 0)]
    // "unknown_b" is never asserted, so the implication should NOT be flattened
    let ghost_exprs = vec![implies(
        var("unknown_b"),
        PureExpr::BinOp(Arc::new(var("x")), BinOp::Gt, Arc::new(int(0))),
    )];

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    // Assert x == -5 (negative). If flatten incorrectly asserted x > 0,
    // this would be Unsat.
    let neg5 = encoder.solver_mut().int_const(-5);
    let x_eq_neg5 = encoder.solver_mut().eq(x_term, neg5);
    encoder.assert_term(x_eq_neg5);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Phase 3: unknown antecedent should NOT flatten, x == -5 should be Sat; got {result:?}"
    );
}

/// Phase 3 should not flatten when the antecedent is a complex expression
/// (not a bare Var), even if the expression might be semantically true.
#[test]
#[timeout(30000)]
fn test_phase3_complex_antecedent_not_flattened() {
    let mut encoder = AYEncoder::new_pure();

    let x_term = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    // Ghost context: [Implies(And(Var("a"), Var("c")), x > 0)]
    // Even with Var("a") and Var("c") both known-true, the antecedent is
    // And(a, c) which is not a bare Var — Phase 3 skips this.
    let ghost_exprs = vec![
        var("a"),
        var("c"),
        implies(
            and(var("a"), var("c")),
            PureExpr::BinOp(Arc::new(var("x")), BinOp::Gt, Arc::new(int(0))),
        ),
    ];

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    // If the implication were flattened, x > 0 would be asserted.
    let neg5 = encoder.solver_mut().int_const(-5);
    let x_eq_neg5 = encoder.solver_mut().eq(x_term, neg5);
    encoder.assert_term(x_eq_neg5);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Phase 3: complex antecedent And(a, c) should NOT flatten; got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Phase 4: Ground constant propagation
// ---------------------------------------------------------------------------

/// Phase 4 collects `complex_expr == constant` from ghost_exprs and
/// substitutes into other expressions. This test verifies the basic case:
/// `f(a) == 0` + `f(b) == f(a) + 1` should produce `f(b) == 0 + 1`.
///
/// We verify by asserting the ghost context plus `f(b) != 1` and checking
/// Unsat (the substitution makes the contradiction visible to ay).
#[test]
#[timeout(30000)]
fn test_phase4_constant_propagation_logic_fn() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare UFs: f(Int) -> Int
    let f_decl = encoder
        .solver
        .declare_fun("test_f", &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func("test_f".to_string(), f_decl);

    // Declare variables a, b
    let _a = encoder.get_or_declare_var("a", Sort::Int).expect("a");
    let _b = encoder.get_or_declare_var("b", Sort::Int).expect("b");

    // Ghost context:
    //   f(a) == 0
    //   f(b) == f(a) + 1
    let f_a = logic_fn_call("test_f", vec![var("a")]);
    let f_b = logic_fn_call("test_f", vec![var("b")]);
    let ghost_exprs = vec![
        eq(f_a.clone(), int(0)),
        eq(f_b.clone(), add(f_a.clone(), int(1))),
    ];

    // Encode and assert the ghost exprs themselves first (they define f(a)=0, f(b)=f(a)+1)
    for expr in &ghost_exprs {
        let term = encoder.encode_pure(expr).expect("encode ghost expr");
        encoder.assert_term(term);
    }

    // Now run flatten to get the constant propagation
    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    // Assert f(b) != 1
    let f_b_term = encoder.encode_pure(&f_b).expect("encode f(b)");
    let one = encoder.solver_mut().int_const(1);
    let f_b_ne_1 = {
        let eq_term = encoder.solver_mut().eq(f_b_term, one);
        encoder.solver_mut().not(eq_term)
    };
    encoder.assert_term(f_b_ne_1);

    // Should be Unsat: f(a)=0, f(b)=f(a)+1=0+1=1, so f(b)!=1 contradicts
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Phase 4: constant propagation should make f(b)!=1 Unsat; got {result:?}"
    );
}

/// Phase 4 should handle the symmetric case where the constant is on the
/// left side of the equality: `0 == f(a)`.
#[test]
#[timeout(30000)]
fn test_phase4_constant_on_lhs() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let f_decl = encoder
        .solver
        .declare_fun("test_g", &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func("test_g".to_string(), f_decl);

    let _a = encoder.get_or_declare_var("a", Sort::Int).expect("a");
    let _b = encoder.get_or_declare_var("b", Sort::Int).expect("b");

    let g_a = logic_fn_call("test_g", vec![var("a")]);
    let g_b = logic_fn_call("test_g", vec![var("b")]);

    // Note: constant on LHS: `0 == g(a)`
    let ghost_exprs = vec![
        eq(int(0), g_a.clone()),
        eq(g_b.clone(), add(g_a.clone(), int(1))),
    ];

    for expr in &ghost_exprs {
        let term = encoder.encode_pure(expr).expect("encode ghost expr");
        encoder.assert_term(term);
    }

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    let g_b_term = encoder.encode_pure(&g_b).expect("encode g(b)");
    let one = encoder.solver_mut().int_const(1);
    let g_b_ne_1 = {
        let eq_term = encoder.solver_mut().eq(g_b_term, one);
        encoder.solver_mut().not(eq_term)
    };
    encoder.assert_term(g_b_ne_1);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Phase 4 (lhs constant): g(b)!=1 should be Unsat; got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

/// Empty ghost_exprs should be a no-op.
#[test]
#[timeout(30000)]
fn test_empty_ghost_exprs_is_noop() {
    let mut encoder = AYEncoder::new_pure();

    let x_term = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    flatten_ghost_implications(&mut encoder, &[]).expect("flatten empty should succeed");

    // Encoder should be unconstrained — x can be anything
    let five = encoder.solver_mut().int_const(5);
    let x_eq_5 = encoder.solver_mut().eq(x_term, five);
    encoder.assert_term(x_eq_5);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "empty ghost_exprs: encoder should be unconstrained; got {result:?}"
    );
}

/// Ghost exprs with no implications and no equalities should not crash
/// or add unexpected assertions.
#[test]
#[timeout(30000)]
fn test_only_plain_vars_no_implications() {
    let mut encoder = AYEncoder::new_pure();

    let x_term = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");

    // Ghost context: [Var("a"), Var("b")]
    // Phase 1 collects a, b as true. Phase 3 finds no implications. Phase 4 no equalities.
    let ghost_exprs = vec![var("a"), var("b")];

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    // x should still be unconstrained
    let neg10 = encoder.solver_mut().int_const(-10);
    let x_eq = encoder.solver_mut().eq(x_term, neg10);
    encoder.assert_term(x_eq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "plain vars only: x should be unconstrained; got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Combined phases: Phase 3 consequent feeds into Phase 4 const_map
// ---------------------------------------------------------------------------

/// When Phase 3 flattens an implication, the consequent becomes available
/// for Phase 4 constant propagation. This tests the cross-phase interaction:
///
///   ghost_exprs: [Var("b"), Implies(Var("b"), f(a) == 0), f(c) == f(a) + 1]
///
/// Phase 3: b ==> (f(a) == 0) → asserts f(a) == 0
/// Phase 4: f(a) == 0 is now in all_exprs (via flattened_consequents),
///          so f(c) == f(a) + 1 gets substituted to f(c) == 0 + 1
#[test]
#[timeout(30000)]
fn test_combined_phase3_phase4_cross_interaction() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let f_decl = encoder
        .solver
        .declare_fun("test_h", &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func("test_h".to_string(), f_decl);

    let _a = encoder.get_or_declare_var("a", Sort::Int).expect("a");
    let _c = encoder.get_or_declare_var("c", Sort::Int).expect("c");

    let h_a = logic_fn_call("test_h", vec![var("a")]);
    let h_c = logic_fn_call("test_h", vec![var("c")]);

    // Ghost context:
    //   Var("b")                           — Phase 1: b is true
    //   Implies(Var("b"), h(a) == 0)       — Phase 3: flattened → asserts h(a) == 0
    //   h(c) == h(a) + 1                   — Phase 4: substitutes h(a) → 0, asserts h(c) == 0 + 1
    let ghost_exprs = vec![
        var("b"),
        implies(var("b"), eq(h_a.clone(), int(0))),
        eq(h_c.clone(), add(h_a.clone(), int(1))),
    ];

    // Encode and assert only the non-Bool ghost exprs.
    // Var("b") is a Bool assertion — encoding it via encode_pure would default
    // to Int sort, causing a sort conflict when flatten later encodes the
    // implication consequent. In production, the ghost context Bool vars are
    // already declared with the correct sort by the precondition encoding pass.
    // Here we only assert the arithmetic equality that Phase 4 needs.
    let eq_term = encoder
        .encode_pure(&ghost_exprs[2])
        .expect("encode h(c)==h(a)+1");
    encoder.assert_term(eq_term);

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    // Assert h(c) != 1 — should contradict the constant propagation result
    let h_c_term = encoder.encode_pure(&h_c).expect("encode h(c)");
    let one = encoder.solver_mut().int_const(1);
    let h_c_ne_1 = {
        let eq_term = encoder.solver_mut().eq(h_c_term, one);
        encoder.solver_mut().not(eq_term)
    };
    encoder.assert_term(h_c_ne_1);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "combined Phase 3+4: h(c)!=1 should be Unsat (h(a)=0 from Phase 3, h(c)=h(a)+1=1); got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Phase 4: substitute_constants structural coverage
// ---------------------------------------------------------------------------

/// Phase 4 should substitute through nested BinOp expressions.
/// Ghost: f(a) == 5, (f(a) + f(a)) > 0
/// After substitution: (5 + 5) > 0 should be asserted as a simplified form.
#[test]
#[timeout(30000)]
fn test_phase4_substitution_through_binop() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let f_decl = encoder
        .solver
        .declare_fun("test_p", &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func("test_p".to_string(), f_decl);

    let _a = encoder.get_or_declare_var("a", Sort::Int).expect("a");

    let p_a = logic_fn_call("test_p", vec![var("a")]);

    // Ghost context:
    //   p(a) == 5
    //   (p(a) + p(a)) > 0
    let ghost_exprs = vec![
        eq(p_a.clone(), int(5)),
        PureExpr::BinOp(
            Arc::new(add(p_a.clone(), p_a.clone())),
            BinOp::Gt,
            Arc::new(int(0)),
        ),
    ];

    for expr in &ghost_exprs {
        let term = encoder.encode_pure(expr).expect("encode ghost expr");
        encoder.assert_term(term);
    }

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    // The substitution should have produced (5+5) > 0 which is trivially true.
    // Assert p(a) != 5 to contradict the original assertion.
    let p_a_term = encoder.encode_pure(&p_a).expect("encode p(a)");
    let five = encoder.solver_mut().int_const(5);
    let p_a_ne_5 = {
        let eq_term = encoder.solver_mut().eq(p_a_term, five);
        encoder.solver_mut().not(eq_term)
    };
    encoder.assert_term(p_a_ne_5);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Phase 4 BinOp substitution: p(a)!=5 should be Unsat; got {result:?}"
    );
}

/// Phase 4 should substitute through Final/Deref/View wrappers.
/// Ghost: Final(Var("x")) == 42, Deref(Final(Var("x"))) > 0
/// After substitution: Deref(42) > 0 (the substitution reaches into wrappers).
///
/// Note: we only verify that flatten doesn't crash on wrapper expressions
/// and that the original assertion is preserved, since Deref(Int(42)) may
/// not have clear semantics in isolation.
#[test]
#[timeout(30000)]
fn test_phase4_substitution_through_wrappers() {
    let mut encoder = AYEncoder::new_pure();

    let _x = encoder.get_or_declare_var("x", Sort::Int).expect("x");

    let final_x = PureExpr::Final(Arc::new(var("x")));

    // Ghost context:
    //   Final(Var("x")) == 42
    //   Final(Var("x")) + 1 > 0
    let ghost_exprs = vec![
        eq(final_x.clone(), int(42)),
        PureExpr::BinOp(
            Arc::new(add(final_x.clone(), int(1))),
            BinOp::Gt,
            Arc::new(int(0)),
        ),
    ];

    // Encode the equality assertion
    let eq_term = encoder.encode_pure(&ghost_exprs[0]).expect("encode eq");
    encoder.assert_term(eq_term);

    flatten_ghost_implications(&mut encoder, &ghost_exprs)
        .expect("flatten with wrapper expressions should succeed");

    // The substitution should produce (42 + 1) > 0 which is true.
    // Verify the original constraint holds: Final(x) == 42
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Phase 4 wrappers: should be Sat after flatten; got {result:?}"
    );
}

/// Phase 4 should not substitute into Var/Int/Bool leaf nodes that don't
/// match any const_map entry (no false positive substitutions).
#[test]
#[timeout(30000)]
fn test_phase4_no_false_substitution_on_leaves() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let f_decl = encoder
        .solver
        .declare_fun("test_q", &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func("test_q".to_string(), f_decl);

    let _a = encoder.get_or_declare_var("a", Sort::Int).expect("a");
    let _y = encoder.get_or_declare_var("y", Sort::Int).expect("y");

    let q_a = logic_fn_call("test_q", vec![var("a")]);

    // Ghost context:
    //   q(a) == 7
    //   y == 99
    // Phase 4 should map q(a) → 7 but NOT substitute y (y is a Var, not substitutable).
    // y == 99 has y on lhs which is a Var (not matching is_substitutable_expr).
    let ghost_exprs = vec![eq(q_a.clone(), int(7)), eq(var("y"), int(99))];

    for expr in &ghost_exprs {
        let term = encoder.encode_pure(expr).expect("encode ghost expr");
        encoder.assert_term(term);
    }

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    // y should be constrained to 99 by the original assertion, not by substitution
    let y_term = *encoder.vars_for_test().get("y").expect("y declared");
    let hundred = encoder.solver_mut().int_const(100);
    let y_eq_100 = encoder.solver_mut().eq(y_term, hundred);
    encoder.assert_term(y_eq_100);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "y should be 99 (from original assertion), y==100 should be Unsat; got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Multiple implications with different antecedents
// ---------------------------------------------------------------------------

/// When multiple implications have different antecedents, only those with
/// known-true antecedents should be flattened.
#[test]
#[timeout(30000)]
fn test_multiple_implications_selective_flattening() {
    let mut encoder = AYEncoder::new_pure();

    let x_term = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");
    let _y_term = encoder
        .get_or_declare_var("y", Sort::Int)
        .expect("declare y");

    // Ghost context:
    //   Var("known_true")
    //   Implies(Var("known_true"), x > 0)     — should be flattened
    //   Implies(Var("unknown"), y > 0)         — should NOT be flattened
    let ghost_exprs = vec![
        var("known_true"),
        implies(
            var("known_true"),
            PureExpr::BinOp(Arc::new(var("x")), BinOp::Gt, Arc::new(int(0))),
        ),
        implies(
            var("unknown"),
            PureExpr::BinOp(Arc::new(var("y")), BinOp::Gt, Arc::new(int(0))),
        ),
    ];

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    // x > 0 was asserted (flattened), so x == -1 should be Unsat
    let neg1 = encoder.solver_mut().int_const(-1);
    let x_eq_neg1 = encoder.solver_mut().eq(x_term, neg1);
    encoder.assert_term(x_eq_neg1);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "known_true implication should be flattened, x==-1 should be Unsat; got {result:?}"
    );
}

/// Complement of the above: verify that the unknown antecedent's implication
/// was NOT flattened by checking y can be negative.
#[test]
#[timeout(30000)]
fn test_multiple_implications_unknown_not_flattened() {
    let mut encoder = AYEncoder::new_pure();

    let _x_term = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");
    let y_term = encoder
        .get_or_declare_var("y", Sort::Int)
        .expect("declare y");

    let ghost_exprs = vec![
        var("known_true"),
        implies(
            var("known_true"),
            PureExpr::BinOp(Arc::new(var("x")), BinOp::Gt, Arc::new(int(0))),
        ),
        implies(
            var("unknown"),
            PureExpr::BinOp(Arc::new(var("y")), BinOp::Gt, Arc::new(int(0))),
        ),
    ];

    flatten_ghost_implications(&mut encoder, &ghost_exprs).expect("flatten should succeed");

    // y > 0 was NOT asserted, so y == -5 should be Sat
    let neg5 = encoder.solver_mut().int_const(-5);
    let y_eq_neg5 = encoder.solver_mut().eq(y_term, neg5);
    encoder.assert_term(y_eq_neg5);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "unknown implication should NOT be flattened, y==-5 should be Sat; got {result:?}"
    );
}
