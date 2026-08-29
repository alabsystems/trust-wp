// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;
use crate::error::EncodingError;

// ── PureExpr::Closure encoding error path (#1013) ──────────────────────

/// Encoding a standalone `PureExpr::Closure` with parameters now falls back
/// to a fresh unconstrained constant (conservative #985 handling) instead
/// of returning an error. Zero-parameter closures encode the body directly.
#[test]
#[timeout(30000)]
fn test_closure_encoding_returns_unsupported_error() {
    let mut encoder = AYEncoder::new();

    // Parameterized closure: returns a fresh constant (not an error)
    let closure_expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(add(var("x"), int(1))),
    };
    let result = encoder.encode_pure(&closure_expr);
    assert!(
        result.is_ok(),
        "Parameterized closure should encode as fresh constant, got: {result:?}"
    );

    // Zero-parameter closure: encodes body directly
    let thunk_expr = PureExpr::Closure {
        params: vec![],
        body: Arc::new(int(42)),
    };
    let result = encoder.encode_pure(&thunk_expr);
    assert!(
        result.is_ok(),
        "Zero-param closure should encode body directly"
    );
}

/// Final(BinOp(...)) distributes the Final wrapper into BinOp operands (#2700).
///
/// Before #2700, Final(BinOp) returned Unsupported. Now the wrapper is
/// distributed into each operand: Final(a + b) → Final(a) + Final(b).
/// For literals, Final is a no-op, so Final(1 + 2) → 1 + 2 = 3.
#[test]
#[timeout(30000)]
fn test_final_complex_expr_returns_unsupported() {
    let mut encoder = AYEncoder::new();

    // ^(1 + 2) — Final wrapping a binary operation. BinOp distribution turns
    // this into Final(1) + Final(2), and each operand is now a prophecy over a
    // constant carrier, so the distribution SINKS into the tract19 refusal.
    // That is the intended reach: fixing the literal arm covers every
    // distribution route (BinOp/UnOp/Ite/Match/args) without a separate guard
    // on each.
    let expr = final_expr(add(int(1), int(2)));
    let result = encoder.encode_pure(&expr);
    assert!(
        matches!(result, Err(EncodingError::Unsupported { .. })),
        "Final(BinOp of literals) must sink into the constant-carrier refusal: {result:?}"
    );
}

// ── tract19: `^<literal>` REFUSES fail-closed ────────────────────────
//
// The four tests below used to assert that `Final(<literal>)` encodes to the
// literal, on the reasoning recorded at #1075: "the final value of an integer
// literal is the literal itself. MIR extraction may produce this when a local
// with a literal initial value participates in reborrow chains."
//
// The premise of that reasoning is the bug. A literal in wrapper position is
// exactly what the driver substitutes for a borrowed local whose CURRENT value
// is a constant (`mir_analysis/extract/substitution/visitor.rs`, #1581), and
// `^p` names the value the borrow holds when it EXPIRES. Folding the wrapper
// away asserts `^p == *p`, so any mutation through the borrow becomes
// invisible to the contract. That was a LIVE false accept on 4d809ba:
//
//     #[ensures((^r)@ >= 0)] fn touch(r: &mut i32) { *r = 99; }
//     #[ensures(result@ == 3)]
//     pub fn evil() -> i32 { let mut x = 3i32; let r = &mut x; touch(r); x }
//
// verified with `decisions=0` (the negated postcondition encoded to literal
// `false`) although `evil` returns 99. Reproducer kept as
// `tests/adversarial/cases/f_prophecy_over_constant_carrier.rs`.
//
// The `Deref` siblings below are unaffected and MUST keep collapsing: `*3` is
// faithful, because the literal already IS the referent's value.

/// `^42` must refuse — see the banner above. (tract19; was #1075/#951)
#[test]
#[timeout(30000)]
fn test_final_int_literal_refuses_fail_closed() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_pure(&final_expr(int(42)));
    assert!(
        matches!(result, Err(EncodingError::Unsupported { .. })),
        "`^42` must refuse fail-closed, got {result:?}"
    );
}

/// `^true` must refuse — same rule as the Int case. (tract19; was #951)
#[test]
#[timeout(30000)]
fn test_final_bool_literal_refuses_fail_closed() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_pure(&final_expr(PureExpr::Bool(true)));
    assert!(
        matches!(result, Err(EncodingError::Unsupported { .. })),
        "`^true` must refuse fail-closed, got {result:?}"
    );
}

/// Deref(Int(n)) — the "current value" of an integer literal is the literal
/// itself. MIR extraction may produce this when a literal participates in
/// reborrow-chain substitution. (#1075)
/// Strengthened: verifies term equality with bare literal. (#951)
#[test]
#[timeout(30000)]
fn test_deref_int_literal_encodes_as_literal() {
    let mut encoder = AYEncoder::new();

    let wrapped = PureExpr::Deref(Arc::new(int(42)));
    let bare = int(42);
    let wrapped_term = encoder
        .encode_pure(&wrapped)
        .expect("Deref(Int(42)) should succeed");
    let bare_term = encoder.encode_pure(&bare).expect("Int(42) should succeed");
    let eq_term = encoder.solver_mut().eq(wrapped_term, bare_term);
    let neq_term = encoder.solver_mut().not(eq_term);
    encoder.assert_term(neq_term);
    let result = encoder.solver_mut().check_sat();
    assert!(
        result.is_unsat(),
        "Deref(Int(42)) must be provably equal to Int(42) (UNSAT of negated eq)"
    );
}

/// Deref(Bool(false)) — same constant-collapse logic for Bool literals.
/// Strengthened: verifies term equality with bare literal. (#951)
#[test]
#[timeout(30000)]
fn test_deref_bool_literal_encodes_as_literal() {
    let mut encoder = AYEncoder::new();

    let wrapped = PureExpr::Deref(Arc::new(PureExpr::Bool(false)));
    let bare = PureExpr::Bool(false);
    let wrapped_term = encoder
        .encode_pure(&wrapped)
        .expect("Deref(Bool(false)) should succeed");
    let bare_term = encoder
        .encode_pure(&bare)
        .expect("Bool(false) should succeed");
    let eq_term = encoder.solver_mut().eq(wrapped_term, bare_term);
    let neq_term = encoder.solver_mut().not(eq_term);
    encoder.assert_term(neq_term);
    let result = encoder.solver_mut().check_sat();
    assert!(
        result.is_unsat(),
        "Deref(Bool(false)) must be provably equal to Bool(false) (UNSAT of negated eq)"
    );
}

/// Nested same-type wrapper: Deref(Deref(Int(n))) collapses to Int(n).
/// peel_deref_depth peels multiple layers; the literal base arm handles the rest.
#[test]
#[timeout(30000)]
fn test_deref_deref_int_literal_encodes_as_literal() {
    let mut encoder = AYEncoder::new();

    let double_deref = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(int(99)))));
    let bare = int(99);
    let wrapped_term = encoder
        .encode_pure(&double_deref)
        .expect("Deref(Deref(Int(99))) should succeed");
    let bare_term = encoder.encode_pure(&bare).expect("Int(99) should succeed");
    let eq_term = encoder.solver_mut().eq(wrapped_term, bare_term);
    let neq_term = encoder.solver_mut().not(eq_term);
    encoder.assert_term(neq_term);
    let result = encoder.solver_mut().check_sat();
    assert!(
        result.is_unsat(),
        "Deref(Deref(Int(99))) must be provably equal to Int(99) (UNSAT of negated eq)"
    );
}

/// Nested same-type wrapper: `^^true` must refuse too — peeling the depth does
/// not make the innermost carrier any less constant. (tract19)
#[test]
#[timeout(30000)]
fn test_final_final_bool_literal_refuses_fail_closed() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_pure(&final_expr(final_expr(PureExpr::Bool(true))));
    assert!(
        matches!(result, Err(EncodingError::Unsupported { .. })),
        "`^^true` must refuse fail-closed, got {result:?}"
    );
}

/// Final(Deref(LogicFnCall(..))): commute Final through Deref so the
/// Deref arm can push the dereference into the LogicFnCall args.
/// Regression test for #1191 (test_fnmut encoding error).
#[test]
#[timeout(30000)]
fn test_final_deref_logic_fn_call_encodes_ok() {
    let mut encoder = AYEncoder::new();

    // ^(*(__trust_wp_tuple1(x))) — the exact pattern from #1191
    let inner_call = logic_fn_call("__trust_wp_tuple1", vec![var("x")]);
    let expr = final_expr(deref(inner_call));
    let term = encoder
        .encode_pure(&expr)
        .expect("Final(Deref(LogicFnCall)) should encode successfully");

    // Semantic: two distinct inputs should produce distinguishable outputs
    let inner_call2 = logic_fn_call("__trust_wp_tuple1", vec![var("y")]);
    let expr2 = final_expr(deref(inner_call2));
    let term2 = encoder
        .encode_pure(&expr2)
        .expect("second Final(Deref(LogicFnCall)) should encode");
    let x_neq_y = encoder.encode_pure(&ne(var("x"), var("y"))).unwrap();
    encoder.assert_term(x_neq_y);
    let terms_neq = encoder.solver.neq(term, term2);
    encoder.assert_term(terms_neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "distinct inputs to Final(Deref(LogicFnCall)) should produce distinguishable results"
    );
}

/// Deref(Final(LogicFnCall(..))): symmetric case — commute Deref through
/// Final so the Final arm can push the final-value into the LogicFnCall args.
#[test]
#[timeout(30000)]
fn test_deref_final_logic_fn_call_encodes_ok() {
    let mut encoder = AYEncoder::new();

    // *( ^(__trust_wp_tuple1(x)) )
    let inner_call = logic_fn_call("__trust_wp_tuple1", vec![var("x")]);
    let expr = deref(final_expr(inner_call));
    let term = encoder
        .encode_pure(&expr)
        .expect("Deref(Final(LogicFnCall)) should encode successfully");

    // Semantic: encoding the same expression twice produces equal terms (UNSAT on neq)
    let inner_call2 = logic_fn_call("__trust_wp_tuple1", vec![var("x")]);
    let expr2 = deref(final_expr(inner_call2));
    let term2 = encoder
        .encode_pure(&expr2)
        .expect("same expression should encode again");
    let neq = encoder.solver.neq(term, term2);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "identical Deref(Final(LogicFnCall)) expressions must produce equal terms"
    );
}

/// Final(Deref(MethodCall(..))): method call variant of the commutation fix.
#[test]
#[timeout(30000)]
fn test_final_deref_method_call_encodes_ok() {
    let mut encoder = AYEncoder::new();

    // ^( *(x.len()) )
    let inner_method = method_call(var("x"), "len", vec![]);
    let expr = final_expr(deref(inner_method));
    let term = encoder
        .encode_pure(&expr)
        .expect("Final(Deref(MethodCall)) should encode successfully");

    // Semantic: constrain the UF result and verify the solver respects it
    let ten = encoder.solver.int_const(10);
    let eq10 = encoder.solver.eq(term, ten);
    let five = encoder.solver.int_const(5);
    let neq5 = encoder.solver.neq(term, five);
    encoder.assert_term(eq10);
    encoder.assert_term(neq5);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Final(Deref(MethodCall)) result should participate in Int constraints"
    );
}

/// Final(Deref(View(..))): push both wrappers into View's inner expression.
#[test]
#[timeout(30000)]
fn test_final_deref_view_rewrites_to_view_of_final_deref_inner() {
    let mut encoder = AYEncoder::new();

    let expr = final_expr(deref(view(var("x"))));
    let expected = view(final_expr(deref(var("x"))));

    let expr_term = encoder
        .encode_pure(&expr)
        .expect("Final(Deref(View(x))) should encode successfully");
    let expected_term = encoder
        .encode_pure(&expected)
        .expect("View(Final(Deref(x))) should encode successfully");

    let neq = encoder.solver.neq(expr_term, expected_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Final(Deref(View(x))) must be equivalent to View(Final(Deref(x)))"
    );
}

/// Deref(Final(View(..))): push both wrappers into View's inner expression.
#[test]
#[timeout(30000)]
fn test_deref_final_view_rewrites_to_view_of_deref_final_inner() {
    let mut encoder = AYEncoder::new();

    let expr = deref(final_expr(view(var("x"))));
    let expected = view(deref(final_expr(var("x"))));

    let expr_term = encoder
        .encode_pure(&expr)
        .expect("Deref(Final(View(x))) should encode successfully");
    let expected_term = encoder
        .encode_pure(&expected)
        .expect("View(Deref(Final(x))) should encode successfully");

    let neq = encoder.solver.neq(expr_term, expected_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Deref(Final(View(x))) must be equivalent to View(Deref(Final(x)))"
    );
}

/// Final(Deref(Ite(..))): distribute both wrappers into branches.
#[test]
#[timeout(30000)]
fn test_final_deref_ite_distributes_wrappers_to_branches() {
    let mut encoder = AYEncoder::new();

    let cond = eq(var("c"), int(0));
    let expr = final_expr(deref(PureExpr::Ite(
        Arc::new(cond.clone()),
        Arc::new(var("t")),
        Arc::new(var("e")),
    )));
    let expected = PureExpr::Ite(
        Arc::new(cond.clone()),
        Arc::new(final_expr(deref(var("t")))),
        Arc::new(final_expr(deref(var("e")))),
    );

    let expr_term = encoder
        .encode_pure(&expr)
        .expect("Final(Deref(Ite(..))) should encode successfully");
    let expected_term = encoder
        .encode_pure(&expected)
        .expect("distributed Ite expression should encode successfully");

    let neq = encoder.solver.neq(expr_term, expected_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Final(Deref(Ite(c,t,e))) must equal Ite(c, Final(Deref(t)), Final(Deref(e)))"
    );
}

/// Deref(Final(Ite(..))): distribute both wrappers into branches.
#[test]
#[timeout(30000)]
fn test_deref_final_ite_distributes_wrappers_to_branches() {
    let mut encoder = AYEncoder::new();

    let cond = eq(var("c"), int(0));
    let expr = deref(final_expr(PureExpr::Ite(
        Arc::new(cond.clone()),
        Arc::new(var("t")),
        Arc::new(var("e")),
    )));
    let expected = PureExpr::Ite(
        Arc::new(cond.clone()),
        Arc::new(deref(final_expr(var("t")))),
        Arc::new(deref(final_expr(var("e")))),
    );

    let expr_term = encoder
        .encode_pure(&expr)
        .expect("Deref(Final(Ite(..))) should encode successfully");
    let expected_term = encoder
        .encode_pure(&expected)
        .expect("distributed Ite expression should encode successfully");

    let neq = encoder.solver.neq(expr_term, expected_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Deref(Final(Ite(c,t,e))) must equal Ite(c, Deref(Final(t)), Deref(Final(e)))"
    );
}

/// Deref(Final(BinOp)) distributes both wrappers into BinOp operands (#2700).
///
/// Before #2700, this returned Unsupported. Now the cross-wrapper handling
/// detects Final inside Deref, and the BinOp distribution handles the inner
/// expression. For literals, both wrappers are no-ops.
#[test]
#[timeout(30000)]
fn test_deref_final_complex_expr_returns_unsupported() {
    let mut encoder = AYEncoder::new();

    // *(^(1 + 2)) — Deref(Final(BinOp)). With BinOp distribution in both
    // the cross-wrapper and direct wrapper paths, this now succeeds.
    let expr = deref(final_expr(add(int(1), int(2))));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Deref(Final(BinOp)) should succeed via BinOp distribution (#2700): {result:?}"
    );
}
