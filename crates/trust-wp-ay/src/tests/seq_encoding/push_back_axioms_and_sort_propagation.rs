// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq encoding (Part of #111).
//!
//! Includes sequence view, len, index, `push_back`, error handling, and axiom tests.
//! Split from encoding.rs per #395.

use super::*;

/// Test that Seq axiom 4 holds: sequence length is non-negative.
///
/// Axiom 4: forall s. len(s) >= 0
/// The test encodes: `NOT(v@.len() >= 0)` and checks it's UNSAT.
#[test]
#[timeout(30000)]
fn test_seq_axiom_len_nonnegative() {
    let mut encoder = AYEncoder::new();

    let v_view_expr = view(var("v"));

    // v@.len()
    let v_len = method_call(v_view_expr, "len", vec![]);

    // v@.len() >= 0
    let len_nonneg = ge(v_len, int(0));

    let formula_term = encoder
        .encode_pure(&len_nonneg)
        .expect("Axiom formula should encode");

    // Assert NOT(len >= 0) and check UNSAT — proves the axiom holds
    let neg_formula = encoder.solver.not(formula_term);
    encoder.assert_term(neg_formula);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Seq axiom 4 (len >= 0) should verify (expected UNSAT, got {result:?})"
    );
}

/// Cross-expression sort: a View first seen without Seq context in one expression
/// must still work when used as Seq receiver in a later expression (#544).
///
/// This simulates the `verify_function` pattern where requires and ensures are
/// encoded as separate `encode_pure` calls. If requires mentions `v@` without
/// Seq context and ensures uses `v@.len()`, the View must still get Seq sort.
#[test]
#[timeout(30000)]
fn test_view_sort_cross_expression_seq_after_int() {
    let mut encoder = AYEncoder::new();

    // First: register_sort_hints with ALL expressions (simulates verify.rs pre-scan).
    // This canonical API captures both Seq and Bool hints before encoding.
    let requires_expr = eq(view(var("v")), view(var("v")));
    let ensures_expr = ge(method_call(view(var("v")), "len", vec![]), int(0));

    // Pre-register all expressions (the correct pattern)
    encoder.register_sort_hints(&[requires_expr.clone(), ensures_expr.clone()]);

    // Now encode them separately (as verify_function does)
    let r1 = encoder.encode_pure(&requires_expr);
    r1.unwrap_or_else(|err| panic!("requires encoding should succeed: {err:?}"));

    let r2 = encoder.encode_pure(&ensures_expr);
    r2.unwrap_or_else(|err| panic!("ensures encoding should succeed: {err:?}"));
}

/// Without `register_sort_hints`, a View first declared as Int in one `encode_pure`
/// call will be treated as Int. When `v@.len()` is encoded later, the `is_seq_receiver`
/// dispatch (#756) detects v_view is not Seq-hinted and falls through to UF encoding
/// instead of panicking. Callers should still use `register_sort_hints` for correct
/// Seq encoding, but the absence no longer crashes.
#[test]
#[timeout(30000)]
fn test_view_sort_cross_expression_degrades_without_prescan() {
    let mut encoder = AYEncoder::new();

    // Requires: v@ == v@ (View appears without Seq context → declared as Int)
    let requires_expr = eq(view(var("v")), view(var("v")));

    // Ensures: v@.len() >= 0 (v_view is already Int; len falls through to UF)
    let ensures_expr = ge(method_call(view(var("v")), "len", vec![]), int(0));

    // NO register_sort_hints — v_view was declared as Int by requires encoding.
    // With #756 dispatch, len on non-Seq receiver falls through to UF encoding
    // instead of panicking with Sort mismatch.
    let r1 = encoder.encode_pure(&requires_expr);
    r1.unwrap_or_else(|err| panic!("requires encoding should succeed: {err:?}"));

    let r2 = encoder.encode_pure(&ensures_expr);
    r2.unwrap_or_else(|err| panic!("ensures encoding should degrade to UF, not panic: {err:?}"));
}

/// Verify Seq sort propagates through Ite branches: `(^self)@ == if cond { self@.push_back(v) } else { self@ }`
/// should mark both `final_self_view` and `self_view` as Seq even though the Seq-producing
/// `push_back` is inside an Ite branch.
///
/// Requested by Prover P11 audit (Part of #544).
#[test]
#[timeout(30000)]
fn test_view_sort_seq_through_ite_push_back() {
    let mut encoder = AYEncoder::new();

    // (^self)@
    let final_view = view(final_expr(var("self")));
    // self@.push_back(v)
    let push_back_expr = method_call(view(var("self")), "push_back", vec![var("v")]);
    // self@
    let self_view = view(var("self"));
    // if cond { self@.push_back(v) } else { self@ }
    let ite_expr = ite(var("cond"), push_back_expr, self_view);
    // (^self)@ == if cond { self@.push_back(v) } else { self@ }
    let eq_expr = eq(final_view, ite_expr);

    let result = encoder.encode_pure(&eq_expr);
    assert!(
        result.is_ok(),
        "Ite with push_back in then-branch should propagate Seq sort: {result:?}"
    );
    assert!(
        encoder.vars_for_test().contains_key("self_view"),
        "self_view should be created as Seq variable"
    );
    assert!(
        encoder.vars_for_test().contains_key("final_self_view"),
        "final_self_view should be created as Seq variable via equality propagation"
    );
}

/// Verify Seq sort propagates through Match arms: `(^self)@ == match x { 0 => self@.push_back(v), _ => self@ }`
/// should mark both view variables as Seq.
///
/// Requested by Prover P11 audit (Part of #544).
#[test]
#[timeout(30000)]
fn test_view_sort_seq_through_match_push_back() {
    let mut encoder = AYEncoder::new();

    // (^self)@
    let final_view = view(final_expr(var("self")));
    // match x { 0 => self@.push_back(v), _ => self@ }
    let match_expr_val = match_expr(
        var("x"),
        vec![
            (
                Pattern::Literal(int(0)),
                method_call(view(var("self")), "push_back", vec![var("v")]),
            ),
            (Pattern::Wildcard, view(var("self"))),
        ],
    );
    // (^self)@ == match x { ... }
    let eq_expr = eq(final_view, match_expr_val);

    let result = encoder.encode_pure(&eq_expr);
    assert!(
        result.is_ok(),
        "Match with push_back in arm should propagate Seq sort: {result:?}"
    );
    assert!(
        encoder.vars_for_test().contains_key("self_view"),
        "self_view should be created as Seq variable"
    );
    assert!(
        encoder.vars_for_test().contains_key("final_self_view"),
        "final_self_view should be created as Seq variable via equality propagation"
    );
}
