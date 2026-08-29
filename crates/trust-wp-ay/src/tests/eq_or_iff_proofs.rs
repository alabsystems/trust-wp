// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof tests for the legacy `eq_or_iff` wrapper and the shared equality path
//! behind it (#901, #1755, #1179).
//!
//! The current ay pin includes the Bool/Bool equality fix for #1179, so
//! `eq_or_iff` is now a compatibility wrapper over the native `eq_term`
//! helper. These tests keep the historical module name but now validate:
//! 1. Bool equality still constrains disagreement to UNSAT
//! 2. Bool equality is SAT when operands agree
//! 3. Int equality still uses standard solver equality
//! 4. Sort-mismatch coercion/panic isolation still works

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::BinOp;

use super::{
    super::AYEncoder,
    helpers::{binop, logic_fn_call, var},
};

/// Bool-sorted equality through the compatibility wrapper must reject
/// disagreement: asserting `a = b`, `a = true`, and `b = false` must be UNSAT.
///
/// Re: #1755 — eq_or_iff correctness for Bool operands
#[test]
#[timeout(30000)]
fn test_eq_or_iff_bool_constrains_as_biconditional() {
    let mut encoder = AYEncoder::new();
    let a = encoder
        .get_or_declare_var("__eoi_a", Sort::Bool)
        .expect("a");
    let b = encoder
        .get_or_declare_var("__eoi_b", Sort::Bool)
        .expect("b");

    // Assert equality through the compatibility wrapper.
    let eq_term = encoder.eq_or_iff(a, b, &Sort::Bool);
    encoder.solver.assert_term(eq_term);

    // Assert a = true and b = false — contradicts equality
    encoder.solver.assert_term(a);
    let not_b = encoder.solver.not(b);
    encoder.solver.assert_term(not_b);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "eq_or_iff(a, b, Bool) with a=T, b=F must be UNSAT"
    );
}

/// Bool-sorted `eq_or_iff` must be SAT when both operands agree.
///
/// Re: #1755 — eq_or_iff correctness for Bool operands (positive case)
#[test]
#[timeout(30000)]
fn test_eq_or_iff_bool_sat_when_operands_agree() {
    let mut encoder = AYEncoder::new();
    let a = encoder
        .get_or_declare_var("__eoi_sat_a", Sort::Bool)
        .expect("a");
    let b = encoder
        .get_or_declare_var("__eoi_sat_b", Sort::Bool)
        .expect("b");

    let eq_term = encoder.eq_or_iff(a, b, &Sort::Bool);
    encoder.solver.assert_term(eq_term);
    encoder.solver.assert_term(a);
    encoder.solver.assert_term(b);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "eq_or_iff(a, b, Bool) with a=T, b=T must be SAT"
    );
}

/// Int-sorted `eq_or_iff` uses standard equality (mk_eq).
///
/// Asserting `eq_or_iff(x, y, Int)` and `x = 5` and `y != 5` must be UNSAT,
/// proving that Int equality correctly constrains x == y.
///
/// Re: #1755 — eq_or_iff correctness for Int operands
#[test]
#[timeout(30000)]
fn test_eq_or_iff_int_uses_standard_equality() {
    let mut encoder = AYEncoder::new();
    let x = encoder
        .get_or_declare_var("__eoi_int_x", Sort::Int)
        .expect("x");
    let y = encoder
        .get_or_declare_var("__eoi_int_y", Sort::Int)
        .expect("y");

    let eq_term = encoder.eq_or_iff(x, y, &Sort::Int);
    encoder.solver.assert_term(eq_term);

    let five = encoder.solver.int_const(5);
    let x_eq_5 = encoder.solver.eq(x, five);
    encoder.solver.assert_term(x_eq_5);

    let y_neq_5 = encoder.solver.neq(y, five);
    encoder.solver.assert_term(y_neq_5);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "eq_or_iff(x, y, Int) with x=5 and y!=5 must be UNSAT — \
         Int equality should force x == y"
    );
}

/// `eq_or_iff` with mismatched sorts (Int vs Uninterpreted) must catch
/// any ay panic and record the reason, not crash the process.
///
/// Re: #1755, #1806 — eq_or_iff panic isolation
#[test]
#[timeout(30000)]
fn test_eq_or_iff_sort_mismatch_catches_panic() {
    let mut encoder = AYEncoder::new();
    let x = encoder
        .get_or_declare_var("__eoi_mismatch_x", Sort::Int)
        .expect("x");

    // Create an Uninterpreted-sorted term
    let uninterp_sort = Sort::Uninterpreted("SeqBench".to_string());
    let s = encoder
        .get_or_declare_var("__eoi_mismatch_s", uninterp_sort)
        .expect("s");

    // eq_or_iff with Int sort hint but mismatched operand sorts
    // should catch the ay panic (if ay panics) or succeed (if ay
    // handles uninterpreted sorts).
    let _eq_term = encoder.eq_or_iff(x, s, &Sort::Int);

    // The key invariant: the encoder must not crash. If ay panicked,
    // the panic reason should be recorded.
    let reason = encoder.solver_panic_reason();
    if reason.is_some() {
        // Panic was caught — good. check_sat must return Unknown.
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unknown),
            "caught sort-mismatch panic must force Unknown"
        );
    }
    // If reason is None, ay handled the Int/Uninterpreted equality
    // without panicking — also acceptable.
}

/// Sort-mismatch coercion in `eq_or_iff` prevents ay panics by coercing
/// the Int operand to a fresh unconstrained constant of the other sort.
/// The eq result with an unconstrained constant is sound: ay treats
/// `fresh_seq = s` as satisfiable (the fresh const can equal s), so
/// the equality doesn't create false proof obligations. (#2077)
///
/// Previously (#1663): panic caught, fallback = bool_const(false), result = Unknown.
/// Now (#2077): no panic, coerced eq, result = normal SAT/UNSAT.
///
/// Re: #1663 — panic recovery bool_const(true) fallback soundness fix
/// Re: #2077 — generalized sort coercion for all sort-mismatch pairs
#[cfg(debug_assertions)]
#[test]
#[timeout(30000)]
fn test_eq_or_iff_sort_mismatch_coerced_conservative() {
    let mut encoder = AYEncoder::new();
    let x = encoder
        .get_or_declare_var("__eoi_fallback_x", Sort::Int)
        .expect("x");

    // Create a Seq-sorted term — sort mismatch with Int.
    let seq_sort = Sort::Seq(Box::new(Sort::Int));
    let s = encoder
        .get_or_declare_var("__eoi_fallback_s", seq_sort)
        .expect("s");

    // Coercion prevents the panic: Int operand becomes a fresh Seq const.
    let eq_term = encoder.eq_or_iff(x, s, &Sort::Int);

    // No panic should be recorded — coercion prevents the mismatch.
    assert!(
        encoder.solver_panic_reason().is_none(),
        "Sort coercion should prevent ay panic for Int vs Seq mismatch"
    );

    // The coerced equality is well-sorted and produces a normal result.
    encoder.assert_term(eq_term);
    let result = encoder.check_sat();
    assert!(
        !result.is_unknown(),
        "sort coercion should prevent Unknown result, got: {result:?}"
    );
}

/// `BinOp::Eq` on two `LogicFnCall` expressions returning Bool must still
/// constrain both sides to the same truth value.
///
/// This is the final acceptance criterion for #1755: when the full
/// `encode_pure` path processes `is_valid(x) == is_sorted(x)` with both
/// functions detected as Bool-returning, the equality must reject disagreement.
/// Specifically: asserting the equality and then forcing
/// `is_valid(x) = true` and `is_sorted(x) = false` must be UNSAT.
///
/// Re: #1755 AC-3
#[test]
#[timeout(30000)]
fn test_binop_eq_on_two_logic_fn_calls_returning_bool_uses_iff() {
    let mut encoder = AYEncoder::new();

    // Build: is_valid(x) == is_sorted(x)
    let is_valid_x = logic_fn_call("is_valid", vec![var("x")]);
    let is_sorted_x = logic_fn_call("is_sorted", vec![var("x")]);
    let eq_expr = binop(is_valid_x.clone(), BinOp::Eq, is_sorted_x.clone());

    // Register Bool sort hints for both logic functions.
    // In the real pipeline, `register_formula_sort_hints` detects these from
    // their context (e.g., appearing as top-level formula leaves in And/Or/
    // requires). For this test, we call `register_formula_sort_hints` on each
    // LogicFnCall to simulate them appearing in a Bool-requiring context.
    // This stores hints under the SMT name (e.g., "logic_is__valid"), matching
    // the lookup key in `apply_logic_fn`.
    encoder.register_formula_sort_hints(std::slice::from_ref(&is_valid_x));
    encoder.register_formula_sort_hints(std::slice::from_ref(&is_sorted_x));
    // Also register from the full expression tree
    encoder.register_sort_hints(std::slice::from_ref(&eq_expr));

    // Encode the equality expression through the full encode_pure path.
    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("BinOp::Eq on two Bool-returning LogicFnCalls should encode");

    // Assert the equality holds
    encoder.assert_term(eq_term);

    // Now assert is_valid(x) = true and is_sorted(x) = false.
    // Equality must reject the disagreement.
    let valid_term = encoder
        .encode_pure(&is_valid_x)
        .expect("encode is_valid(x)");
    let sorted_term = encoder
        .encode_pure(&is_sorted_x)
        .expect("encode is_sorted(x)");

    // Force is_valid(x) = true
    encoder.assert_term(valid_term);
    // Force is_sorted(x) = false
    let not_sorted = encoder.solver.not(sorted_term);
    encoder.assert_term(not_sorted);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "BinOp::Eq on two Bool LogicFnCalls must reject disagreement. \
         is_valid(x) == is_sorted(x) with is_valid=T, is_sorted=F must be UNSAT. \
         Got {result:?}."
    );
}

/// Defense validation: `eq_or_iff` with wrong sort hint `Sort::Int` for
/// Bool-sorted terms still produces correct results (UNSAT).
///
/// `eq_or_iff` now ignores the legacy sort hint and forwards to the shared
/// native-equality helper. This test keeps the old wrong-hint scenario alive
/// to make sure the compatibility wrapper still rejects Bool disagreement.
///
/// If this test starts FAILING (SAT instead of UNSAT), it means the current
/// ay Bool-equality behavior has regressed again (#1179) and the wrapper can
/// no longer rely on native solver equality.
///
/// Re: #2231 — Sort::Int fallback on Bool terms
/// Re: #1179 — ay-dpll mk_eq Bool behavior
#[test]
#[timeout(30000)]
fn test_eq_or_iff_wrong_sort_hint_int_on_bool_terms_still_correct() {
    let mut encoder = AYEncoder::new();
    let a = encoder
        .get_or_declare_var("__eoi_hint_a", Sort::Bool)
        .expect("a");
    let b = encoder
        .get_or_declare_var("__eoi_hint_b", Sort::Bool)
        .expect("b");

    // Call eq_or_iff with a stale Sort::Int hint even though the terms are Bool.
    let eq_term = encoder.eq_or_iff(a, b, &Sort::Int);
    encoder.solver.assert_term(eq_term);

    // Assert a = true and b = false — contradicts equality.
    encoder.solver.assert_term(a);
    let not_b = encoder.solver.not(b);
    encoder.solver.assert_term(not_b);

    let result = encoder.check_sat();
    // Native Bool equality must still reject disagreement here.
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "eq_or_iff with wrong Sort::Int hint on Bool terms must still be \
         UNSAT. Got {result:?}. If SAT, ay-dpll #1179 has regressed."
    );
}
