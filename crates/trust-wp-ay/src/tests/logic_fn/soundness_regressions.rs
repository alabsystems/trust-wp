// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Standalone soundness regression tests for logic function encoding.

use std::sync::Arc;

use ay_dpll::api::SolveResult;
use ntest::timeout;

use super::*;

// =============================================================================
// emit_spec_axioms silent-drop soundness tests (#1323)
// =============================================================================

/// When a logic function's `ensures` clause fails to encode (e.g., contains an
/// unsupported `Closure` expression), `emit_spec_axioms` silently drops the
/// failed axiom via `.flatten()` on `Result` iterators (logic_fn.rs:374).
///
/// This test verifies that dropping the ensures axiom does NOT cause the verifier
/// to produce a false `Verified` result for a postcondition that depends on
/// the (now-absent) spec axiom.
///
/// If `emit_spec_axioms` properly propagated the encoding error, verification
/// would return `Unknown` or `Err`. With the silent drop, the function becomes
/// constrained only by its body axiom (if Open mode), so the postcondition
/// `f(1) == 42` should NOT be `Verified` (it should be `Failed`).
#[test]
#[timeout(30000)]
fn test_emit_spec_axioms_dropped_ensures_does_not_falsely_verify() {
    use trust_wp_core::{
        formula::ExprSort,
        logic::{LogicFnDef, LogicMode},
    };

    // Logic function f(x) = x + 1 with body in Open mode.
    // Add an ensures clause that CANNOT encode: `result == |y| y + x`
    // The Closure expression is unsupported in the encoder, so encode_pure
    // returns Err(EncodingError::Unsupported). emit_spec_axioms drops it.
    let unencodable_ensures = eq(
        var("result"),
        PureExpr::Closure {
            params: vec![("y".to_string(), Some(ExprSort::Int))],
            body: Arc::new(add(var("y"), var("x"))),
        },
    );

    let mut logic_fn = LogicFnDef::new(
        "f_spec_drop".to_string(),
        "test::f_spec_drop".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)), // body: x + 1
    )
    .with_mode(LogicMode::Open);
    logic_fn.set_ensures(vec![unencodable_ensures]);

    // Postcondition: f(1) == 42.
    // This is FALSE (f(1) = 1+1 = 2, not 42).
    // If the body axiom fires, this should be Failed.
    // The key check: this must NOT be Verified.
    let ens = eq(logic_fn_call("f_spec_drop", vec![int(1)]), int(42));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).logic_fns(Some(&[logic_fn])),
    );

    assert!(
        crate::tests::rejected_ok(&result),
        "f(1)==42 must fail from the visible body axiom f(x)=x+1: {result:?}"
    );
}

/// Regression for `cell/02_fib`: spec axioms using `i.pow2()` must encode
/// instead of being dropped as an unsupported method. (#994)
#[test]
#[timeout(30000)]
fn test_emit_spec_axioms_supports_pow2_method() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let fib = LogicFnDef::new(
        "fib".to_string(),
        "test::fib".to_string(),
        vec!["i".to_string()],
        var("i"),
    )
    .with_mode(LogicMode::Open);

    let mut lemma = LogicFnDef::new(
        "lemma_fib_bound".to_string(),
        "test::lemma_fib_bound".to_string(),
        vec!["i".to_string()],
        int(0),
    )
    .with_mode(LogicMode::Open);
    lemma.set_requires(vec![le(int(0), var("i"))]);
    lemma.set_ensures(vec![le(
        logic_fn_call("fib", vec![var("i")]),
        method_call(var("i"), "pow2", vec![]),
    )]);

    let mut encoder = AYEncoder::new();
    encoder.register_logic_fn(&fib).expect("register fib");
    encoder
        .register_logic_fn(&lemma)
        .expect("pow2 in spec axiom should encode");

    assert!(
        encoder.decls().has_logic_func("method_pow2_1_i"),
        "symbolic pow2 in ensures should declare method_pow2_1_i"
    );
}

/// Ground `pow2` receivers should fold to the exact arithmetic term instead of
/// allocating an unnecessary UF. (#994)
#[test]
#[timeout(30000)]
fn test_pow2_ground_literal_folds_to_exact_power_of_two() {
    let mut encoder = AYEncoder::new();
    let pow_term = encoder
        .encode_pure(&method_call(int(4), "pow2", vec![]))
        .expect("pow2(4) should encode");
    let sixteen = encoder.encode_pure(&int(16)).expect("encode 16");
    let neq = encoder.solver.neq(pow_term, sixteen);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "pow2(4) should fold to 16"
    );
    assert!(
        !encoder.decls().has_logic_func("method_pow2_1_i"),
        "ground-folded pow2 should not need a UF declaration"
    );
}

/// Symbolic `pow2` must still reduce in branch-local base cases such as the
/// `lemma_fib_bound` proof's `i == 0` / `i == 1` arms. (#994)
#[test]
#[timeout(30000)]
fn test_pow2_symbolic_base_axioms_cover_zero_and_one() {
    for (input, expected) in [(0, 1), (1, 2)] {
        let mut encoder = AYEncoder::new();
        let assumption = encoder
            .encode_pure(&eq(var("i"), int(input)))
            .expect("encode branch assumption");
        let pow_term = encoder
            .encode_pure(&method_call(var("i"), "pow2", vec![]))
            .expect("symbolic pow2 should encode");
        let expected_term = encoder
            .encode_pure(&int(expected))
            .expect("encode expected pow2 value");
        encoder.assert_term(assumption);
        let neq = encoder.solver.neq(pow_term, expected_term);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "pow2({input}) should reduce to {expected} under a symbolic branch assumption"
        );
    }
}

/// Offset symbolic `pow2` receivers must also inherit the base cases needed by
/// the Fibonacci proof step: when `i == 2`, the predecessor terms reduce to
/// `pow2(i - 1) == 2` and `pow2(i - 2) == 1`. (#994)
#[test]
#[timeout(30000)]
fn test_pow2_symbolic_offset_base_axioms_cover_fib_predecessors() {
    let mut encoder = AYEncoder::new();
    let i_is_two = encoder
        .encode_pure(&eq(var("i"), int(2)))
        .expect("encode i == 2");
    let mismatch = encoder
        .encode_pure(&or(
            ne(method_call(sub(var("i"), int(1)), "pow2", vec![]), int(2)),
            ne(method_call(sub(var("i"), int(2)), "pow2", vec![]), int(1)),
        ))
        .expect("encode predecessor pow2 mismatch");
    encoder.assert_term(i_is_two);
    encoder.assert_term(mismatch);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "pow2 predecessor terms should reduce at i == 2"
    );
}

/// `lemma_fib_bound` needs the symbolic lower bound
/// `pow2(i) >= pow2(i - 1) + pow2(i - 2)` when `i >= 2`. (#994)
#[test]
#[timeout(30000)]
fn test_pow2_symbolic_lower_bound_matches_fib_step() {
    let mut encoder = AYEncoder::new();
    let non_base = encoder
        .encode_pure(&ge(var("i"), int(2)))
        .expect("encode i >= 2");
    let contradictory_goal = encoder
        .encode_pure(&lt(
            method_call(var("i"), "pow2", vec![]),
            add(
                method_call(sub(var("i"), int(1)), "pow2", vec![]),
                method_call(sub(var("i"), int(2)), "pow2", vec![]),
            ),
        ))
        .expect("encode pow2 lower-bound negation");
    encoder.assert_term(non_base);
    encoder.assert_term(contradictory_goal);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "pow2 should dominate the Fibonacci induction step for i >= 2"
    );
}

/// `pow2` is a known Int-returning method and should stay on the LOW-risk
/// method-call fallback lane, not the generic high-risk fallback. (#994)
#[test]
#[timeout(30000)]
fn test_pow2_sort_inference_uses_low_risk_method_category() {
    use crate::encoder::{
        sort_context::infer_expr_sort,
        unsoundness::{self, UnsoundnessCategory},
    };

    unsoundness::reset();
    let before = unsoundness::snapshot();
    let _ = infer_expr_sort(&method_call(var("i"), "pow2", vec![]));
    let delta = unsoundness::delta(&before, &unsoundness::snapshot());

    assert!(
        delta.contains_key(&UnsoundnessCategory::SortFallbackToIntFromMethodCall),
        "pow2 should use LOW-risk method-call fallback, got delta: {delta:?}"
    );
    assert!(
        !delta.contains_key(&UnsoundnessCategory::SortFallbackToInt),
        "pow2 should not hit HIGH-risk generic fallback, got delta: {delta:?}"
    );
    unsoundness::reset();
}

/// Some(fmap_view) should fall through to UF path when OptionInt datatype
/// is declared with Int fields (#994).
///
/// Before this fix, `encode_logic_fn_call` would attempt `datatype_constructor`
/// with an FMap-sorted argument, causing a ay sort mismatch panic.
#[test]
#[timeout(30000)]
fn test_some_with_fmap_arg_falls_through_to_uf() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();

    // Declare OptionInt datatype (Some has Int field sort)
    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&option_int);

    // Create an FMap-sorted variable (simulating r@ view of HashMap)
    let r_view = view(var("r"));
    encoder.record_sort_hint("r_view".to_string(), trust_wp_core::formula::ExprSort::FMap);

    // Some(r@) — this should NOT crash, should fall through to UF path
    let some_fmap = logic_fn_call("Some", vec![r_view]);
    let result = encoder.encode_pure(&some_fmap);
    assert!(
        result.is_ok(),
        "Some(fmap_view) should succeed via UF fallback: {result:?}"
    );
}
