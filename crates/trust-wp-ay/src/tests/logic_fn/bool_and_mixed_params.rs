// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::{
    formula::ExprSort,
    logic::{LogicFnDef, LogicMode},
};

use super::*;

/// Test that a logic function with a Bool parameter declares the correct sort.
///
/// Regression test for #544 Phase 3: previously all params were forced to Int,
/// causing ay panics when a Bool argument was passed.
///
/// Semantic check: negate(true) should equal false (axiom: negate(b) = !b).
/// Part of #1990.
///
/// ```text
/// #[logic(open)]
/// fn negate(b: bool) -> bool { !b }
/// ```
#[test]
#[timeout(30000)]
fn test_register_logic_fn_bool_param() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fn = LogicFnDef::new(
        "negate".to_string(),
        "test::negate".to_string(),
        vec!["b".to_string()],
        not(var("b")),
    )
    .with_param_sorts(vec![Some(ExprSort::Bool)])
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("Bool-param logic function registration should not panic");

    // Semantic: negate(true) = !true = false. Assert negate(true) != false → Unsat.
    let call = logic_fn_call("negate", vec![bool_expr(true)]);
    let call_term = encoder.encode_pure(&call).expect("encode negate(true)");
    let false_term = encoder.solver.bool_const(false);
    let eq = encoder.solver.eq(call_term, false_term);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "negate(true) != false should be Unsat (axiom: negate(b) = !b) (#1990)"
    );
}

/// Test that a logic function call with a View argument propagates Seq sort.
///
/// Regression test for #1572: when `num_of_pos(0, i@, t@)` is encoded,
/// the `t@` argument must be resolved as Seq sort (not the default Int),
/// because the function declaration has Seq at parameter index 2.
/// Without the fix in `encode_logic_fn_call_impl`, the pre-scan misses
/// `t@` as Seq (it only detects Seq via method receivers or equality),
/// and `encode_view_expr` defaults `t_view` to Int, causing a sort mismatch.
///
/// ```text
/// #[logic]
/// fn num_of_pos(i: Int, j: Int, t: Seq<i32>) -> Int { ... }
/// // invariant: count@ == num_of_pos(0, i@, t@)
/// ```
#[test]
#[timeout(30000)]
fn test_logic_fn_call_view_arg_gets_seq_sort_from_declaration() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register num_of_pos with Seq at param 2
    let logic_fn = LogicFnDef::new(
        "num_of_pos".to_string(),
        "test::num_of_pos".to_string(),
        vec!["i".to_string(), "j".to_string(), "t".to_string()],
        // Body: if i >= j { 0 } else { ... } — simplified to Int(0) for test
        int(0),
    )
    .with_param_sorts(vec![None, None, Some(ExprSort::Seq)])
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fns(&[logic_fn])
        .expect("registration should succeed");

    // Encode: num_of_pos(0, i@, t@)
    // The critical test: t@ must be encoded with Seq sort, not Int.
    let call_expr = logic_fn_call("num_of_pos", vec![int(0), view(var("i")), view(var("t"))]);
    // Register sort hints for the call expression (simulates verifier pre-scan)
    encoder.register_sort_hints(std::slice::from_ref(&call_expr));

    let result = encoder.encode_pure(&call_expr);
    // NOTE: encoding-only — tests sort propagation for View args with Seq sort hint.
    // check_sat would test UF semantics unrelated to the sort mismatch regression. See #1990.
    assert!(
        result.is_ok(),
        "Encoding num_of_pos(0, i@, t@) should not panic with sort mismatch. Got: {result:?}"
    );
}

/// End-to-end: verify a function that calls a Bool-parameter logic function.
///
/// ```text
/// #[logic(open)]
/// fn negate(b: bool) -> bool { !b }
///
/// #[requires(negate(x > 0))]     // negate(true when x>0) => !(x>0) => x<=0
/// #[ensures(result <= 0)]
/// fn identity(x: i32) -> i32 { x }
/// ```
#[test]
#[timeout(30000)]
fn test_verify_bool_param_logic_fn() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let logic_fn = LogicFnDef::new(
        "negate".to_string(),
        "test::negate".to_string(),
        vec!["b".to_string()],
        not(var("b")),
    )
    .with_param_sorts(vec![Some(ExprSort::Bool)])
    .with_mode(LogicMode::Open);

    // requires: negate(x > 0) — evaluates to !(x > 0), i.e. x <= 0
    let requires = vec![logic_fn_call("negate", vec![gt(var("x"), int(0))])];

    // ensures: result <= 0
    let ensures = vec![le(var("result"), int(0))];

    // body: result = x
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "negate(x > 0) => result <= 0 should verify: {result:?}"
    );
}

/// Test that mixed Int and Bool parameters work correctly.
///
/// Semantic check: guard(5, true) = true && 5 > 0 = true. Part of #1990.
///
/// ```text
/// #[logic(open)]
/// fn guard(x: i32, flag: bool) -> bool { flag && x > 0 }
/// ```
#[test]
#[timeout(30000)]
fn test_register_logic_fn_mixed_int_bool_params() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fn = LogicFnDef::new(
        "guard".to_string(),
        "test::guard".to_string(),
        vec!["x".to_string(), "flag".to_string()],
        and(var("flag"), gt(var("x"), int(0))),
    )
    .with_param_sorts(vec![None, Some(ExprSort::Bool)])
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("mixed Int/Bool params should register");

    // Semantic: guard(5, true) = true && 5 > 0 = true.
    // Assert guard(5, true) = false → Unsat.
    let call = logic_fn_call("guard", vec![int(5), bool_expr(true)]);
    let call_term = encoder.encode_pure(&call).expect("encode guard(5, true)");
    let false_term = encoder.solver.bool_const(false);
    let eq = encoder.solver.eq(call_term, false_term);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "guard(5, true) = false should be Unsat (axiom: guard = flag && x>0) (#1990)"
    );
}

/// End-to-end: mixed params — verify guard(x, true) implies x > 0.
#[test]
#[timeout(30000)]
fn test_verify_mixed_param_logic_fn() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let logic_fn = LogicFnDef::new(
        "guard".to_string(),
        "test::guard".to_string(),
        vec!["x".to_string(), "flag".to_string()],
        and(var("flag"), gt(var("x"), int(0))),
    )
    .with_param_sorts(vec![None, Some(ExprSort::Bool)])
    .with_mode(LogicMode::Open);

    // requires: guard(x, true) — expands to true && x > 0, i.e. x > 0
    let requires = vec![logic_fn_call("guard", vec![var("x"), bool_expr(true)])];

    // ensures: result > 0
    let ensures = vec![gt(var("result"), int(0))];

    // body: result = x
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "guard(x, true) => result > 0 must verify: {result:?}"
    );
}

/// Test that empty `param_sorts` is backward-compatible (defaults to all Int).
#[test]
#[timeout(30000)]
fn test_empty_param_sorts_backward_compat() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // max(a, b) with no param_sorts specified — should behave exactly as before
    let logic_fn = LogicFnDef::new(
        "max".to_string(),
        "test::max".to_string(),
        vec!["a".to_string(), "b".to_string()],
        ite(ge(var("a"), var("b")), var("a"), var("b")),
    )
    .with_mode(LogicMode::Open);

    // requires: max(x, 0) > 0 means x > 0
    // Actually: requires x > 0, ensures max(x, 0) == x
    let requires = vec![gt(var("x"), int(0))];

    let ensures = vec![eq(
        logic_fn_call("max", vec![var("x"), int(0)]),
        var("result"),
    )];

    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Empty param_sorts (backward compat) should verify: {result:?}"
    );
}
