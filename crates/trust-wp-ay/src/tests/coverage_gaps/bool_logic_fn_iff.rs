// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_core::logic::LogicFnDef;

use super::*;

// ── Bool-returning LogicFnCall equality uses iff encoding (#1755) ────

/// `BinOp::Eq` on two Bool-returning `LogicFnCall` expressions must use iff
/// encoding (`(a => b) AND (b => a)`) instead of raw `mk_eq`, which ay-dpll
/// mishandles for Bool-sorted terms (#1179).
///
/// This test declares two logic functions `is_valid` and `is_ready` that
/// return Bool (body uses `>` which infers as Bool), then encodes
/// `is_valid(x) == is_ready(x)` and verifies the solver correctly treats the
/// equality as a biconditional by checking that
/// `is_valid(x) = true AND is_ready(x) = false AND is_valid(x) == is_ready(x)`
/// is UNSAT (the equality must forbid differing truth values).
#[test]
#[timeout(30000)]
fn test_bool_logic_fn_eq_uses_iff_encoding() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare two Bool-returning logic functions.
    // Body uses `>` (comparison), so infer_expr_sort returns Sort::Bool,
    // which makes the function declaration have Bool return sort.
    let is_valid_def = LogicFnDef::new(
        "is_valid".to_string(),
        "test::is_valid".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(0)), // body: x > 0, returns Bool
    );
    let is_ready_def = LogicFnDef::new(
        "is_ready".to_string(),
        "test::is_ready".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(5)), // body: x > 5, returns Bool
    );

    // Register the functions (creates UF declarations with Bool return sort).
    encoder
        .register_logic_fn(&is_valid_def)
        .expect("is_valid registration should succeed");
    encoder
        .register_logic_fn(&is_ready_def)
        .expect("is_ready registration should succeed");

    // Build the expression: is_valid(x) == is_ready(x)
    let x_expr = var("x");
    let call_valid = logic_fn_call("is_valid", vec![x_expr.clone()]);
    let call_ready = logic_fn_call("is_ready", vec![x_expr]);
    let equality_expr = eq(call_valid.clone(), call_ready.clone());

    // Encode the equality — should use iff, not raw mk_eq.
    let eq_term = encoder
        .encode_pure(&equality_expr)
        .expect("Bool equality encoding should succeed");

    // Assert: is_valid(x) = true, is_ready(x) = false, AND is_valid(x) == is_ready(x).
    // With iff encoding: the equality forces is_valid(x) <=> is_ready(x), which
    // contradicts the true/false constraints → UNSAT.
    // With raw mk_eq: ay-dpll may treat the equality as unconstrained, allowing SAT.
    let valid_term = encoder
        .encode_pure(&call_valid)
        .expect("is_valid(x) encode");
    let ready_term = encoder
        .encode_pure(&call_ready)
        .expect("is_ready(x) encode");

    encoder.solver.assert_term(valid_term); // is_valid(x) = true
    let not_ready = encoder.solver.not(ready_term);
    encoder.solver.assert_term(not_ready); // is_ready(x) = false
    encoder.solver.assert_term(eq_term); // is_valid(x) == is_ready(x)

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Bool-returning logic fn equality must use iff encoding: \
         asserting is_valid(x)=T, is_ready(x)=F, and is_valid(x)==is_ready(x) \
         should be UNSAT, got: {result:?} (Part of #1755)"
    );
}

/// `BinOp::Ne` on Bool-returning LogicFnCall also routes through iff.
///
/// Complement of the above: `is_valid(x) != is_ready(x)` when both are true
/// must be UNSAT.
#[test]
#[timeout(30000)]
fn test_bool_logic_fn_ne_uses_iff_encoding() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_valid_def = LogicFnDef::new(
        "is_valid".to_string(),
        "test::is_valid".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(0)),
    );
    let is_ready_def = LogicFnDef::new(
        "is_ready".to_string(),
        "test::is_ready".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(5)),
    );

    encoder
        .register_logic_fn(&is_valid_def)
        .expect("is_valid registration");
    encoder
        .register_logic_fn(&is_ready_def)
        .expect("is_ready registration");

    let x_expr = var("x");
    let call_valid = logic_fn_call("is_valid", vec![x_expr.clone()]);
    let call_ready = logic_fn_call("is_ready", vec![x_expr]);
    let ne_expr = ne(call_valid.clone(), call_ready.clone());

    let ne_term = encoder
        .encode_pure(&ne_expr)
        .expect("Bool ne encoding should succeed");

    // Assert both true AND is_valid(x) != is_ready(x).
    // With iff-based ne: both true means equal, so ne is false → UNSAT.
    let valid_term = encoder.encode_pure(&call_valid).expect("encode is_valid");
    let ready_term = encoder.encode_pure(&call_ready).expect("encode is_ready");

    encoder.solver.assert_term(valid_term);
    encoder.solver.assert_term(ready_term);
    encoder.solver.assert_term(ne_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Bool-returning logic fn ne must use iff encoding: \
         asserting both true and ne should be UNSAT, got: {result:?} (Part of #1755)"
    );
}
