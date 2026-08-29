// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

#[test]
#[timeout(30000)]
fn test_verify_function_filters_unused_logic_fns() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let used_logic_fn = LogicFnDef::new(
        "add_one".to_string(),
        "crate::specs::add_one".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Open);

    let unused_logic_fn = LogicFnDef::new(
        "unused_bad".to_string(),
        "crate::specs::unused_bad".to_string(),
        vec!["x".to_string()],
        method_call(var("x"), "unknown_method", Vec::new()),
    );

    let requires = vec![gt(logic_fn_call("add_one", vec![var("x")]), int(0))];
    let ensures = vec![bool_expr(true)];
    let body = var("x");

    let logic_fns = vec![used_logic_fn, unused_logic_fn];
    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(&logic_fns)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "verify_function should ignore unused logic fns: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_verify_function_registers_transitive_logic_fn_deps() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let is_positive = LogicFnDef::new(
        "is_positive".to_string(),
        "crate::specs::is_positive".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(0)),
    )
    .with_mode(LogicMode::Open);

    let is_strictly_positive = LogicFnDef::new(
        "is_strictly_positive".to_string(),
        "crate::specs::is_strictly_positive".to_string(),
        vec!["x".to_string()],
        and(
            logic_fn_call("is_positive", vec![var("x")]),
            gt(var("x"), int(1)),
        ),
    )
    .with_mode(LogicMode::Open);

    let requires = vec![logic_fn_call("is_strictly_positive", vec![var("x")])];
    let ensures = vec![bool_expr(true)];
    let body = var("x");

    let logic_fns = vec![is_strictly_positive, is_positive];
    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(&logic_fns)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "verify_function should register transitive logic fn deps: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_register_logic_fn_idempotent() {
    // Registering the same function twice should be idempotent.
    // Semantic: id(x) = x, so id(7) = 7. Assert id(7) != 7 → Unsat. Part of #1990.
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fn = LogicFnDef::new(
        "id".to_string(),
        "crate::specs::id".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("first registration should succeed");
    encoder
        .register_logic_fn(&logic_fn)
        .expect("second registration should also succeed");

    // Semantic: after double registration, id(7) should still equal 7.
    let call = logic_fn_call("id", vec![int(7)]);
    let call_term = encoder.encode_pure(&call).expect("encode id(7)");
    let seven = encoder.solver.int_const(7);
    let eq = encoder.solver.eq(call_term, seven);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "id(7) != 7 should be Unsat after idempotent registration (#1990)"
    );
}

#[test]
#[timeout(30000)]
fn test_register_logic_fns_batch() {
    // Test registering multiple logic functions at once.
    // Semantic: min(3, 5) = 3, max(3, 5) = 5. Part of #1990.
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fns = vec![
        LogicFnDef::new(
            "min".to_string(),
            "crate::specs::min".to_string(),
            vec!["a".to_string(), "b".to_string()],
            ite(le(var("a"), var("b")), var("a"), var("b")),
        )
        .with_mode(LogicMode::Open),
        LogicFnDef::new(
            "max".to_string(),
            "crate::specs::max".to_string(),
            vec!["a".to_string(), "b".to_string()],
            ite(ge(var("a"), var("b")), var("a"), var("b")),
        )
        .with_mode(LogicMode::Open),
    ];

    encoder
        .register_logic_fns(&logic_fns)
        .expect("batch logic function registration should succeed");
    assert!(
        encoder.decls().has_logic_func("logic_min"),
        "batch registration should include 'logic_min'; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
    assert!(
        encoder.decls().has_logic_func("logic_max"),
        "batch registration should include 'logic_max'; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );

    // Semantic: min(3, 5) = 3. Assert min(3, 5) != 3 → Unsat.
    let min_call = logic_fn_call("min", vec![int(3), int(5)]);
    let min_term = encoder.encode_pure(&min_call).expect("encode min(3,5)");
    let three = encoder.solver.int_const(3);
    let eq = encoder.solver.eq(min_term, three);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "min(3, 5) != 3 should be Unsat (axiom: min(a,b) = ite(a<=b, a, b)) (#1990)"
    );
}

#[test]
#[timeout(30000)]
fn test_register_logic_fn_then_call() {
    // Register a function, then encode a call to it
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fn = LogicFnDef::new(
        "double".to_string(),
        "crate::specs::double".to_string(),
        vec!["x".to_string()],
        mul(var("x"), int(2)),
    )
    .with_mode(LogicMode::Open);

    // Register the function
    encoder
        .register_logic_fn(&logic_fn)
        .expect("logic function registration should succeed");

    // Now encode a call to it: double(5)
    let call = logic_fn_call("double", vec![int(5)]);

    let call_term = encoder.encode_pure(&call).expect("Should encode call");

    // Semantic: the axiom says double(x) = x*2, so double(5) = 10.
    // Assert double(5) != 10 — if the axiom works, this is UNSAT.
    let ten = encoder.solver.int_const(10);
    let eq = encoder.solver.eq(call_term, ten);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "double(5) != 10 should be UNSAT (axiom: double(x)=x*2)"
    );
}

#[test]
#[timeout(30000)]
fn test_register_logic_fn_preserves_var_scope() {
    // Test that registration doesn't pollute the variable namespace
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fn = LogicFnDef::new(
        "test_fn".to_string(),
        "test::test_fn".to_string(),
        vec!["x".to_string(), "y".to_string()],
        add(var("x"), var("y")),
    )
    .with_mode(LogicMode::Open);

    // Before registration, x and y shouldn't be in vars
    assert!(
        !encoder.vars_for_test().contains_key("x"),
        "x should not exist before registration"
    );
    assert!(
        !encoder.vars_for_test().contains_key("y"),
        "y should not exist before registration"
    );

    encoder
        .register_logic_fn(&logic_fn)
        .expect("register bound-variable logic function");

    // After registration, x and y still shouldn't be in vars
    // (they were bound variables in the axiom, not global constants)
    assert!(
        !encoder.vars_for_test().contains_key("x"),
        "x should not exist after registration"
    );
    assert!(
        !encoder.vars_for_test().contains_key("y"),
        "y should not exist after registration"
    );
}

#[test]
#[timeout(30000)]
fn test_register_logic_fn_with_arithmetic_body() {
    // Test a logic function with complex arithmetic
    let mut encoder = AYEncoder::new_with_quantifiers();

    // clamp(x, lo, hi) = if x < lo { lo } else { if x > hi { hi } else { x } }
    let logic_fn = LogicFnDef::new(
        "clamp".to_string(),
        "crate::specs::clamp".to_string(),
        vec!["x".to_string(), "lo".to_string(), "hi".to_string()],
        ite(
            lt(var("x"), var("lo")),
            var("lo"),
            ite(gt(var("x"), var("hi")), var("hi"), var("x")),
        ),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("complex logic function registration should succeed");

    // Semantic check: clamp(5, 0, 10) should equal 5
    // (5 is between lo=0 and hi=10, so clamp returns x=5)
    let call_expr = logic_fn_call("clamp", vec![int(5), int(0), int(10)]);
    let call_term = encoder
        .encode_pure(&call_expr)
        .expect("clamp(5, 0, 10) should encode");
    let five = encoder.encode_pure(&int(5)).expect("encode int literal 5");
    let neq = {
        let solver = encoder.solver_mut();
        let eq = solver.eq(call_term, five);
        solver.not(eq)
    };
    encoder.assert_term(neq);
    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, SolveResult::Unsat(_)),
        "clamp(5, 0, 10) must equal 5 (in range): {sat_result:?}"
    );
}
