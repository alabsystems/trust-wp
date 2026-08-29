// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

#[test]
#[timeout(30000)]
fn test_register_logic_fn_simple() {
    // Test registering a simple logic function: max(a, b) = if a >= b { a } else { b }
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fn = LogicFnDef::new(
        "max".to_string(),
        "crate::specs::max".to_string(),
        vec!["a".to_string(), "b".to_string()],
        ite(ge(var("a"), var("b")), var("a"), var("b")),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("logic function registration should succeed");

    // Verify function was registered
    assert!(
        encoder.decls().has_logic_func("logic_max"),
        "Should register function with SMT name 'logic_max'"
    );

    // Semantic: the axiom says max(a,b) = ite(a>=b, a, b).
    // max(3, 7) should equal 7 — assert max(3,7) != 7 is UNSAT.
    let call = logic_fn_call("max", vec![int(3), int(7)]);
    let call_term = encoder.encode_pure(&call).expect("encode max(3,7)");
    let seven = encoder.solver.int_const(7);
    let eq = encoder.solver.eq(call_term, seven);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "max(3,7) != 7 should be UNSAT (axiom: max(a,b)=ite(a>=b,a,b))"
    );
}

#[test]
#[timeout(30000)]
fn test_register_logic_fn_nullary() {
    // Test registering a nullary logic function: zero() = 0
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fn = LogicFnDef::new(
        "zero".to_string(),
        "crate::specs::zero".to_string(),
        vec![], // No parameters
        int(0),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("nullary logic function registration should succeed");
    assert!(
        encoder.decls().has_logic_func("logic_zero"),
        "nullary logic function 'logic_zero' should be registered; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );

    // Semantic: axiom says zero() = 0, so zero() != 0 should be UNSAT
    let call = logic_fn_call("zero", vec![]);
    let call_term = encoder.encode_pure(&call).expect("encode zero()");
    let z = encoder.solver.int_const(0);
    let eq = encoder.solver.eq(call_term, z);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "zero() != 0 should be UNSAT (axiom: zero()=0)"
    );
}

#[test]
#[timeout(30000)]
fn test_register_logic_fn_unary() {
    // Test registering a unary logic function: abs(x) = if x >= 0 { x } else { -x }
    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fn = LogicFnDef::new(
        "abs".to_string(),
        "crate::specs::abs".to_string(),
        vec!["x".to_string()],
        ite(ge(var("x"), int(0)), var("x"), neg(var("x"))),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("unary logic function registration should succeed");

    // Semantic: abs(-3) should equal 3 via the axiom
    let call = logic_fn_call("abs", vec![int(-3)]);
    let call_term = encoder.encode_pure(&call).expect("encode abs(-3)");
    let three = encoder.solver.int_const(3);
    let eq = encoder.solver.eq(call_term, three);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "abs(-3) != 3 should be UNSAT (axiom: abs(x)=ite(x>=0,x,-x))"
    );
}

/// Test that bool-returning logic functions (predicates) work correctly.
/// Regression test for #289: predicates crashed with "sort mismatch" because
/// all logic functions were declared with `Sort::Int` return type.
#[test]
#[timeout(30000)]
fn test_register_logic_fn_bool_predicate() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // is_positive(x) = x > 0  (returns Bool, not Int)
    let logic_fn = LogicFnDef::new(
        "is_positive".to_string(),
        "test::is_positive".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(0)),
    )
    .with_mode(LogicMode::Open);

    // Test the predicate can be used in a requires clause:
    // #[requires(is_positive(x))]
    // #[ensures(result > 0)]
    // fn positive_identity(x: i32) -> i32 { x }
    //
    // requires: is_positive(x)  [which means x > 0]
    let requires = vec![logic_fn_call("is_positive", vec![var("x")])];

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
        "positive_identity must verify: {result:?}"
    );
}

/// Regression: logic function calling another Bool-returning logic function. (#544)
///
/// When `uses_simple()` calls `simple()` which returns Bool, the return sort of
/// `uses_simple` must also be Bool. Without sort hint propagation,
/// `infer_expr_sort(LogicFnCall { "simple" })` returns Int, causing
/// `mk_eq(Int, Bool)` panic in the defining axiom.
#[test]
#[timeout(30000)]
fn test_register_logic_fn_calling_bool_fn_no_sort_mismatch() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // simple() = true  (returns Bool)
    let simple_fn = LogicFnDef::new(
        "simple".to_string(),
        "test::simple".to_string(),
        vec![],
        bool_expr(true),
    )
    .with_mode(LogicMode::Open);

    // uses_simple() = simple()  (calls Bool-returning function)
    let uses_simple_fn = LogicFnDef::new(
        "uses_simple".to_string(),
        "test::uses_simple".to_string(),
        vec![],
        logic_fn_call("simple", vec![]),
    )
    .with_mode(LogicMode::Open);

    let logic_fns = vec![simple_fn, uses_simple_fn];

    // #[requires(uses_simple())]
    // #[ensures(simple())]
    // fn program() {}
    let requires = vec![logic_fn_call("uses_simple", vec![])];
    let ensures = vec![logic_fn_call("simple", vec![])];

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).logic_fns(Some(&logic_fns)),
    )
    .expect("logic fn call chain should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "requires(uses_simple()) ensures(simple()) should verify: both expand to true"
    );
}

/// Regression: opaque/default logic fns must still use the declared return
/// sort at call sites even when body inference falls back to Int. (#2320)
#[test]
#[timeout(30000)]
fn test_logic_fn_call_site_uses_declared_return_sort_hint() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = LogicFnDef::new(
        "is_valid".to_string(),
        "test::is_valid".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_return_sort(Some(ExprSort::Bool));

    encoder
        .register_logic_fn(&logic_fn)
        .expect("opaque Bool-returning logic fn registration should succeed");

    let call = logic_fn_call("is_valid", vec![int(0)]);
    assert_eq!(
        encoder.infer_expr_sort_with_context(&call, None),
        Sort::Bool,
        "call-site inference should use the declared Bool return sort"
    );

    let eq_term = encoder
        .encode_pure(&eq(call, bool_expr(true)))
        .expect("Bool call-site equality should encode without sort mismatch");
    assert_eq!(encoder.solver.get_sort(eq_term), Sort::Bool);
}

/// Regression: declared Seq return sorts must drive call-site inference for
/// opaque/default logic fns too, not just Bool-returning ones. (#2320)
#[test]
#[timeout(30000)]
fn test_logic_fn_call_site_uses_declared_seq_return_sort_hint() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = LogicFnDef::new(
        "items".to_string(),
        "test::items".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_return_sort(Some(ExprSort::Seq));

    encoder
        .register_logic_fn(&logic_fn)
        .expect("opaque Seq-returning logic fn registration should succeed");

    let call = logic_fn_call("items", vec![int(0)]);
    let inferred_sort = encoder.infer_expr_sort_with_context(&call, None);
    assert!(
        inferred_sort.is_seq(),
        "call-site inference should use the declared Seq return sort, got {inferred_sort:?}"
    );

    let term = encoder
        .encode_pure(&call)
        .expect("Seq-returning call should encode without sort mismatch");
    let term_sort = encoder.solver.get_sort(term);
    assert!(
        term_sort.is_seq(),
        "call-site encoding should preserve the declared Seq return sort, got {term_sort:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_register_opaque_logic_fn_skips_defining_axiom() {
    use ay_dpll::api::SolveResult;

    let mut encoder = AYEncoder::new_with_quantifiers();

    let logic_fn = LogicFnDef::new_with_requires(
        "secret".to_string(),
        "test::secret".to_string(),
        vec![],
        vec![bool_expr(false)],
        int(42),
    )
    .with_opaque(true);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("opaque logic function registration should succeed");
    assert!(
        encoder.decls().has_logic_func("logic_secret"),
        "Opaque function should still be declared"
    );

    let call = logic_fn_call("secret", vec![]);
    let call_term = encoder
        .encode_pure(&call)
        .expect("Opaque call should encode successfully");
    let expected = encoder.solver.int_const(42);
    let eq = encoder.solver.eq(call_term, expected);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "False-guarded definition should remain unconstrained at call sites, got: {result:?}"
    );
}
