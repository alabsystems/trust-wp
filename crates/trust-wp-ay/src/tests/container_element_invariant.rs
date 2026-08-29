// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct unit tests for `assert_container_element_invariant` and
//! `assert_container_element_invariant_body` (#P1-433).
//!
//! These functions encode quantified axioms:
//! ```text
//! forall i. 0 <= i < len(view) => inv(index(view, i))
//! ```
//!
//! Prior to this file, both functions had zero test coverage — they were
//! only called from `verify/function.rs` in a branch gated on
//! `element_invariant_method.is_some()` which no test exercises.

use ay_dpll::api::SolveResult;
use ntest::timeout;

use super::{super::AYEncoder, helpers::*};

// =============================================================================
// assert_container_element_invariant: basic smoke tests
// =============================================================================

/// Calling `assert_container_element_invariant` should succeed and not panic
/// for a well-formed view variable and invariant method name.
#[test]
#[timeout(30000)]
fn test_container_element_invariant_succeeds() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let result =
        encoder.assert_container_element_invariant("x_view", "__trust_wp_invariant_Positive");
    assert!(
        result.is_ok(),
        "assert_container_element_invariant should succeed for valid inputs: {result:?}"
    );
}

/// Asserting the element invariant should register the invariant for later
/// ground instances without needing a satisfiable bare-quantifier query.
#[test]
#[timeout(30000)]
fn test_container_element_invariant_registers_for_ground_instances() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .assert_container_element_invariant("v_view", "__trust_wp_invariant_IsEven")
        .expect("assert_container_element_invariant should succeed");

    let v_view = encoder
        .get_or_declare_var("v_view", ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int))
        .expect("v_view should be declared");
    assert!(
        encoder
            .seq_state_for_test()
            .container_element_invariants_cloned(&v_view)
            .is_some_and(|specs| specs.len() == 1),
        "element invariant should be registered for v_view ground instances"
    );
}

/// Assert element invariant, then assert that the invariant function returns
/// false for some element, while also asserting the element is in bounds.
/// This should be Unsat because the invariant axiom requires inv(elem) for
/// all in-bounds indices.
///
/// We use `encode_pure` to produce len/index terms (avoids accessing private
/// Seq fields) and `decls.logic_funcs` to look up the invariant UF.
#[test]
#[timeout(30000)]
fn test_container_element_invariant_contradicts_violation() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // First register sort hints so v_view resolves as Seq
    let len_expr = method_call(view(var("v")), "len", vec![]);
    encoder.register_sort_hints(std::slice::from_ref(&len_expr));

    // Assert the element invariant axiom
    encoder
        .assert_container_element_invariant("v_view", "__trust_wp_invariant_Pos")
        .expect("assert_container_element_invariant should succeed");

    // Encode v@.len() to get the len term and trigger seq infrastructure
    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("v@.len() should encode");

    // Encode v@.index_logic(0) to get element-at-0 term
    let index_expr = method_call(view(var("v")), "index_logic", vec![int(0)]);
    let elem_0_term = encoder
        .encode_pure(&index_expr)
        .expect("v@.index_logic(0) should encode");

    // Assert len(v_view) >= 1 (container has at least one element)
    let one = encoder.solver_mut().int_const(1);
    let has_element = encoder.solver_mut().ge(len_term, one);
    encoder.assert_term(has_element);

    // Look up the invariant UF declared by assert_container_element_invariant
    let inv_fn = encoder
        .decls()
        .get_logic_func("method___trust_wp_invariant_Pos_1_i")
        .expect("invariant function should be declared by assert_container_element_invariant")
        .clone();

    // Assert !inv(index(v_view, 0)) — the first element violates the invariant
    let inv_0 = encoder.solver_mut().apply(&inv_fn, &[elem_0_term]);
    let not_inv_0 = encoder.solver_mut().not(inv_0);
    encoder.assert_term(not_inv_0);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "element invariant + in-bounds element violating invariant should be Unsat: {result:?}"
    );
}

// =============================================================================
// assert_container_element_invariant: trivial invariant short-circuit
// =============================================================================

/// When the invariant method is registered as trivially true, the function
/// should return Ok but NOT assert any quantified axiom (tautological).
#[test]
#[timeout(30000)]
fn test_container_element_invariant_trivial_true_skips() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register the invariant as trivially true
    let element_smt = "method___trust_wp_invariant_Trivial_1_i".to_string();
    encoder
        .decls_for_test_mut()
        .register_trivial_invariant(element_smt);

    let result =
        encoder.assert_container_element_invariant("x_view", "__trust_wp_invariant_Trivial");
    assert!(
        result.is_ok(),
        "trivially-true invariant should short-circuit successfully: {result:?}"
    );
}

// =============================================================================
// assert_container_element_invariant_body: inlined body variant
// =============================================================================

/// `assert_container_element_invariant_body` with a simple body expression
/// (self_param > 0) should succeed and produce a consistent axiom.
#[test]
#[timeout(30000)]
fn test_container_element_invariant_body_succeeds() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Body: self_param > 0 (the element must be positive)
    let body = gt(var("self_param"), int(0));

    let result = encoder.assert_container_element_invariant_body("v_view", "self_param", &body);
    assert!(
        result.is_ok(),
        "assert_container_element_invariant_body should succeed: {result:?}"
    );
}

/// Asserting the inlined body invariant should register the invariant for later
/// ground instances without needing a satisfiable bare-quantifier query.
#[test]
#[timeout(30000)]
fn test_container_element_invariant_body_registers_for_ground_instances() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let body = gt(var("self_param"), int(0));
    encoder
        .assert_container_element_invariant_body("v_view", "self_param", &body)
        .expect("should succeed");

    let v_view = encoder
        .get_or_declare_var("v_view", ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int))
        .expect("v_view should be declared");
    assert!(
        encoder
            .seq_state_for_test()
            .container_element_invariants_cloned(&v_view)
            .is_some_and(|specs| specs.len() == 1),
        "inlined body invariant should be registered for v_view ground instances"
    );
}

/// Assert the inlined body invariant (elem > 0), then use encode_pure to
/// produce len/index terms, and assert violation. Should be Unsat.
#[test]
#[timeout(30000)]
fn test_container_element_invariant_body_contradicts_violation() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register sort hints so v_view is Seq
    let len_expr = method_call(view(var("v")), "len", vec![]);
    encoder.register_sort_hints(std::slice::from_ref(&len_expr));

    // Body: self_param > 0
    let body = gt(var("self_param"), int(0));
    encoder
        .assert_container_element_invariant_body("v_view", "self_param", &body)
        .expect("should succeed");

    // Encode v@.len() to get the len term
    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("v@.len() should encode");

    // Encode v@.index_logic(0) to get element-at-0 term
    let index_expr = method_call(view(var("v")), "index_logic", vec![int(0)]);
    let elem_0_term = encoder
        .encode_pure(&index_expr)
        .expect("v@.index_logic(0) should encode");

    // Assert len(v_view) >= 1 (container has at least one element)
    let one = encoder.solver_mut().int_const(1);
    let has_element = encoder.solver_mut().ge(len_term, one);
    encoder.assert_term(has_element);

    // Assert index(v_view, 0) <= 0 (violates the > 0 invariant)
    let zero_val = encoder.solver_mut().int_const(0);
    let elem_le_zero = encoder.solver_mut().le(elem_0_term, zero_val);
    encoder.assert_term(elem_le_zero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "inlined body invariant (>0) + element <= 0 should be Unsat: {result:?}"
    );
}

/// Trivially-true body (`Bool(true)`) should short-circuit without asserting.
#[test]
#[timeout(30000)]
fn test_container_element_invariant_body_trivial_true_skips() {
    use super::super::PureExpr;

    let mut encoder = AYEncoder::new_with_quantifiers();
    let body = PureExpr::Bool(true);
    let result = encoder.assert_container_element_invariant_body("v_view", "self_param", &body);
    assert!(
        result.is_ok(),
        "trivially-true body should short-circuit: {result:?}"
    );
}
