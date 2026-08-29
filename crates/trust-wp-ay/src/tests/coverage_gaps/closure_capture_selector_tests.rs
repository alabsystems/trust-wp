// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `closure_capture_selector`, `assert_capture_projection`, and
//! `build_closure_constructor` boundary conditions (#2514 algorithm_audit).
//!
//! Coverage targets in `closure_sorts.rs`:
//! - `closure_capture_selector` (line 198): selector term for closure capture field
//! - `assert_capture_projection` (line 253): capture projection assertions
//! - `build_closure_constructor` (line 289): closure constructor term assembly
//!
//! These functions had no direct test coverage. The boundary conditions tested
//! here exercise: bounds checking, empty captures, unregistered closures, and
//! the interaction between selector lookup and bounds validation.

use ntest::timeout;
use trust_wp_core::{
    closure::{CaptureField, CaptureKind},
    formula::ExprSort,
};

use super::*;
use crate::encoder::closure_sorts::StructuredSortContext;

// ── Helpers ─────────────────────────────────────────────────────────────

/// Register a closure struct sort with the given captures and return the sort.
fn register_closure(encoder: &mut AYEncoder, def_id: &str, captures: Vec<CaptureField>) -> Sort {
    encoder
        .register_structured_sort(StructuredSortContext::ClosureStruct {
            def_id: def_id.to_string(),
            captures,
        })
        .expect("closure sort registration should succeed")
}

// ── closure_capture_selector ────────────────────────────────────────────

/// Happy path: select capture field 0 from a single-capture closure.
#[test]
#[timeout(30000)]
fn test_closure_capture_selector_single_capture_field_0() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    let closure_sort = register_closure(&mut encoder, "test::closure#0", captures);

    // Declare an env variable with the closure sort
    let env_term = encoder
        .get_or_declare_var("env", closure_sort)
        .expect("env var");

    let result = encoder.closure_capture_selector("test::closure#0", 0, env_term);
    assert!(
        result.is_ok(),
        "field 0 of single-capture closure should succeed: {result:?}"
    );
}

/// Boundary: select the last field of a multi-capture closure (index == len-1).
#[test]
#[timeout(30000)]
fn test_closure_capture_selector_last_field_boundary() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![
        CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue),
        CaptureField::new("y", ExprSort::Bool, CaptureKind::ByRef),
        CaptureField::new("z", ExprSort::Int, CaptureKind::ByMutRef),
    ];
    let closure_sort = register_closure(&mut encoder, "test::multi#0", captures);
    let env_term = encoder
        .get_or_declare_var("env", closure_sort)
        .expect("env var");

    // Index 2 = last field (len is 3)
    let result = encoder.closure_capture_selector("test::multi#0", 2, env_term);
    assert!(result.is_ok(), "index == len-1 should succeed: {result:?}");
}

/// Off-by-one: field_index == captures.len() must fail (one past the end).
#[test]
#[timeout(30000)]
fn test_closure_capture_selector_index_equals_len_fails() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![
        CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue),
        CaptureField::new("y", ExprSort::Bool, CaptureKind::ByRef),
    ];
    let closure_sort = register_closure(&mut encoder, "test::oob#0", captures);
    let env_term = encoder
        .get_or_declare_var("env", closure_sort)
        .expect("env var");

    // Index 2 = len, should be out of bounds
    let result = encoder.closure_capture_selector("test::oob#0", 2, env_term);
    assert!(
        result.is_err(),
        "field_index == captures.len() must return error"
    );
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("out of bounds"),
        "error should mention 'out of bounds': {err_msg}"
    );
}

/// Off-by-one: field_index far beyond length also fails.
#[test]
#[timeout(30000)]
fn test_closure_capture_selector_index_far_beyond_len_fails() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    let closure_sort = register_closure(&mut encoder, "test::far_oob#0", captures);
    let env_term = encoder
        .get_or_declare_var("env", closure_sort)
        .expect("env var");

    let result = encoder.closure_capture_selector("test::far_oob#0", 100, env_term);
    assert!(
        result.is_err(),
        "field_index=100 with 1 capture must return error"
    );
}

/// Empty captures closure: field_index 0 must fail (no fields at all).
#[test]
#[timeout(30000)]
fn test_closure_capture_selector_empty_captures_index_0_fails() {
    let mut encoder = AYEncoder::new_pure();
    let closure_sort = register_closure(&mut encoder, "test::empty#0", vec![]);
    let env_term = encoder
        .get_or_declare_var("env", closure_sort)
        .expect("env var");

    let result = encoder.closure_capture_selector("test::empty#0", 0, env_term);
    assert!(
        result.is_err(),
        "field_index=0 with empty captures must return error"
    );
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("out of bounds") && err_msg.contains("0 captures"),
        "error should mention 0 captures: {err_msg}"
    );
}

/// Unregistered closure def_id must fail.
#[test]
#[timeout(30000)]
fn test_closure_capture_selector_unregistered_closure_fails() {
    let mut encoder = AYEncoder::new_pure();
    // Don't register anything — use a fresh Int term as a dummy
    let dummy_term = encoder
        .get_or_declare_var("dummy", Sort::Int)
        .expect("dummy var");

    let result = encoder.closure_capture_selector("nonexistent::closure#0", 0, dummy_term);
    assert!(
        result.is_err(),
        "unregistered closure def_id must return error"
    );
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("not registered"),
        "error should mention 'not registered': {err_msg}"
    );
}

// ── assert_capture_projection ───────────────────────────────────────────

/// Happy path: project capture fields back to caller variables.
#[test]
#[timeout(30000)]
fn test_assert_capture_projection_single_binding() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    let _sort = register_closure(&mut encoder, "test::proj#0", captures);

    let result = encoder.assert_capture_projection(
        "test::proj#0",
        "post_state",
        &[(0, "caller_x".to_string())],
    );
    assert!(
        result.is_ok(),
        "single-binding projection should succeed: {result:?}"
    );
}

/// Empty capture_bindings is a no-op — should succeed without asserting anything.
#[test]
#[timeout(30000)]
fn test_assert_capture_projection_empty_bindings_succeeds() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    let _sort = register_closure(&mut encoder, "test::noop#0", captures);

    let result = encoder.assert_capture_projection("test::noop#0", "post_state", &[]);
    assert!(
        result.is_ok(),
        "empty capture bindings should succeed: {result:?}"
    );
}

/// Multiple bindings for a multi-capture closure.
#[test]
#[timeout(30000)]
fn test_assert_capture_projection_multi_binding() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![
        CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue),
        CaptureField::new("y", ExprSort::Bool, CaptureKind::ByRef),
    ];
    let _sort = register_closure(&mut encoder, "test::multi_proj#0", captures);

    let result = encoder.assert_capture_projection(
        "test::multi_proj#0",
        "post_state",
        &[(0, "caller_x".to_string()), (1, "caller_y".to_string())],
    );
    assert!(
        result.is_ok(),
        "multi-binding projection should succeed: {result:?}"
    );
}

/// Out-of-bounds field_index in bindings must fail.
#[test]
#[timeout(30000)]
fn test_assert_capture_projection_oob_field_index_fails() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    let _sort = register_closure(&mut encoder, "test::oob_proj#0", captures);

    let result = encoder.assert_capture_projection(
        "test::oob_proj#0",
        "post_state",
        &[(1, "caller_x".to_string())], // index 1 with only 1 capture
    );
    assert!(
        result.is_err(),
        "field_index=1 with 1 capture in bindings must fail"
    );
}

/// Unregistered closure in projection must fail.
#[test]
#[timeout(30000)]
fn test_assert_capture_projection_unregistered_closure_fails() {
    let mut encoder = AYEncoder::new_pure();

    let result = encoder.assert_capture_projection(
        "nonexistent::closure#0",
        "post_state",
        &[(0, "caller_x".to_string())],
    );
    assert!(result.is_err(), "unregistered closure must return error");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("not registered"),
        "error should mention 'not registered': {err_msg}"
    );
}

// ── build_closure_constructor ───────────────────────────────────────────

/// Happy path: construct a closure env term with matching capture vars.
#[test]
#[timeout(30000)]
fn test_build_closure_constructor_single_capture() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    let _sort = register_closure(&mut encoder, "test::ctor#0", captures);

    let result = encoder.build_closure_constructor("test::ctor#0", &["x_val"]);
    assert!(
        result.is_ok(),
        "single-capture constructor should succeed: {result:?}"
    );
}

/// Arity mismatch: too few capture vars.
#[test]
#[timeout(30000)]
fn test_build_closure_constructor_too_few_vars_fails() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![
        CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue),
        CaptureField::new("y", ExprSort::Bool, CaptureKind::ByRef),
    ];
    let _sort = register_closure(&mut encoder, "test::ctor_few#0", captures);

    let result = encoder.build_closure_constructor("test::ctor_few#0", &["x_val"]);
    assert!(result.is_err(), "too few capture vars must fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("expected 2") && err_msg.contains("got 1"),
        "error should mention arity mismatch: {err_msg}"
    );
}

/// Arity mismatch: too many capture vars.
#[test]
#[timeout(30000)]
fn test_build_closure_constructor_too_many_vars_fails() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    let _sort = register_closure(&mut encoder, "test::ctor_many#0", captures);

    let result = encoder.build_closure_constructor("test::ctor_many#0", &["a", "b"]);
    assert!(result.is_err(), "too many capture vars must fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("expected 1") && err_msg.contains("got 2"),
        "error should mention arity mismatch: {err_msg}"
    );
}

/// Empty captures constructor: zero-arity constructor should succeed.
#[test]
#[timeout(30000)]
fn test_build_closure_constructor_zero_captures() {
    let mut encoder = AYEncoder::new_pure();
    let _sort = register_closure(&mut encoder, "test::ctor_empty#0", vec![]);

    let result = encoder.build_closure_constructor("test::ctor_empty#0", &[]);
    assert!(
        result.is_ok(),
        "zero-capture constructor should succeed: {result:?}"
    );
}

/// Unregistered closure constructor must fail.
#[test]
#[timeout(30000)]
fn test_build_closure_constructor_unregistered_fails() {
    let mut encoder = AYEncoder::new_pure();

    let result = encoder.build_closure_constructor("nonexistent::closure#0", &["x_val"]);
    assert!(result.is_err(), "unregistered closure must return error");
}

// ── Round-trip: constructor + selector ───────────────────────────────────

/// Datatype round-trip: construct a closure env, select each field, and verify
/// the selected values are semantically equivalent to the inputs.
///
/// This is the key algebraic property: selector(constructor(a, b)) == a for field 0.
#[test]
#[timeout(30000)]
fn test_closure_constructor_selector_roundtrip_unsat() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![
        CaptureField::new("a", ExprSort::Int, CaptureKind::ByValue),
        CaptureField::new("b", ExprSort::Int, CaptureKind::ByMutRef),
    ];
    let _sort = register_closure(&mut encoder, "test::roundtrip#0", captures);

    // Build constructor: mk_closure_env(a_val, b_val)
    let ctor_term = encoder
        .build_closure_constructor("test::roundtrip#0", &["a_val", "b_val"])
        .expect("constructor");

    // Select field 0 from the constructor term
    let sel_0 = encoder
        .closure_capture_selector("test::roundtrip#0", 0, ctor_term)
        .expect("selector 0");

    // The selected value should equal a_val
    let a_val = encoder
        .get_or_declare_var("a_val", Sort::Int)
        .expect("a_val");

    // Assert sel_0 != a_val — should be UNSAT by datatype round-trip
    let neq = {
        let eq = encoder.eq_term(sel_0, a_val);
        encoder.solver_mut().not(eq)
    };
    encoder.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "selector(constructor(a, b), 0) != a must be UNSAT: {result:?}"
    );
}

/// Datatype round-trip for field 1 (non-first field).
#[test]
#[timeout(30000)]
fn test_closure_constructor_selector_roundtrip_field_1_unsat() {
    let mut encoder = AYEncoder::new_pure();
    let captures = vec![
        CaptureField::new("a", ExprSort::Int, CaptureKind::ByValue),
        CaptureField::new("b", ExprSort::Int, CaptureKind::ByMutRef),
    ];
    let _sort = register_closure(&mut encoder, "test::rt1#0", captures);

    let ctor_term = encoder
        .build_closure_constructor("test::rt1#0", &["a_val", "b_val"])
        .expect("constructor");

    // Select field 1
    let sel_1 = encoder
        .closure_capture_selector("test::rt1#0", 1, ctor_term)
        .expect("selector 1");

    let b_val = encoder
        .get_or_declare_var("b_val", Sort::Int)
        .expect("b_val");

    let neq = {
        let eq = encoder.eq_term(sel_1, b_val);
        encoder.solver_mut().not(eq)
    };
    encoder.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "selector(constructor(a, b), 1) != b must be UNSAT: {result:?}"
    );
}
