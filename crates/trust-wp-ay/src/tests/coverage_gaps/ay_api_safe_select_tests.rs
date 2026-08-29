// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `safe_select`, `safe_store`, and `safe_apply` boundary
//! conditions (#2514 algorithm_audit).
//!
//! Coverage targets in `ay_api.rs`:
//! - `safe_select` (line 64): array select with error mapping
//! - `safe_store` (line 76): array store with error mapping
//! - `safe_apply` (line 44): function application with arity check
//! - `safe_declare_fun` (line 30): function declaration with error mapping
//!
//! These wrappers had no direct test coverage. The tests verify:
//! - Happy path: valid operations produce correct terms
//! - Error path: invalid operations produce descriptive EncodingError
//! - Semantic: select(store(arr, i, v), i) == v (array axiom)
//! - Arity: mismatched argument count is caught before solver dispatch

use ntest::timeout;

use super::*;

// ── safe_select ─────────────────────────────────────────────────────────

/// Happy path: select from a (Int → Int) array with an Int index.
#[test]
#[timeout(30000)]
fn test_safe_select_int_array_succeeds() {
    let mut encoder = AYEncoder::new_pure();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let arr = encoder
        .get_or_declare_var("arr", arr_sort)
        .expect("array var");
    let idx = encoder
        .get_or_declare_var("idx", Sort::Int)
        .expect("index var");

    let result = encoder.safe_select("test/select", arr, idx);
    assert!(
        result.is_ok(),
        "select from Int→Int array with Int index should succeed: {result:?}"
    );
}

/// Error path: select from a non-array term must fail.
#[test]
#[timeout(30000)]
fn test_safe_select_non_array_fails() {
    let mut encoder = AYEncoder::new_pure();
    let non_array = encoder
        .get_or_declare_var("scalar", Sort::Int)
        .expect("scalar var");
    let idx = encoder
        .get_or_declare_var("idx", Sort::Int)
        .expect("index var");

    let result = encoder.safe_select("test/non_array", non_array, idx);
    assert!(result.is_err(), "select from non-array term must fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("test/non_array") && err_msg.contains("select failed"),
        "error should contain context and 'select failed': {err_msg}"
    );
}

// ── safe_store ──────────────────────────────────────────────────────────

/// Happy path: store into a (Int → Int) array.
#[test]
#[timeout(30000)]
fn test_safe_store_int_array_succeeds() {
    let mut encoder = AYEncoder::new_pure();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let arr = encoder
        .get_or_declare_var("arr", arr_sort)
        .expect("array var");
    let idx = encoder
        .get_or_declare_var("idx", Sort::Int)
        .expect("index var");
    let val = encoder
        .get_or_declare_var("val", Sort::Int)
        .expect("value var");

    let result = encoder.safe_store("test/store", arr, idx, val);
    assert!(
        result.is_ok(),
        "store into Int→Int array should succeed: {result:?}"
    );
}

/// Error path: store into a non-array term must fail.
#[test]
#[timeout(30000)]
fn test_safe_store_non_array_fails() {
    let mut encoder = AYEncoder::new_pure();
    let non_array = encoder
        .get_or_declare_var("scalar", Sort::Int)
        .expect("scalar var");
    let idx = encoder
        .get_or_declare_var("idx", Sort::Int)
        .expect("index var");
    let val = encoder
        .get_or_declare_var("val", Sort::Int)
        .expect("value var");

    let result = encoder.safe_store("test/non_array_store", non_array, idx, val);
    assert!(result.is_err(), "store into non-array term must fail");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("test/non_array_store") && err_msg.contains("store failed"),
        "error should contain context and 'store failed': {err_msg}"
    );
}

// ── Semantic: select(store(arr, i, v), i) == v ──────────────────────────

/// Array axiom: select(store(arr, i, v), i) == v should be a tautology.
/// Assert the negation and check UNSAT.
#[test]
#[timeout(30000)]
fn test_safe_select_store_roundtrip_unsat() {
    let mut encoder = AYEncoder::new_pure();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let arr = encoder
        .get_or_declare_var("arr", arr_sort)
        .expect("array var");
    let idx = encoder
        .get_or_declare_var("idx", Sort::Int)
        .expect("index var");
    let val = encoder
        .get_or_declare_var("val", Sort::Int)
        .expect("value var");

    // store(arr, idx, val)
    let stored = encoder.safe_store("test/rt", arr, idx, val).expect("store");

    // select(store(arr, idx, val), idx)
    let selected = encoder.safe_select("test/rt", stored, idx).expect("select");

    // Assert selected != val — should be UNSAT by array axiom
    let neq = {
        let eq = encoder.eq_term(selected, val);
        encoder.solver_mut().not(eq)
    };
    encoder.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "select(store(arr, i, v), i) != v must be UNSAT: {result:?}"
    );
}

/// safe_apply arity check: mismatched arity returns descriptive error.
#[test]
#[timeout(30000)]
fn test_safe_apply_arity_mismatch_returns_error() {
    let mut encoder = AYEncoder::new_pure();
    // Declare a 2-arity function
    let func = encoder
        .safe_declare_fun(
            "test/arity",
            "arity_test_fn",
            &[Sort::Int, Sort::Int],
            Sort::Int,
        )
        .expect("declare");

    // Try to apply with wrong number of args (1 instead of 2)
    let x = encoder.get_or_declare_var("x", Sort::Int).expect("x var");
    let result = encoder.safe_apply("test/arity", &func, &[x]);
    assert!(result.is_err(), "arity mismatch must return error");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("arity mismatch")
            && err_msg.contains("expects 2")
            && err_msg.contains("got 1"),
        "error should describe arity mismatch: {err_msg}"
    );
}

/// safe_apply correct arity succeeds.
#[test]
#[timeout(30000)]
fn test_safe_apply_correct_arity_succeeds() {
    let mut encoder = AYEncoder::new_pure();
    let func = encoder
        .safe_declare_fun("test/apply_ok", "apply_ok_fn", &[Sort::Int], Sort::Bool)
        .expect("declare");

    let x = encoder.get_or_declare_var("x", Sort::Int).expect("x var");
    let result = encoder.safe_apply("test/apply_ok", &func, &[x]);
    assert!(
        result.is_ok(),
        "correct arity apply should succeed: {result:?}"
    );
}
