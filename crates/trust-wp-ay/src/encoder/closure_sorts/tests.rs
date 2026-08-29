// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `closure_sorts.rs`.
//!
//! The production module keeps the closure sort registration logic in the
//! parent file; these tests live in a sibling module to keep that file under
//! the file-size threshold.

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::{
    closure::{CaptureField, CaptureKind},
    formula::{ExprSort, PureExpr},
};

use super::*;

// ── closure_symbol_suffix tests ──────────────────────────────────────

#[test]
#[timeout(5000)]
fn test_closure_symbol_suffix_deterministic() {
    let a = closure_symbol_suffix("my::closure::DefId");
    let b = closure_symbol_suffix("my::closure::DefId");
    assert_eq!(a, b, "same input must produce identical hash");
}

#[test]
#[timeout(5000)]
fn test_closure_symbol_suffix_different_inputs_differ() {
    let a = closure_symbol_suffix("closure_a");
    let b = closure_symbol_suffix("closure_b");
    assert_ne!(a, b, "different def_ids should produce different suffixes");
}

#[test]
#[timeout(5000)]
fn test_closure_symbol_suffix_empty_input() {
    let suffix = closure_symbol_suffix("");
    assert_eq!(
        suffix.len(),
        16,
        "FNV-1a hash should produce a 16-char hex string"
    );
}

#[test]
#[timeout(5000)]
fn test_closure_symbol_suffix_hex_format() {
    let suffix = closure_symbol_suffix("test");
    // FNV-1a produces 64-bit hash → 16 hex chars
    assert_eq!(suffix.len(), 16, "suffix must be 16 hex characters");
    assert!(
        suffix.chars().all(|c| c.is_ascii_hexdigit()),
        "suffix must contain only hex digits, got: {suffix}"
    );
}

// ── closure_env_sort_name tests ──────────────────────────────────────

#[test]
#[timeout(5000)]
fn test_closure_env_sort_name_uninterpreted_match() {
    let sort = Sort::Uninterpreted("ClosureEnv_abc123".to_string());
    assert_eq!(
        closure_env_sort_name(&sort),
        Some("ClosureEnv_abc123"),
        "Uninterpreted sort with ClosureEnv_ prefix should match"
    );
}

#[test]
#[timeout(5000)]
fn test_closure_env_sort_name_uninterpreted_no_match() {
    let sort = Sort::Uninterpreted("Option_i32".to_string());
    assert_eq!(
        closure_env_sort_name(&sort),
        None,
        "Uninterpreted sort without ClosureEnv_ prefix should return None"
    );
}

#[test]
#[timeout(5000)]
fn test_closure_env_sort_name_int_returns_none() {
    assert_eq!(
        closure_env_sort_name(&Sort::Int),
        None,
        "Sort::Int should return None"
    );
}

#[test]
#[timeout(5000)]
fn test_closure_env_sort_name_bool_returns_none() {
    assert_eq!(
        closure_env_sort_name(&Sort::Bool),
        None,
        "Sort::Bool should return None"
    );
}

// ── register_closure_struct_sort tests ────────────────────────────────

#[test]
#[timeout(30000)]
fn test_register_closure_struct_sort_single_capture() {
    let mut encoder = AYEncoder::new();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    let sort = encoder
        .register_closure_struct_sort("test::closure_1", &captures)
        .expect("registering closure sort with one Int capture should succeed");
    assert!(
        matches!(sort, Sort::Datatype(_)),
        "registered sort should be a Datatype, got: {sort:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_register_closure_struct_sort_idempotent() {
    let mut encoder = AYEncoder::new();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByRef)];
    let sort1 = encoder
        .register_closure_struct_sort("test::closure_idem", &captures)
        .expect("first registration should succeed");
    let sort2 = encoder
        .register_closure_struct_sort("test::closure_idem", &captures)
        .expect("second registration with same captures should succeed");
    assert_eq!(
        format!("{sort1:?}"),
        format!("{sort2:?}"),
        "idempotent registration should return the same sort"
    );
}

#[test]
#[timeout(30000)]
fn test_register_closure_struct_sort_conflicting_captures_errors() {
    let mut encoder = AYEncoder::new();
    let captures_v1 = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    encoder
        .register_closure_struct_sort("test::closure_conflict", &captures_v1)
        .expect("first registration should succeed");

    let captures_v2 = vec![CaptureField::new("y", ExprSort::Bool, CaptureKind::ByRef)];
    let result = encoder.register_closure_struct_sort("test::closure_conflict", &captures_v2);
    assert!(
        result.is_err(),
        "registering same def_id with different captures should fail"
    );
}

#[test]
#[timeout(30000)]
fn test_register_closure_struct_sort_multiple_captures() {
    let mut encoder = AYEncoder::new();
    let captures = vec![
        CaptureField::new("a", ExprSort::Int, CaptureKind::ByValue),
        CaptureField::new("b", ExprSort::Bool, CaptureKind::ByRef),
        CaptureField::new("c", ExprSort::Int, CaptureKind::ByMutRef),
    ];
    let sort = encoder
        .register_closure_struct_sort("test::multi_capture", &captures)
        .expect("registering closure with 3 captures should succeed");
    assert!(
        matches!(sort, Sort::Datatype(_)),
        "multi-capture closure should produce a Datatype sort"
    );
}

// ── closure_capture_selector tests ────────────────────────────────────

#[test]
#[timeout(30000)]
fn test_closure_capture_selector_valid_index() {
    let mut encoder = AYEncoder::new();
    let captures = vec![
        CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue),
        CaptureField::new("y", ExprSort::Int, CaptureKind::ByRef),
    ];
    let sort = encoder
        .register_closure_struct_sort("test::sel", &captures)
        .expect("registration should succeed");
    let env = encoder
        .get_or_declare_var("env", sort)
        .expect("declaring env var should succeed");
    let selector_result = encoder.closure_capture_selector("test::sel", 0, env);
    assert!(
        selector_result.is_ok(),
        "selector for field 0 should succeed"
    );
}

#[test]
#[timeout(30000)]
fn test_tuple_get_on_closure_env_uses_native_capture_selector() {
    let mut encoder = AYEncoder::new();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    let sort = encoder
        .register_closure_struct_sort("test::tuple_get_bridge", &captures)
        .expect("registration should succeed");
    encoder
        .get_or_declare_var("closure", sort)
        .expect("declaring closure env should succeed");

    let result = encoder
        .encode_pure(&PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("closure".to_string(), None)],
        })
        .expect("tuple_get_0 over a closure env should encode");

    assert_eq!(
        encoder.solver.get_sort(result),
        Sort::Int,
        "closure capture selector should preserve the capture sort"
    );
    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "closure env field projection must not fall through to the tuple-get UF"
    );
}

#[test]
#[timeout(30000)]
fn test_closure_capture_selector_out_of_bounds() {
    let mut encoder = AYEncoder::new();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    let sort = encoder
        .register_closure_struct_sort("test::sel_oob", &captures)
        .expect("registration should succeed");
    let env = encoder
        .get_or_declare_var("env_oob", sort)
        .expect("declaring env var should succeed");
    let result = encoder.closure_capture_selector("test::sel_oob", 5, env);
    assert!(
        result.is_err(),
        "selector for out-of-bounds index should fail"
    );
}

#[test]
#[timeout(30000)]
fn test_closure_capture_selector_unregistered_def_id() {
    let mut encoder = AYEncoder::new();
    let dummy_term = encoder.solver.int_const(0);
    let result = encoder.closure_capture_selector("nonexistent::closure", 0, dummy_term);
    assert!(
        result.is_err(),
        "selector for unregistered closure should fail"
    );
}

// ── assert_capture_projection tests ──────────────────────────────────

#[test]
#[timeout(30000)]
fn test_assert_capture_projection_roundtrip() {
    let mut encoder = AYEncoder::new();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    encoder
        .register_closure_struct_sort("test::proj", &captures)
        .expect("registration should succeed");

    let bindings = vec![(0, "caller_x".to_string())];
    let result = encoder.assert_capture_projection("test::proj", "post_state", &bindings);
    assert!(
        result.is_ok(),
        "capture projection with valid bindings should succeed"
    );
}

#[test]
#[timeout(30000)]
fn test_assert_capture_projection_unregistered_errors() {
    let mut encoder = AYEncoder::new();
    let bindings = vec![(0, "caller_x".to_string())];
    let result = encoder.assert_capture_projection("nonexistent::closure", "post_state", &bindings);
    assert!(
        result.is_err(),
        "capture projection for unregistered closure should fail"
    );
}

// ── build_closure_constructor tests ──────────────────────────────────

#[test]
#[timeout(30000)]
fn test_build_closure_constructor_single_capture() {
    let mut encoder = AYEncoder::new();
    let captures = vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)];
    encoder
        .register_closure_struct_sort("test::ctor", &captures)
        .expect("registration should succeed");

    let ctor_term = encoder
        .build_closure_constructor("test::ctor", &["x_val"])
        .expect("building constructor with 1 capture should succeed");

    // The constructor term should exist and be usable with the solver.
    // Assert it equals itself - trivially SAT.
    let eq = encoder.eq_term(ctor_term, ctor_term);
    encoder.assert_solver_term("ctor_self_eq", eq);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "constructor self-equality should be SAT"
    );
}

#[test]
#[timeout(30000)]
fn test_build_closure_constructor_wrong_capture_count_errors() {
    let mut encoder = AYEncoder::new();
    let captures = vec![
        CaptureField::new("a", ExprSort::Int, CaptureKind::ByValue),
        CaptureField::new("b", ExprSort::Int, CaptureKind::ByRef),
    ];
    encoder
        .register_closure_struct_sort("test::ctor_bad", &captures)
        .expect("registration should succeed");

    let result = encoder.build_closure_constructor("test::ctor_bad", &["only_one"]);
    assert!(
        result.is_err(),
        "constructor with wrong number of capture vars should fail"
    );
}

// ── StructuredSortContext dispatch tests ─────────────────────────────

#[test]
#[timeout(30000)]
fn test_register_structured_sort_closure_struct() {
    let mut encoder = AYEncoder::new();
    let sort = encoder
        .register_structured_sort(StructuredSortContext::ClosureStruct {
            def_id: "test::structured".to_string(),
            captures: vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue)],
        })
        .expect("register_structured_sort should succeed for ClosureStruct");
    assert!(
        matches!(sort, Sort::Datatype(_)),
        "ClosureStruct registration should produce a Datatype sort"
    );
}
