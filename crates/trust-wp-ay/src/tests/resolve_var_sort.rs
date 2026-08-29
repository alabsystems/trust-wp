// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct unit tests for `AYEncoder::resolve_var_sort` (#1319).
//!
//! `resolve_var_sort` checks (in order):
//! 1. Already-declared variables in the solver (`var_sorts`)
//! 2. Registered sort hints (`sort_hints`)
//! 3. Returns `None` if neither found
//!
//! Prior to this file, the function had zero direct test coverage.

use ay_dpll::api::Sort;
use ntest::timeout;

use super::{super::AYEncoder, helpers::*};

// =============================================================================
// resolve_var_sort: basic fallback chain
// =============================================================================

#[test]
#[timeout(30000)]
fn test_resolve_unknown_var_returns_none() {
    let mut encoder = AYEncoder::new();
    assert_eq!(
        encoder.resolve_var_sort("unknown"),
        None,
        "Undeclared variable with no sort hint should return None"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_declared_int_var() {
    let mut encoder = AYEncoder::new();
    // Declare "x" as Int via get_or_declare_var
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x as Int");
    let resolved = encoder.resolve_var_sort("x");
    assert_eq!(
        resolved,
        Some(Sort::Int),
        "Declared Int variable should resolve to Int: {resolved:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_declared_bool_var() {
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("flag", Sort::Bool)
        .expect("declare flag as Bool");
    let resolved = encoder.resolve_var_sort("flag");
    assert_eq!(
        resolved,
        Some(Sort::Bool),
        "Declared Bool variable should resolve to Bool: {resolved:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_bool_hint_without_declaration() {
    let mut encoder = AYEncoder::new();
    // Register Bool hint via mark_bool_var (no solver declaration)
    encoder.mark_bool_var("p");
    let resolved = encoder.resolve_var_sort("p");
    assert_eq!(
        resolved,
        Some(Sort::Bool),
        "Bool sort hint should resolve to Bool when no declaration exists: {resolved:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_seq_hint_without_declaration() {
    let mut encoder = AYEncoder::new();
    // Register Seq hint via register_sort_hints with a Seq-producing expression
    let seq_expr = method_call(view(var("v")), "len", vec![]);
    encoder.register_sort_hints(&[seq_expr]);
    let resolved = encoder.resolve_var_sort("v_view");
    assert!(
        resolved.is_some(),
        "Seq sort hint should resolve to a Seq sort, got None"
    );
    // The Seq sort is now a native Seq(Int) sort (not Uninterpreted)
    match resolved {
        Some(Sort::Seq(_)) => {} // native Seq sort — correct
        other => panic!("Expected Seq(Int), got {other:?}"),
    }
}

// =============================================================================
// resolve_var_sort: precedence (declared sort wins over hint)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_declared_sort_takes_precedence_over_hint() {
    let mut encoder = AYEncoder::new();
    // First register a Bool hint
    encoder.mark_bool_var("x");
    // Then declare "x" as Int in the solver
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x as Int");
    let resolved = encoder.resolve_var_sort("x");
    assert_eq!(
        resolved,
        Some(Sort::Int),
        "Declared sort (Int) should take precedence over Bool hint: {resolved:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_hint_used_when_no_declaration() {
    let mut encoder = AYEncoder::new();
    // Only register a Bool hint, no declaration
    encoder.mark_bool_var("y");
    // Declare a *different* variable to confirm no cross-contamination
    encoder
        .get_or_declare_var("z", Sort::Int)
        .expect("declare z as Int");
    let resolved_y = encoder.resolve_var_sort("y");
    assert_eq!(
        resolved_y,
        Some(Sort::Bool),
        "Variable with hint but no declaration should resolve from hint: {resolved_y:?}"
    );
    let resolved_z = encoder.resolve_var_sort("z");
    assert_eq!(
        resolved_z,
        Some(Sort::Int),
        "Variable with declaration should resolve from declaration: {resolved_z:?}"
    );
}
