// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Int→non-Int redeclaration should upgrade, not error. Int is the universal
/// fallback default from `infer_expr_sort` — upgrading to a richer sort when
/// type evidence arrives is correct behaviour (#1965, #951, #835).
#[test]
#[timeout(30000)]
fn test_get_or_declare_var_int_to_non_int_upgrades_sort() {
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::Int);
    assert!(
        first.is_ok(),
        "first declaration of 'x' as Int should succeed: {first:?}"
    );

    // Int→Bool: should upgrade, not error.
    let upgraded = encoder.get_or_declare_var("x", Sort::Bool);
    assert!(
        upgraded.is_ok(),
        "Int→Bool should upgrade, not error: {upgraded:?}"
    );
    assert_eq!(
        encoder.var_sort("x"),
        Some(&Sort::Bool),
        "var_sorts should reflect Bool after Int→Bool upgrade"
    );
}

/// Non-Int→different non-Int is a genuine conflict and must error.
#[test]
#[timeout(30000)]
fn test_get_or_declare_var_non_int_conflict_returns_error() {
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::Bool);
    assert!(
        first.is_ok(),
        "first declaration of 'x' as Bool should succeed: {first:?}"
    );

    let conflict = encoder.get_or_declare_var("x", Sort::seq(Sort::Int));
    assert!(
        conflict.is_err(),
        "Bool→Seq should return EncodingError; got {conflict:?}"
    );
    assert!(
        matches!(conflict, Err(EncodingError::SortConflict { .. })),
        "Bool→Seq should return SortConflict variant; got: {conflict:?}"
    );
}

/// Declaring the same variable with the same sort twice should succeed
/// and return the same term.
#[test]
#[timeout(30000)]
fn test_get_or_declare_var_same_sort_reuses_term() {
    let mut encoder = AYEncoder::new();

    let first = encoder
        .get_or_declare_var("y", Sort::Bool)
        .expect("first declaration should succeed");
    let second = encoder
        .get_or_declare_var("y", Sort::Bool)
        .expect("same-sort redeclaration should succeed");
    assert_eq!(
        first, second,
        "same variable with same sort should return identical Term"
    );
}
