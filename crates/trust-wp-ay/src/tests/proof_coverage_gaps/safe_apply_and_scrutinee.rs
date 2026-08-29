// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// 5. safe_apply — error path
// =============================================================================

/// Verify that `safe_apply` catches ay sort-mismatch panics and returns
/// `EncodingError` instead of propagating the panic.
///
/// Re: #901 — safe_apply error path has zero direct tests
#[test]
#[timeout(30000)]
fn test_safe_apply_sort_mismatch_returns_error() {
    let mut encoder = AYEncoder::new();

    // Declare a function expecting (Int) -> Int
    let int_sort = Sort::Int;
    let func_decl =
        encoder
            .solver
            .declare_fun("test_fn", std::slice::from_ref(&int_sort), int_sort.clone());

    // Create a Bool-sorted argument (mismatch)
    let bool_arg = encoder.solver.bool_const(true);

    // safe_apply should catch the panic and return an error
    let result = encoder.safe_apply("test_sort_mismatch", &func_decl, &[bool_arg]);
    assert!(
        result.is_err(),
        "safe_apply should return Err on sort mismatch, got Ok"
    );

    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("sort mismatch") || err_msg.contains("test_sort_mismatch"),
        "error message should mention sort mismatch or context: {err_msg}"
    );
}

/// Verify that `safe_apply` returns Ok on valid sort application.
///
/// Re: #901 — safe_apply success path (positive control)
#[test]
#[timeout(30000)]
fn test_safe_apply_valid_sorts_returns_ok() {
    let mut encoder = AYEncoder::new();

    let int_sort = Sort::Int;
    let func_decl =
        encoder
            .solver
            .declare_fun("add_one", std::slice::from_ref(&int_sort), int_sort.clone());

    let int_arg = encoder.solver.int_const(5);

    let result = encoder.safe_apply("test_valid", &func_decl, &[int_arg]);
    assert!(
        result.is_ok(),
        "safe_apply should return Ok for matching sorts"
    );
}

// =============================================================================
// 6. scrutinee_existing_datatype (indirect via encode_match_impl)
// =============================================================================
// `scrutinee_existing_datatype` is private on AYEncoder and is called
// internally from `encode_match_impl` when the scrutinee has a conflicting
// sort declaration. We test it indirectly: declare a variable with a Datatype
// sort, then encode a match on that variable. If the existing sort is used,
// encoding succeeds without sort mismatches.

/// Verify that matching on a variable already declared with OptionInt sort
/// succeeds (exercises scrutinee_existing_datatype when the auto-inferred
/// datatype conflicts with the pre-declared sort).
///
/// Re: #901 — indirect coverage for scrutinee_existing_datatype
#[test]
#[timeout(30000)]
fn test_match_on_pre_declared_datatype_var_succeeds() {
    let mut encoder = AYEncoder::new();

    // Pre-declare "result" with the OptionInt sort
    let dt = SwitchTarget::OptionInt.datatype();
    encoder
        .get_or_declare_var("result", Sort::Datatype(dt))
        .expect("should declare result");

    // Build a match on "result" using encode_pure (public API) which
    // internally calls encode_match_impl → scrutinee_existing_datatype
    // when the auto-inferred datatype conflicts with the pre-declared sort.
    let expr = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );

    let result = encoder.encode_pure(&expr);

    assert!(
        result.is_ok(),
        "match on pre-declared Datatype var should succeed: {:?}",
        result.err()
    );
}

/// Verify that matching on a variable declared with Int sort skips native
/// datatype encoding (the scrutinee_has_conflicting_sort path).
///
/// Re: #901 — conflicting sort causes datatype skip
#[test]
#[timeout(30000)]
fn test_match_on_int_declared_var_skips_datatype() {
    let mut encoder = AYEncoder::new();

    // Declare "x" with Int sort — conflicting with Option match inference
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("should declare x");

    // Build an Option-like match — the auto-inferred OptionInt datatype
    // will conflict with the Int declaration, so native datatype encoding
    // should be skipped entirely (both scrutinee_has_conflicting_sort and
    // scrutinee_existing_datatype paths).
    let expr = match_expr(
        var("x"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let result = encoder.encode_pure(&expr);

    // Encoding succeeds because the wildcard catch-all means ITE is valid
    // even without native datatype encoding
    assert!(
        result.is_ok(),
        "match on Int-declared var with wildcard should succeed: {:?}",
        result.err()
    );
}
