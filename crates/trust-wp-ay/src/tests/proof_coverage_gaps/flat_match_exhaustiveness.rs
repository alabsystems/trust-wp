// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use ntest::timeout;

use super::*;
use crate::Pattern;

// =============================================================================
// 3. check_flat_constructor_exhaustive (via match encoding)
// =============================================================================

/// Verify that encoding a complete Option match (Some + None, last arm is
/// constructor not wildcard) succeeds — exercising the exhaustiveness check.
///
/// The exhaustiveness check in `encode_match_impl` fires when the last arm
/// is NOT a catch-all. A complete set of constructors should pass the check.
///
/// Re: #901 — check_flat_constructor_exhaustive has zero direct tests
#[test]
#[timeout(30000)]
fn test_exhaustive_option_match_encodes_successfully() {
    let mut encoder = AYEncoder::new();

    // Complete Option match with None as last arm (not a wildcard)
    let expr = match_expr(
        var("opt"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                },
                var("x"),
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
        "complete Option match should encode: {:?}",
        result.err()
    );
}

/// Verify that encoding an incomplete match (missing constructor, last arm
/// not a wildcard) returns an error — exercising the non-exhaustive rejection.
///
/// Re: #901 — incomplete match detection
#[test]
#[timeout(30000)]
fn test_non_exhaustive_option_match_returns_error() {
    let mut encoder = AYEncoder::new();

    // Only Some, no None — last arm is a constructor, not catch-all
    let expr = match_expr(
        var("opt"),
        vec![(
            Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("x".to_string()))),
            },
            var("x"),
        )],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "single-arm Some match without wildcard should fail exhaustiveness"
    );
    let err = format!("{}", result.unwrap_err());
    assert!(
        err.contains("not exhaustive") || err.contains("catch-all"),
        "error should mention exhaustiveness: {err}"
    );
}

#[test]
#[timeout(30000)]
fn test_exhaustive_qualified_list_match_encodes_successfully() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("list"),
        vec![
            (
                Pattern::Constructor {
                    name: "List::Nil".to_string(),
                    inner: None,
                },
                int(0),
            ),
            (
                Pattern::Constructor {
                    name: "List::Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("head".to_string()),
                        Pattern::Binding("tail".to_string()),
                    ]))),
                },
                var("head"),
            ),
        ],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "qualified List::Nil/List::Cons match should be exhaustive: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_exhaustive_list_match_uses_arm_datatype_when_scrutinee_sort_is_stale() {
    let mut encoder = AYEncoder::new();
    let hashmap = DatatypeSort {
        name: "MyHashMap".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "MyHashMap".to_string(),
            fields: vec![DatatypeField {
                name: "myhashmap_buckets".to_string(),
                sort: Sort::seq(Sort::Int),
            }],
        }],
    };
    encoder.ensure_datatype_declared(&hashmap);
    encoder
        .get_or_declare_var("self", Sort::Datatype(hashmap))
        .expect("declare stale self datatype");

    let expr = match_expr(
        var("self"),
        vec![
            (
                Pattern::Constructor {
                    name: "List::Nil".to_string(),
                    inner: None,
                },
                int(0),
            ),
            (
                Pattern::Constructor {
                    name: "List::Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Wildcard,
                        Pattern::Wildcard,
                    ]))),
                },
                int(1),
            ),
        ],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "stale scrutinee datatype must not make exhaustive List arms look non-exhaustive: {result:?}"
    );
}

/// Verify that encoding a complete Result match succeeds.
///
/// Re: #901 — ResultIntInt exhaustiveness through encoding
#[test]
#[timeout(30000)]
fn test_exhaustive_result_match_encodes_successfully() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("res"),
        vec![
            (
                Pattern::Constructor {
                    name: "Ok".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                var("e"),
            ),
        ],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "complete Result match should encode: {:?}",
        result.err()
    );
}

/// Verify that encoding a user-defined enum match with all constructors succeeds.
///
/// Re: #901 — UserDefined exhaustiveness through encoding
#[test]
#[timeout(30000)]
fn test_exhaustive_user_defined_match_encodes_successfully() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("shape"),
        vec![
            (
                Pattern::Constructor {
                    name: "Shape::Circle".to_string(),
                    inner: Some(Box::new(Pattern::Binding("r".to_string()))),
                },
                var("r"),
            ),
            (
                Pattern::Constructor {
                    name: "Shape::Square".to_string(),
                    inner: Some(Box::new(Pattern::Binding("s".to_string()))),
                },
                var("s"),
            ),
        ],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "complete user-defined enum match should encode: {:?}",
        result.err()
    );
}
