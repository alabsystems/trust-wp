// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// 4. check_tuple_exhaustive / cross_product_covered (via match encoding)
// =============================================================================

/// Verify that encoding a complete 2×2 tuple match with all Option×Option
/// combinations succeeds (exercises check_tuple_exhaustive).
///
/// Re: #901 — check_tuple_exhaustive has zero direct tests
#[test]
#[timeout(30000)]
fn test_exhaustive_tuple_2x2_match_encodes_successfully() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("pair"),
        vec![
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("a".to_string()))),
                    },
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("b".to_string()))),
                    },
                ]),
                add(var("a"), var("b")),
            ),
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("a".to_string()))),
                    },
                    Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                ]),
                var("a"),
            ),
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("b".to_string()))),
                    },
                ]),
                var("b"),
            ),
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                ]),
                int(0),
            ),
        ],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "complete 2×2 tuple match should encode: {:?}",
        result.err()
    );
}

/// Verify that encoding an incomplete 2×2 tuple match (missing one
/// combination) returns an error.
///
/// Re: #901 — tuple cross_product_covered missing combination
#[test]
#[timeout(30000)]
fn test_non_exhaustive_tuple_2x2_match_returns_error() {
    let mut encoder = AYEncoder::new();

    // Missing (None, None)
    let expr = match_expr(
        var("pair"),
        vec![
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("a".to_string()))),
                    },
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("b".to_string()))),
                    },
                ]),
                add(var("a"), var("b")),
            ),
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("a".to_string()))),
                    },
                    Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                ]),
                var("a"),
            ),
            (
                Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("b".to_string()))),
                    },
                ]),
                var("b"),
            ),
        ],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "incomplete tuple match (missing None×None) should fail: {:?}",
        result.ok()
    );
}

/// Verify that tuple match with wildcard at one position is exhaustive.
///
/// Re: #901 — wildcard handling in check_tuple_exhaustive
#[test]
#[timeout(30000)]
fn test_tuple_with_wildcard_position_encodes_successfully() {
    let mut encoder = AYEncoder::new();

    let expr = match_expr(
        var("pair"),
        vec![
            (
                Pattern::Tuple(vec![
                    Pattern::Wildcard,
                    Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("b".to_string()))),
                    },
                ]),
                var("b"),
            ),
            (
                Pattern::Tuple(vec![
                    Pattern::Wildcard,
                    Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                ]),
                int(0),
            ),
        ],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "wildcard + complete constructors should encode: {:?}",
        result.err()
    );
}
