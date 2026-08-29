// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{parse_spec, *};

#[test]
fn test_parse_spec_simple() {
    let expr = parse_spec("result > 0").unwrap();
    assert!(matches!(expr, PureExpr::BinOp(_, _, _)));
}

#[test]
fn test_parse_spec_complex() {
    let expr = parse_spec("result == x + 1").unwrap();
    assert!(matches!(
        expr,
        PureExpr::BinOp(_, trust_wp_core::formula::BinOp::Eq, _)
    ));
}

#[test]
fn test_parse_spec_invalid() {
    assert!(parse_spec("invalid ((( syntax").is_none());
}

// Tests for from_spec_string helper

#[test]
fn test_from_spec_string_ensures_only() {
    let spec = StdSpec::from_spec_string(
        r"
            ensures: result == true
        ",
    );
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 1);
    assert_eq!(spec.ensures[0], "result == true");
}

#[test]
fn test_from_spec_string_with_requires() {
    let spec = StdSpec::from_spec_string(
        r"
            requires: *self != None
            ensures: Some(result) == *self
        ",
    );
    assert_eq!(spec.requires.len(), 1);
    assert_eq!(spec.requires[0], "*self != None");
    assert_eq!(spec.ensures.len(), 1);
    assert_eq!(spec.ensures[0], "Some(result) == *self");
}

#[test]
fn test_from_spec_string_multiline_ensures() {
    let spec = StdSpec::from_spec_string(
        r"
            ensures: match *self {
                Some(v) => result == v,
                None => result == default,
            }
        ",
    );
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 1);
    assert!(spec.ensures[0].contains("match"));
    assert!(spec.ensures[0].contains("Some(v)"));
}

#[test]
fn test_from_spec_string_multiple_ensures() {
    let spec = StdSpec::from_spec_string(
        r"
            ensures: (^self) == None
            ensures: result == old(*self)
        ",
    );
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 2);
}

#[test]
fn test_from_spec_string_ignores_comments() {
    let spec = StdSpec::from_spec_string(
        r"
            // doc comment before anything
            requires: *self != None // must be Some
            ensures: Some(result) == *self // result mirrors self
            // trailing comment
        ",
    );
    assert_eq!(spec.requires.len(), 1);
    assert_eq!(spec.requires[0], "*self != None");
    assert_eq!(spec.ensures.len(), 1);
    assert_eq!(spec.ensures[0], "Some(result) == *self");
}

#[test]
fn test_from_spec_string_strips_block_comments() {
    let spec = StdSpec::from_spec_string(
        r"
            /* leading block comment */
            requires: *self != None /* inline block */
            ensures: Some(result) == *self
        ",
    );
    assert_eq!(spec.requires.len(), 1);
    assert_eq!(spec.requires[0], "*self != None");
    assert_eq!(spec.ensures.len(), 1);
    assert_eq!(spec.ensures[0], "Some(result) == *self");
}

#[test]
fn test_from_spec_string_handles_nested_block_comments() {
    let spec = StdSpec::from_spec_string(
        r"
            requires: *self != None /* outer /* inner */ still outer */
            ensures: result == old(*self)
        ",
    );
    assert_eq!(spec.requires.len(), 1);
    assert_eq!(spec.requires[0], "*self != None");
    assert_eq!(spec.ensures.len(), 1);
    assert_eq!(spec.ensures[0], "result == old(*self)");
}

#[test]
fn test_from_spec_string_preserves_token_separation_with_block_comments() {
    let spec = StdSpec::from_spec_string(
        r"
            requires: a/* comment */b
            ensures: c/* multi
                line */d
        ",
    );
    assert_eq!(spec.requires.len(), 1);
    assert_eq!(spec.requires[0], "a b");
    assert_eq!(spec.ensures.len(), 1);
    assert_eq!(spec.ensures[0], "c d");
}

#[test]
fn test_from_spec_string_multiline_ensures_with_comments() {
    let spec = StdSpec::from_spec_string(
        r"
            ensures: match *self {
                Some(v) => result == v, // inline comment
                /* multi-line
                   block comment */
                None => result == default,
            }
        ",
    );
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 1);
    assert!(spec.ensures[0].contains("match"));
    assert!(spec.ensures[0].contains("Some(v) => result == v,"));
    assert!(spec.ensures[0].contains("None => result == default,"));
}

// Tests for newly exposed methods from trust-wp-std

#[test]
fn test_from_spec_string_params_parsing() {
    let spec = StdSpec::from_spec_string(
        r#"
        params: self, err
        ensures: match *self {
            Some(v) => result == Ok(v),
            None => result == Err(err),
        }
    "#,
    );
    assert_eq!(
        spec.param_names,
        Some(vec!["self".to_string(), "err".to_string()])
    );
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 1);
    assert!(spec.ensures[0].contains("Err(err)"));
}

#[test]
fn test_from_spec_string_no_params() {
    let spec = StdSpec::from_spec_string(
        r#"
        ensures: result == self + 1
    "#,
    );
    assert!(spec.param_names.is_none());
}

#[test]
fn test_from_spec_string_empty_params() {
    let spec = StdSpec::from_spec_string(
        r#"
        params:
        ensures: result == 0
    "#,
    );
    assert_eq!(
        spec.param_names,
        Some(vec![]),
        "empty params: line should produce Some(vec![]), not None"
    );
    assert_eq!(spec.ensures.len(), 1);
    assert_eq!(spec.ensures[0], "result == 0");
}

// --- Result: expect, unwrap_or_else, as_ref, as_mut (#607) ---
