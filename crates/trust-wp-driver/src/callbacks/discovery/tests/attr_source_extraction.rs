// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn basic_extraction() {
    let src = r#"fn f() { #[invariant(x > 0)] loop {} }"#;
    let result = extract_attr_args_from_source(src, "invariant");
    assert_eq!(result, vec!["x > 0"]);
}

#[test]
fn nested_parens() {
    let src = r#"fn f() { #[invariant(foo(x) > 0)] loop {} }"#;
    let result = extract_attr_args_from_source(src, "invariant");
    assert_eq!(result, vec!["foo(x) > 0"]);
}

#[test]
fn string_literal_with_parens() {
    let src = r#"fn f() { #[invariant(s.contains("("))] loop {} }"#;
    let result = extract_attr_args_from_source(src, "invariant");
    assert_eq!(result, vec![r#"s.contains("(")"#]);
}

#[test]
fn string_literal_with_close_paren() {
    let src = r#"fn f() { #[invariant(s.contains(")"))] loop {} }"#;
    let result = extract_attr_args_from_source(src, "invariant");
    assert_eq!(result, vec![r#"s.contains(")")"#]);
}

#[test]
fn string_literal_with_escaped_quote() {
    let src = r#"fn f() { #[invariant(s.contains("\"("))] loop {} }"#;
    let result = extract_attr_args_from_source(src, "invariant");
    assert_eq!(result, vec![r#"s.contains("\"(")"#]);
}

#[test]
fn block_comment_with_parens() {
    let src = "fn f() { #[invariant(x > 0 /* x must be positive (always) */)] loop {} }";
    let result = extract_attr_args_from_source(src, "invariant");
    assert_eq!(result, vec!["x > 0 /* x must be positive (always) */"]);
}

#[test]
fn line_comment_with_parens() {
    let src = "fn f() {\n#[invariant(\nx > 0 // must be positive (always)\n)]\nloop {} }";
    let result = extract_attr_args_from_source(src, "invariant");
    assert_eq!(result, vec!["x > 0 // must be positive (always)"]);
}

#[test]
fn multiple_attrs() {
    let src = r#"fn f() { #[invariant(a > 0)] #[invariant(b < 10)] loop {} }"#;
    let result = extract_attr_args_from_source(src, "invariant");
    assert_eq!(result, vec!["a > 0", "b < 10"]);
}

#[test]
fn variant_attr() {
    let src = r#"fn f() { #[variant(n - i)] loop {} }"#;
    let result = extract_attr_args_from_source(src, "variant");
    assert_eq!(result, vec!["n - i"]);
}

#[test]
fn no_match_different_attr() {
    let src = r#"fn f() { #[requires(x > 0)] loop {} }"#;
    let result = extract_attr_args_from_source(src, "invariant");
    assert!(result.is_empty());
}
