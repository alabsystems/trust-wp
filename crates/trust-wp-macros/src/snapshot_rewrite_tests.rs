// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `snapshot_rewrite` AST rewriting passes.

use quote::quote;
use syn::{Expr, ExprBlock};

use crate::snapshot_rewrite::{
    annotate_closure_params_with_int, annotate_closure_wildcards_only,
    rewrite_snapshot_call_arg_derefs, rewrite_such_that_closure_to_mapping,
    rewrite_unit_block_call_path_args,
};

fn parse_expr(tokens: proc_macro2::TokenStream) -> Expr {
    syn::parse2(tokens).expect("valid expression")
}

fn parse_block_expr(tokens: proc_macro2::TokenStream) -> ExprBlock {
    match syn::parse2::<Expr>(tokens).expect("valid expression") {
        Expr::Block(b) => b,
        _ => panic!("expected ExprBlock"),
    }
}

fn to_string(expr: &Expr) -> String {
    quote!(#expr).to_string()
}

// ── rewrite_snapshot_call_arg_derefs ──

#[test]
fn deref_arg_rewritten_to_into_inner() {
    let expr = parse_expr(quote!(f(*x)));
    let result = rewrite_snapshot_call_arg_derefs(expr);
    let s = to_string(&result);
    assert!(
        s.contains("into_inner"),
        "deref arg should become into_inner: {s}"
    );
    assert!(!s.contains("* x"), "deref should be removed: {s}");
}

#[test]
fn non_deref_arg_unchanged() {
    let expr = parse_expr(quote!(f(x)));
    let result = rewrite_snapshot_call_arg_derefs(expr.clone());
    assert_eq!(to_string(&result), to_string(&expr));
}

#[test]
fn method_call_deref_arg_rewritten() {
    let expr = parse_expr(quote!(obj.method(*y)));
    let result = rewrite_snapshot_call_arg_derefs(expr);
    let s = to_string(&result);
    assert!(
        s.contains("into_inner"),
        "method call deref arg should become into_inner: {s}"
    );
}

#[test]
fn deref_non_path_not_rewritten() {
    let expr = parse_expr(quote!(f(*(a + b))));
    let result = rewrite_snapshot_call_arg_derefs(expr);
    let s = to_string(&result);
    assert!(
        !s.contains("into_inner"),
        "deref of non-path should not be rewritten: {s}"
    );
}

#[test]
fn non_call_expr_passes_through() {
    let expr = parse_expr(quote!(a + *b));
    let result = rewrite_snapshot_call_arg_derefs(expr.clone());
    assert_eq!(to_string(&result), to_string(&expr));
}

// ── rewrite_unit_block_call_path_args ──

#[test]
fn path_arg_wrapped_with_snapshot_capture() {
    let block = parse_block_expr(quote!({
        f(x);
    }));
    let result = rewrite_unit_block_call_path_args(&block);
    let s = quote!(#result).to_string();
    assert!(
        s.contains("Snapshot") && s.contains("capture"),
        "path arg should be wrapped with Snapshot::capture: {s}"
    );
}

#[test]
fn literal_arg_not_wrapped() {
    let block = parse_block_expr(quote!({
        f(42);
    }));
    let result = rewrite_unit_block_call_path_args(&block);
    let s = quote!(#result).to_string();
    assert!(
        !s.contains("Snapshot"),
        "literal arg should NOT be wrapped: {s}"
    );
}

// ── annotate_closure_wildcards_only ──

#[test]
fn wildcard_param_gets_int_annotation() {
    let expr = parse_expr(quote!(|_| 42));
    let result = annotate_closure_wildcards_only(expr);
    let s = to_string(&result);
    assert!(
        s.contains("Int"),
        "wildcard param should get Int annotation: {s}"
    );
}

#[test]
fn named_param_not_annotated_by_wildcards_only() {
    let expr = parse_expr(quote!(|x| x + 1));
    let result = annotate_closure_wildcards_only(expr);
    let s = to_string(&result);
    assert!(
        !s.contains("Int"),
        "named param should NOT get Int from wildcards_only: {s}"
    );
}

#[test]
fn non_closure_unchanged() {
    let expr = parse_expr(quote!(42));
    let result = annotate_closure_wildcards_only(expr.clone());
    assert_eq!(to_string(&result), to_string(&expr));
}

// ── annotate_closure_params_with_int ──

#[test]
fn named_param_gets_int_annotation() {
    let expr = parse_expr(quote!(|x| x + 1));
    let result = annotate_closure_params_with_int(expr);
    let s = to_string(&result);
    assert!(
        s.contains("Int"),
        "named param should get Int from params_with_int: {s}"
    );
}

#[test]
fn already_typed_param_not_re_annotated() {
    let expr = parse_expr(quote!(|x: bool| x));
    let result = annotate_closure_params_with_int(expr);
    let s = to_string(&result);
    assert!(
        s.contains("bool"),
        "already-typed param should keep its type: {s}"
    );
}

#[test]
fn nested_closure_params_annotated() {
    let expr = parse_expr(quote!(f(|x| g(|y| y))));
    let result = annotate_closure_params_with_int(expr);
    let s = to_string(&result);
    let int_count = s.matches("Int").count();
    assert!(
        int_count >= 2,
        "both nested closure params should get Int: {s} (count={int_count})"
    );
}

// ── rewrite_such_that_closure_to_mapping ──

#[test]
fn such_that_closure_wrapped_in_mapping() {
    let expr = parse_expr(quote!(such_that(|x| x > 0)));
    let result = rewrite_such_that_closure_to_mapping(expr);
    let s = to_string(&result);
    assert!(
        s.contains("Mapping") && s.contains("from_closure"),
        "such_that closure should be wrapped in Mapping::from_closure: {s}"
    );
}

#[test]
fn such_that_non_closure_arg_not_wrapped() {
    let expr = parse_expr(quote!(such_that(predicate)));
    let result = rewrite_such_that_closure_to_mapping(expr);
    let s = to_string(&result);
    assert!(
        !s.contains("from_closure"),
        "non-closure arg should not be wrapped: {s}"
    );
}

#[test]
fn non_such_that_call_unchanged() {
    let expr = parse_expr(quote!(other_fn(|x| x)));
    let result = rewrite_such_that_closure_to_mapping(expr);
    let s = to_string(&result);
    assert!(
        !s.contains("Mapping"),
        "non-such_that call should not be modified: {s}"
    );
}
