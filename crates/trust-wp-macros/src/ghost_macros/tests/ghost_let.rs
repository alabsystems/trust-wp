// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for ghost_let! expansion.

use quote::quote;

use crate::ghost_macros::ghost_let::expand_ghost_let_tokens;

#[test]
fn ghost_let_expands_to_ghost_wrapped_bindings() {
    let expanded = expand_ghost_let_tokens(quote!(g = 41 + 1)).to_string();
    assert!(
        expanded.contains(":: trust_wp_std :: ghost :: Ghost :: new"),
        "expansion should construct Ghost<T>: {expanded}"
    );
    assert!(
        expanded.contains(":: trust_wp_std :: ghost :: Ghost :: conjure"),
        "non-trust-wp branch should erase with Ghost::conjure(): {expanded}"
    );
    assert!(
        expanded.contains("let g"),
        "expansion should preserve binding name: {expanded}"
    );
}

#[test]
fn ghost_let_preserves_mutability() {
    let expanded = expand_ghost_let_tokens(quote!(mut g = 0)).to_string();
    assert!(
        expanded.contains("let mut g"),
        "expansion should preserve `mut` binding: {expanded}"
    );
}

#[test]
fn ghost_let_emits_ghost_marker_for_driver_validator() {
    // trust-wp-driver's `GhostBlockFinder` keys on the `#[doc = "__trust_wp_ghost"]`
    // marker to know the `let` introduces a ghost block. Without it, the
    // driver rejects `Ghost::new(...)` (and any ghost extractions inside the
    // body) when `ghost_let!` is used in program context — breaking tests
    // like `reference/creusot/tests/should_succeed/ghost/ghost_let.rs`.
    let expanded = expand_ghost_let_tokens(quote!(g = 41 + 1)).to_string();
    assert!(
        expanded.contains("\"__trust_wp_ghost\""),
        "expansion must carry `__trust_wp_ghost` doc marker so the driver \
         treats the let as a ghost block: {expanded}"
    );
}

#[test]
fn ghost_let_invalid_shape_reports_parse_error() {
    let expanded = expand_ghost_let_tokens(quote!(x + y)).to_string();
    assert!(
        expanded.contains("ghost_let")
            && expanded.contains("expected")
            && expanded.contains("var = expr"),
        "invalid input should produce helpful parse error: {expanded}"
    );
}
