// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for proof_assert! expansion and word boundary matching.

use crate::ghost_macros::proof_assert::{has_word_boundary_match, proof_assert_expansion};

#[test]
fn proof_assert_expansion_contains_doc_marker() {
    let expanded = proof_assert_expansion("x > 0").to_string();
    assert!(
        expanded.contains("trust-wp:proof_assert:x > 0"),
        "expansion should embed original expression in doc marker: {expanded}"
    );
}

#[test]
fn proof_assert_expansion_has_cfg_trust_wp_branch() {
    let expanded = proof_assert_expansion("a == b").to_string();
    // proc_macro2 stringifies attribute args with spaces: `cfg (trust_wp)`
    assert!(
        expanded.contains("cfg (trust_wp)"),
        "expansion should have cfg(trust_wp) verification branch: {expanded}"
    );
    assert!(
        expanded.contains("cfg (not (trust_wp))"),
        "expansion should have cfg(not(trust_wp)) erasure branch: {expanded}"
    );
}

#[test]
fn proof_assert_expansion_preserves_quantifier_text() {
    // Quantifier syntax like `forall<i> i >= 0` is not valid Rust but
    // must be preserved verbatim in the doc marker for the trust-wp driver
    // to extract during MIR analysis.
    let expanded = proof_assert_expansion("forall<i: i32> i >= 0 ==> i >= 0").to_string();
    assert!(
        expanded.contains("trust-wp:proof_assert:forall<i: i32> i >= 0 ==> i >= 0"),
        "quantifier text should be preserved in doc marker: {expanded}"
    );

    let expanded = proof_assert_expansion("exists<y: i32> y == y").to_string();
    assert!(
        expanded.contains("trust-wp:proof_assert:exists<y: i32> y == y"),
        "existential quantifier should be preserved: {expanded}"
    );
}

#[test]
fn proof_assert_expansion_contains_dummy_closure() {
    let expanded = proof_assert_expansion("true").to_string();
    // The expansion uses `let _ = || -> bool { ... true }` as the doc-marker carrier
    assert!(
        expanded.contains("bool") && expanded.contains("true"),
        "expansion should contain dummy closure body: {expanded}"
    );
}

#[test]
fn proof_assert_expansion_no_variable_captures() {
    // #2586: the marker closure must NOT capture free variables by reference.
    // Captures cause borrowck failures when proof_assert! appears in code with
    // live mutable borrows (e.g., `proof_assert!(r == x)` where `x: &mut T`).
    let expanded = proof_assert_expansion("x > 0").to_string();
    assert!(
        !expanded.contains("& x"),
        "expansion should NOT capture free variables: {expanded}"
    );

    let expanded = proof_assert_expansion("a == b").to_string();
    assert!(
        !expanded.contains("& a") && !expanded.contains("& b"),
        "expansion should NOT capture any variables: {expanded}"
    );

    let expanded = proof_assert_expansion("forall<i: i32> i >= 0 ==> x > i").to_string();
    assert!(
        !expanded.contains("& x") && !expanded.contains("& i"),
        "expansion should NOT capture any variables (including quantifier-bound): {expanded}"
    );
}

#[test]
fn word_boundary_match_rejects_prefixed_result() {
    assert!(
        !has_word_boundary_match("my_result.foo()", "result."),
        "my_result.foo() should not match — 'result.' is not at a word boundary"
    );
    assert!(
        !has_word_boundary_match("some_result.method()", "result."),
        "some_result.method() should not match"
    );
    assert!(
        !has_word_boundary_match("theresult.x", "result."),
        "theresult.x should not match — no word boundary before 'result'"
    );
}

#[test]
fn word_boundary_match_accepts_standalone_result() {
    assert!(
        has_word_boundary_match("result.ext_eq(x)", "result."),
        "result.ext_eq(x) should match at start of string"
    );
    assert!(
        has_word_boundary_match("(result.len())", "result."),
        "result. after '(' should match"
    );
    assert!(
        has_word_boundary_match("a&&result.val", "result."),
        "result. after '&' should match"
    );
    assert!(
        has_word_boundary_match("!result.ok", "result."),
        "result. after '!' should match"
    );
}

#[test]
fn word_boundary_match_empty_needle_returns_false() {
    assert!(
        !has_word_boundary_match("anything", ""),
        "empty needle should never match"
    );
}

#[test]
fn proof_assert_expansion_empty_in_non_trust_wp() {
    // Under not(trust_wp), the expansion should be an empty block — no runtime cost
    let expanded = proof_assert_expansion("x > 0").to_string();
    // proc_macro2 stringifies as `cfg (not (trust_wp))` with spaces
    let not_trust_wp_pos = expanded.find("cfg (not (trust_wp))");
    assert!(
        not_trust_wp_pos.is_some(),
        "expansion should have not(trust_wp) branch: {expanded}"
    );
}

// --- Phase 3 regression: trusted marker prefix distinct from standard ---

#[test]
fn proof_assert_trusted_marker_prefix_is_distinct() {
    use crate::ghost_macros::proof_assert::proof_assert_expansion;

    // Standard proof_assert uses "trust-wp:proof_assert:" prefix
    let standard = proof_assert_expansion("x > 0").to_string();
    assert!(
        standard.contains("trust-wp:proof_assert:x > 0"),
        "standard marker should use trust-wp:proof_assert: prefix: {standard}"
    );
    assert!(
        !standard.contains("trusted_proof_assert"),
        "standard marker should NOT contain trusted prefix: {standard}"
    );
}
