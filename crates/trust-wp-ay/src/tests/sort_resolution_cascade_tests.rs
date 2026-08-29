// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the annotation-aware variable sort resolution cascade in
//! `encoder::sort_context::resolution`.
//!
//! `resolve_var_sort_or_int_with_annotation` is the main public entry point
//! for sort resolution. It has 7+ priority levels including ExprSort
//! annotations, derived-name suffix/prefix stripping, hint fallback, and
//! source-name plan gap detection. This cascade is where `SortFallbackToInt`
//! fires — the #1 unsoundness demotion category (45 sites).
//!
//! Coverage targets (zero direct tests prior to this file):
//! - `resolve_var_sort_or_int_with_annotation`: annotation authority,
//!   Int annotation passthrough, derived-name cascade, source-name fallback
//! - `resolve_var_sort_candidate`: non-Int preference, suffix stripping,
//!   view/current/final/prime peeling, old_ prefix cascade
//! - `resolve_decl_sort`: base_name projection, hint priority,
//!   reference-like sort peeling, fallback selection
//! - `resolve_logic_param_sort`: param_sorts precedence, hint fallback
//!
//! `resolve_var_sort` (the simple 3-tier fallback) is already covered in
//! `tests/resolve_var_sort.rs`. `DerivedKind` naming is covered in
//! `tests/derived_kind.rs`. This file fills the gap between those two:
//! the full annotation-aware cascade that the production encoder uses.

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::ExprSort;

use crate::encoder::AYEncoder;

// ── resolve_var_sort_or_int_with_annotation: annotation authority ──

#[test]
#[timeout(5000)]
fn annotation_non_int_overrides_cascade() {
    let mut enc = AYEncoder::new();
    // Hint says Bool, but annotation says Seq — annotation wins
    enc.sort_resolver_mut_for_test()
        .record_sort_hint("x".to_string(), ExprSort::Bool);
    let result = enc.resolve_var_sort_or_int_with_annotation("x", Some(&ExprSort::Seq));
    // Seq resolves to Sort::seq(Sort::Int) (#2080)
    assert_ne!(
        result,
        Sort::Bool,
        "Non-Int annotation should override hint cascade"
    );
    assert_ne!(
        result,
        Sort::Int,
        "Seq annotation should not fall back to Int"
    );
}

#[test]
#[timeout(5000)]
fn annotation_bool_overrides_cascade() {
    let mut enc = AYEncoder::new();
    // No hints, no declarations — Bool annotation is authoritative
    let result = enc.resolve_var_sort_or_int_with_annotation("x", Some(&ExprSort::Bool));
    assert_eq!(result, Sort::Bool);
}

#[test]
#[timeout(5000)]
fn annotation_int_falls_through_to_cascade() {
    let mut enc = AYEncoder::new();
    // Int annotation is weak — falls through to cascade
    enc.var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Bool);
    let result = enc.resolve_var_sort_or_int_with_annotation("x", Some(&ExprSort::Int));
    assert_eq!(
        result,
        Sort::Bool,
        "Int annotation should fall through; cascade finds Bool declaration"
    );
}

#[test]
#[timeout(5000)]
fn no_annotation_uses_cascade() {
    let mut enc = AYEncoder::new();
    enc.var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Bool);
    let result = enc.resolve_var_sort_or_int_with_annotation("x", None);
    assert_eq!(result, Sort::Bool, "No annotation should use cascade");
}

// ── resolve_var_sort_or_int_with_annotation: derived-name cascade ──

#[test]
#[timeout(5000)]
fn derived_view_inherits_base_sort() {
    let mut enc = AYEncoder::new();
    enc.var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Bool);
    // x_view should inherit Bool from base "x" via suffix stripping
    let result = enc.resolve_var_sort_or_int_with_annotation("x_view", None);
    assert_eq!(result, Sort::Bool, "x_view should resolve via base x");
}

#[test]
#[timeout(5000)]
fn derived_current_inherits_base_sort() {
    let mut enc = AYEncoder::new();
    enc.var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Bool);
    let result = enc.resolve_var_sort_or_int_with_annotation("x_current", None);
    assert_eq!(result, Sort::Bool, "x_current should resolve via base x");
}

#[test]
#[timeout(5000)]
fn derived_final_inherits_base_sort() {
    let mut enc = AYEncoder::new();
    enc.var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Bool);
    let result = enc.resolve_var_sort_or_int_with_annotation("x_final", None);
    assert_eq!(result, Sort::Bool, "x_final should resolve via base x");
}

#[test]
#[timeout(5000)]
fn derived_prime_inherits_base_sort() {
    let mut enc = AYEncoder::new();
    enc.var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Bool);
    let result = enc.resolve_var_sort_or_int_with_annotation("x_prime", None);
    assert_eq!(result, Sort::Bool, "x_prime should resolve via base x");
}

#[test]
#[timeout(5000)]
fn old_prefix_peels_to_base() {
    let mut enc = AYEncoder::new();
    enc.var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Bool);
    // old_x → peel old_ → resolve "x" → Bool
    let result = enc.resolve_var_sort_or_int_with_annotation("old_x", None);
    assert_eq!(result, Sort::Bool, "old_x should peel to base x");
}

#[test]
#[timeout(5000)]
fn double_old_peels_through() {
    let mut enc = AYEncoder::new();
    enc.var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Bool);
    // old_old_x → peel old_ → old_x → peel old_ → x → Bool
    let result = enc.resolve_var_sort_or_int_with_annotation("old_old_x", None);
    assert_eq!(result, Sort::Bool, "old_old_x should double-peel to x");
}

#[test]
#[timeout(5000)]
fn old_current_chain_resolves() {
    let mut enc = AYEncoder::new();
    enc.var_sorts_mut_for_test()
        .insert("x".to_string(), Sort::Bool);
    // old_x_current → suffix Current("old_x") → old_x stripped → x → Bool
    let result = enc.resolve_var_sort_or_int_with_annotation("old_x_current", None);
    assert_eq!(
        result,
        Sort::Bool,
        "old_x_current should resolve through suffix then prefix"
    );
}

// ── resolve_var_sort_or_int_with_annotation: hint-based resolution ──

#[test]
#[timeout(5000)]
fn hint_resolves_for_undeclared_var() {
    let mut enc = AYEncoder::new();
    enc.sort_resolver_mut_for_test()
        .record_sort_hint("p".to_string(), ExprSort::Bool);
    let result = enc.resolve_var_sort_or_int_with_annotation("p", None);
    assert_eq!(
        result,
        Sort::Bool,
        "Bool hint should resolve undeclared var"
    );
}

#[test]
#[timeout(5000)]
fn hint_resolves_for_derived_name() {
    let mut enc = AYEncoder::new();
    enc.sort_resolver_mut_for_test()
        .record_sort_hint("x".to_string(), ExprSort::Bool);
    // x_view with hint on "x" should resolve through suffix stripping + hint
    let result = enc.resolve_var_sort_or_int_with_annotation("x_view", None);
    assert_eq!(
        result,
        Sort::Bool,
        "Hint on base should resolve derived x_view"
    );
}

#[test]
#[timeout(5000)]
fn annotation_generic_mutref_preserves_carrier() {
    use trust_wp_core::formula::intern_sort_name;

    let mut enc = AYEncoder::new();
    let ann = ExprSort::MutRef(Box::new(ExprSort::TypeParam(intern_sort_name("T"))));
    let result = enc.resolve_var_sort_or_int_with_annotation("x", Some(&ann));
    assert_eq!(
        result,
        enc.sort_from_expr_sort(ann.clone()),
        "generic MutRef(TypeParam) annotations should preserve the mut-ref carrier sort"
    );
}

// ── resolve_var_sort_or_int_with_annotation: fallback to Int ──

#[test]
#[timeout(5000)]
fn source_name_no_info_falls_to_int() {
    let mut enc = AYEncoder::new();
    let result = enc.resolve_var_sort_or_int_with_annotation("unknown_var", None);
    assert_eq!(
        result,
        Sort::Int,
        "Source name with no info should fall back to Int"
    );
}

#[test]
#[timeout(5000)]
fn derived_name_no_base_info_falls_to_int() {
    let mut enc = AYEncoder::new();
    // x_view with no declaration or hint for "x" — should fall to Int
    let result = enc.resolve_var_sort_or_int_with_annotation("x_view", None);
    assert_eq!(
        result,
        Sort::Int,
        "Derived name with no base info should fall back to Int"
    );
}

// ── resolve_logic_param_sort ──
// Note: resolve_decl_sort is pub(in crate::encoder) and not testable
// from crate-root tests. Its correctness is exercised indirectly via
// the mut_borrow and function verification test suites.

#[test]
#[timeout(5000)]
fn logic_param_sort_falls_back_to_int_without_info() {
    let mut enc = AYEncoder::new();
    // Create a logic fn def with no param_sorts
    let def = trust_wp_core::logic::LogicFnDef::new(
        "test_fn".to_string(),
        "crate::test_fn".to_string(),
        vec!["x".to_string()],
        trust_wp_core::formula::PureExpr::Var("x".to_string(), None),
    );
    let result = enc.resolve_logic_param_sort(&def, 0);
    assert_eq!(
        result,
        Sort::Int,
        "Logic param with no sort info should fall back to Int"
    );
}

#[test]
#[timeout(5000)]
fn logic_param_sort_uses_hint_when_available() {
    let mut enc = AYEncoder::new();
    enc.sort_resolver_mut_for_test()
        .record_sort_hint("x".to_string(), ExprSort::Bool);
    let def = trust_wp_core::logic::LogicFnDef::new(
        "test_fn".to_string(),
        "crate::test_fn".to_string(),
        vec!["x".to_string()],
        trust_wp_core::formula::PureExpr::Var("x".to_string(), None),
    );
    let result = enc.resolve_logic_param_sort(&def, 0);
    assert_eq!(
        result,
        Sort::Bool,
        "Logic param with Bool hint should resolve to Bool"
    );
}
