// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for free helper functions in `encoder::sort_context::mod`.
//!
//! Coverage targets (all zero test references prior to this file):
//! - `is_collection_expr_sort`: classifies ExprSort as collection (Seq/FMap/Mapping)
//! - `extract_inner_var_annotation`: digs through Deref/Final/Old/View to find Var annotation
//! - `apply_name_prefix`: formats variable name with optional DerivedKind prefix
//! - `mapping_expr_sort`: constructs the ExprSort for the Mapping pseudo-datatype

use std::borrow::Cow;

use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, resolve_sort_name, ExprSort};

use crate::{
    encoder::sort_context::{
        apply_name_prefix, extract_inner_var_annotation, is_collection_expr_sort,
        mapping_expr_sort, reference_like_inner_sort, DerivedKind,
    },
    tests::helpers::{deref, final_expr, int, old, var, var_with_sort, view},
};

// ── mapping_expr_sort ──────────────────────────────────────────────

#[test]
#[timeout(5000)]
fn mapping_expr_sort_is_datatype() {
    let sort = mapping_expr_sort();
    match &sort {
        ExprSort::Datatype(id) => {
            assert_eq!(resolve_sort_name(*id), "Mapping");
        }
        other => panic!("expected ExprSort::Datatype, got {other:?}"),
    }
}

#[test]
#[timeout(5000)]
fn mapping_expr_sort_stable_across_calls() {
    let a = mapping_expr_sort();
    let b = mapping_expr_sort();
    assert_eq!(
        a, b,
        "mapping_expr_sort must return the same value on repeated calls"
    );
}

#[test]
#[timeout(5000)]
fn mapping_expr_sort_matches_manual_intern() {
    let manual = ExprSort::Datatype(intern_sort_name("Mapping"));
    assert_eq!(mapping_expr_sort(), manual);
}

// ── reference_like_inner_sort (#2141) ─────────────────────────────

#[test]
#[timeout(5000)]
fn reference_like_ref_returns_inner() {
    let sort = ExprSort::Ref(Box::new(ExprSort::Seq));
    assert_eq!(reference_like_inner_sort(&sort), Some(&ExprSort::Seq));
}

#[test]
#[timeout(5000)]
fn reference_like_mutref_returns_inner() {
    let sort = ExprSort::MutRef(Box::new(ExprSort::Int));
    assert_eq!(reference_like_inner_sort(&sort), Some(&ExprSort::Int));
}

#[test]
#[timeout(5000)]
fn reference_like_non_ref_returns_none() {
    assert_eq!(reference_like_inner_sort(&ExprSort::Bool), None);
    assert_eq!(reference_like_inner_sort(&ExprSort::Int), None);
    assert_eq!(reference_like_inner_sort(&ExprSort::Seq), None);
    assert_eq!(reference_like_inner_sort(&ExprSort::FMap), None);
    assert_eq!(reference_like_inner_sort(&ExprSort::Tuple(2)), None);
}

// ── is_collection_expr_sort ────────────────────────────────────────

#[test]
#[timeout(5000)]
fn collection_sort_seq() {
    assert!(is_collection_expr_sort(&ExprSort::Seq));
}

#[test]
#[timeout(5000)]
fn collection_sort_fmap() {
    assert!(is_collection_expr_sort(&ExprSort::FMap));
}

#[test]
#[timeout(5000)]
fn collection_sort_mapping() {
    assert!(is_collection_expr_sort(&mapping_expr_sort()));
}

#[test]
#[timeout(5000)]
fn non_collection_bool() {
    assert!(!is_collection_expr_sort(&ExprSort::Bool));
}

#[test]
#[timeout(5000)]
fn non_collection_int() {
    assert!(!is_collection_expr_sort(&ExprSort::Int));
}

#[test]
#[timeout(5000)]
fn non_collection_unit() {
    assert!(!is_collection_expr_sort(&ExprSort::Unit));
}

#[test]
#[timeout(5000)]
fn non_collection_tuple() {
    assert!(!is_collection_expr_sort(&ExprSort::Tuple(2)));
}

#[test]
#[timeout(5000)]
fn non_collection_float() {
    assert!(!is_collection_expr_sort(&ExprSort::Float(
        trust_wp_core::formula::FloatWidth::F64
    )));
}

#[test]
#[timeout(5000)]
fn non_collection_type_param() {
    assert!(!is_collection_expr_sort(&ExprSort::TypeParam(0)));
}

#[test]
#[timeout(5000)]
fn non_collection_ref() {
    assert!(!is_collection_expr_sort(&ExprSort::Ref(Box::new(
        ExprSort::Int
    ))));
}

// MutRef collection sort coverage (#2141)

#[test]
#[timeout(5000)]
fn collection_sort_ref_seq() {
    assert!(is_collection_expr_sort(&ExprSort::Ref(Box::new(
        ExprSort::Seq
    ))));
}

#[test]
#[timeout(5000)]
fn collection_sort_mutref_seq() {
    assert!(is_collection_expr_sort(&ExprSort::MutRef(Box::new(
        ExprSort::Seq
    ))));
}

#[test]
#[timeout(5000)]
fn collection_sort_ref_fmap() {
    assert!(is_collection_expr_sort(&ExprSort::Ref(Box::new(
        ExprSort::FMap
    ))));
}

#[test]
#[timeout(5000)]
fn collection_sort_mutref_fmap() {
    assert!(is_collection_expr_sort(&ExprSort::MutRef(Box::new(
        ExprSort::FMap
    ))));
}

#[test]
#[timeout(5000)]
fn non_collection_mutref_int() {
    assert!(!is_collection_expr_sort(&ExprSort::MutRef(Box::new(
        ExprSort::Int
    ))));
}

#[test]
#[timeout(5000)]
fn non_collection_datatype_not_mapping() {
    let sort = ExprSort::Datatype(intern_sort_name("OptionInt"));
    assert!(!is_collection_expr_sort(&sort));
}

// ── extract_inner_var_annotation ───────────────────────────────────

#[test]
#[timeout(5000)]
fn annotation_from_bare_var() {
    let expr = var_with_sort("x", ExprSort::Seq);
    assert_eq!(extract_inner_var_annotation(&expr), Some(&ExprSort::Seq));
}

#[test]
#[timeout(5000)]
fn annotation_from_var_no_sort() {
    let expr = var("x");
    assert_eq!(extract_inner_var_annotation(&expr), None);
}

#[test]
#[timeout(5000)]
fn annotation_through_deref() {
    let expr = deref(var_with_sort("x", ExprSort::FMap));
    assert_eq!(extract_inner_var_annotation(&expr), Some(&ExprSort::FMap));
}

#[test]
#[timeout(5000)]
fn annotation_through_final() {
    let expr = final_expr(var_with_sort("x", ExprSort::Bool));
    assert_eq!(extract_inner_var_annotation(&expr), Some(&ExprSort::Bool));
}

#[test]
#[timeout(5000)]
fn annotation_through_old() {
    let sort = ExprSort::Datatype(intern_sort_name("MyType"));
    let expr = old(var_with_sort("x", sort.clone()));
    assert_eq!(extract_inner_var_annotation(&expr), Some(&sort));
}

#[test]
#[timeout(5000)]
fn annotation_through_view() {
    let expr = view(var_with_sort("v", ExprSort::Seq));
    assert_eq!(extract_inner_var_annotation(&expr), Some(&ExprSort::Seq));
}

#[test]
#[timeout(5000)]
fn annotation_through_nested_chain() {
    // Old(Deref(Var("x", Some(Int)))) — two wrappers deep
    let expr = old(deref(var_with_sort("x", ExprSort::Int)));
    assert_eq!(extract_inner_var_annotation(&expr), Some(&ExprSort::Int));
}

#[test]
#[timeout(5000)]
fn annotation_through_deep_chain() {
    // View(Final(Deref(Var("m", Some(FMap))))) — three wrappers deep
    let expr = view(final_expr(deref(var_with_sort("m", ExprSort::FMap))));
    assert_eq!(extract_inner_var_annotation(&expr), Some(&ExprSort::FMap));
}

#[test]
#[timeout(5000)]
fn annotation_none_for_non_var_leaf() {
    // Deref(Int(42)) — no Var at bottom
    let expr = deref(int(42));
    assert_eq!(extract_inner_var_annotation(&expr), None);
}

#[test]
#[timeout(5000)]
fn annotation_none_for_plain_int() {
    assert_eq!(extract_inner_var_annotation(&int(0)), None);
}

#[test]
#[timeout(5000)]
fn annotation_none_for_unannotated_var_through_chain() {
    let expr = deref(final_expr(var("x")));
    assert_eq!(extract_inner_var_annotation(&expr), None);
}

// ── apply_name_prefix ──────────────────────────────────────────────

#[test]
#[timeout(5000)]
fn prefix_none_returns_borrowed() {
    let result = apply_name_prefix("x", None);
    assert_eq!(result.as_ref(), "x");
    assert!(
        matches!(result, Cow::Borrowed(_)),
        "None prefix should return Cow::Borrowed"
    );
}

#[test]
#[timeout(5000)]
fn prefix_old() {
    let result = apply_name_prefix("x", Some(DerivedKind::Old));
    assert_eq!(result.as_ref(), "old_x");
    assert!(matches!(result, Cow::Owned(_)));
}

#[test]
#[timeout(5000)]
fn prefix_current() {
    let result = apply_name_prefix("x", Some(DerivedKind::Current));
    assert_eq!(result.as_ref(), "x_current");
}

#[test]
#[timeout(5000)]
fn prefix_final() {
    let result = apply_name_prefix("x", Some(DerivedKind::Final));
    assert_eq!(result.as_ref(), "x_final");
}

#[test]
#[timeout(5000)]
fn prefix_view() {
    let result = apply_name_prefix("v", Some(DerivedKind::View));
    assert_eq!(result.as_ref(), "v_view");
}

#[test]
#[timeout(5000)]
fn prefix_prime() {
    let result = apply_name_prefix("y", Some(DerivedKind::Prime));
    assert_eq!(result.as_ref(), "y_prime");
}

#[test]
#[timeout(5000)]
fn prefix_final_prefix() {
    let result = apply_name_prefix("m", Some(DerivedKind::FinalPrefix));
    assert_eq!(result.as_ref(), "final_m");
}

#[test]
#[timeout(5000)]
fn prefix_preserves_complex_base_name() {
    let result = apply_name_prefix("self.0", Some(DerivedKind::Current));
    assert_eq!(result.as_ref(), "self.0_current");
}

#[test]
#[timeout(5000)]
fn prefix_none_empty_name() {
    let result = apply_name_prefix("", None);
    assert_eq!(result.as_ref(), "");
}

#[test]
#[timeout(5000)]
fn prefix_on_already_derived_name() {
    // Applying Old prefix to "x_current" gives "old_x_current"
    let result = apply_name_prefix("x_current", Some(DerivedKind::Old));
    assert_eq!(result.as_ref(), "old_x_current");
}
