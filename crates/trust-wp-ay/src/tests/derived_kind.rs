// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `DerivedKind` and `classify_var_name` in
//! `encoder::sort_context::resolution`.
//!
//! Coverage targets (all zero direct test references prior to this file):
//! - `classify_var_name`: classifies variable names as source or derived
//! - `is_derived_var_name`: convenience wrapper over classify
//! - `DerivedKind::format_name`: constructs derived names from base
//! - `DerivedKind::format_chain`: constructs nested derived names
//! - `DerivedKind::strip_from`: extracts derivation kind and base from name
//! - `DerivedKind::strip_old_prefix`: strips `old_` prefix
//! - `DerivedKind::peel_final_view_prefix`: strips `final_` from `_view` chain
//! - `DerivedKind::peel_old_prefixes`: iterator over repeated `old_` peeling
//!
//! These functions are the foundation of the variable-name resolution
//! pipeline (#2020 Slice 3). Suffix checks take priority over prefix
//! checks, which is a subtle invariant tested thoroughly below.

use ntest::timeout;

use crate::encoder::sort_context::{classify_var_name, is_derived_var_name, DerivedKind};

// ── DerivedKind::format_name ─────────────────────────────────────

#[test]
#[timeout(5000)]
fn format_name_view() {
    assert_eq!(DerivedKind::View.format_name("x"), "x_view");
}

#[test]
#[timeout(5000)]
fn format_name_current() {
    assert_eq!(DerivedKind::Current.format_name("x"), "x_current");
}

#[test]
#[timeout(5000)]
fn format_name_final() {
    assert_eq!(DerivedKind::Final.format_name("x"), "x_final");
}

#[test]
#[timeout(5000)]
fn format_name_prime() {
    assert_eq!(DerivedKind::Prime.format_name("x"), "x_prime");
}

#[test]
#[timeout(5000)]
fn format_name_old() {
    assert_eq!(DerivedKind::Old.format_name("x"), "old_x");
}

#[test]
#[timeout(5000)]
fn format_name_final_prefix() {
    assert_eq!(DerivedKind::FinalPrefix.format_name("x"), "final_x");
}

#[test]
#[timeout(5000)]
fn format_name_preserves_complex_base() {
    assert_eq!(DerivedKind::View.format_name("self.0"), "self.0_view");
    assert_eq!(DerivedKind::Old.format_name("a_b"), "old_a_b");
}

// ── DerivedKind::format_chain ────────────────────────────────────

#[test]
#[timeout(5000)]
fn format_chain_empty_is_identity() {
    assert_eq!(DerivedKind::format_chain("x", &[]), "x");
}

#[test]
#[timeout(5000)]
fn format_chain_single_is_format_name() {
    assert_eq!(
        DerivedKind::format_chain("x", &[DerivedKind::View]),
        DerivedKind::View.format_name("x"),
    );
}

#[test]
#[timeout(5000)]
fn format_chain_current_then_final() {
    // Inner-to-outer: x → x_current → x_current_final
    assert_eq!(
        DerivedKind::format_chain("x", &[DerivedKind::Current, DerivedKind::Final]),
        "x_current_final",
    );
}

#[test]
#[timeout(5000)]
fn format_chain_final_prefix_then_view() {
    // Inner-to-outer: x → final_x → final_x_view
    assert_eq!(
        DerivedKind::format_chain("x", &[DerivedKind::FinalPrefix, DerivedKind::View]),
        "final_x_view",
    );
}

#[test]
#[timeout(5000)]
fn format_chain_old_then_current() {
    assert_eq!(
        DerivedKind::format_chain("v", &[DerivedKind::Old, DerivedKind::Current]),
        "old_v_current",
    );
}

// ── DerivedKind::strip_from ──────────────────────────────────────

#[test]
#[timeout(5000)]
fn strip_from_view_suffix() {
    let (kind, base) = DerivedKind::strip_from("x_view").unwrap();
    assert_eq!(kind, DerivedKind::View);
    assert_eq!(base, "x");
}

#[test]
#[timeout(5000)]
fn strip_from_current_suffix() {
    let (kind, base) = DerivedKind::strip_from("x_current").unwrap();
    assert_eq!(kind, DerivedKind::Current);
    assert_eq!(base, "x");
}

#[test]
#[timeout(5000)]
fn strip_from_final_suffix() {
    let (kind, base) = DerivedKind::strip_from("x_final").unwrap();
    assert_eq!(kind, DerivedKind::Final);
    assert_eq!(base, "x");
}

#[test]
#[timeout(5000)]
fn strip_from_prime_suffix() {
    let (kind, base) = DerivedKind::strip_from("y_prime").unwrap();
    assert_eq!(kind, DerivedKind::Prime);
    assert_eq!(base, "y");
}

#[test]
#[timeout(5000)]
fn strip_from_old_prefix() {
    let (kind, base) = DerivedKind::strip_from("old_x").unwrap();
    assert_eq!(kind, DerivedKind::Old);
    assert_eq!(base, "x");
}

#[test]
#[timeout(5000)]
fn strip_from_final_prefix() {
    let (kind, base) = DerivedKind::strip_from("final_x").unwrap();
    assert_eq!(kind, DerivedKind::FinalPrefix);
    assert_eq!(base, "x");
}

#[test]
#[timeout(5000)]
fn strip_from_source_name_returns_none() {
    assert!(DerivedKind::strip_from("counter").is_none());
    assert!(DerivedKind::strip_from("x").is_none());
    assert!(DerivedKind::strip_from("").is_none());
}

/// Critical invariant: suffixes take priority over prefixes.
/// `old_x_current` should classify as Current (suffix), not Old (prefix).
#[test]
#[timeout(5000)]
fn strip_from_suffix_priority_over_prefix() {
    let (kind, base) = DerivedKind::strip_from("old_x_current").unwrap();
    assert_eq!(
        kind,
        DerivedKind::Current,
        "suffix _current should win over old_ prefix"
    );
    assert_eq!(base, "old_x");
}

/// `final_x_view` — suffix _view wins over final_ prefix.
#[test]
#[timeout(5000)]
fn strip_from_view_wins_over_final_prefix() {
    let (kind, base) = DerivedKind::strip_from("final_x_view").unwrap();
    assert_eq!(kind, DerivedKind::View);
    assert_eq!(base, "final_x");
}

/// `old_x_view` — suffix _view wins over old_ prefix.
#[test]
#[timeout(5000)]
fn strip_from_view_wins_over_old_prefix() {
    let (kind, base) = DerivedKind::strip_from("old_x_view").unwrap();
    assert_eq!(kind, DerivedKind::View);
    assert_eq!(base, "old_x");
}

// ── classify_var_name ────────────────────────────────────────────

#[test]
#[timeout(5000)]
fn classify_source_name() {
    assert_eq!(classify_var_name("x"), None);
    assert_eq!(classify_var_name("counter"), None);
    assert_eq!(classify_var_name("self_"), None);
}

#[test]
#[timeout(5000)]
fn classify_view_suffix() {
    assert_eq!(classify_var_name("x_view"), Some(DerivedKind::View));
}

#[test]
#[timeout(5000)]
fn classify_current_suffix() {
    assert_eq!(classify_var_name("x_current"), Some(DerivedKind::Current));
}

#[test]
#[timeout(5000)]
fn classify_final_suffix() {
    assert_eq!(classify_var_name("x_final"), Some(DerivedKind::Final));
}

#[test]
#[timeout(5000)]
fn classify_prime_suffix() {
    assert_eq!(classify_var_name("y_prime"), Some(DerivedKind::Prime));
}

#[test]
#[timeout(5000)]
fn classify_old_prefix() {
    assert_eq!(classify_var_name("old_x"), Some(DerivedKind::Old));
}

/// `final_x` (FinalPrefix) is explicitly excluded from classify_var_name.
/// FinalPrefix is an intermediate form, not a top-level classification.
#[test]
#[timeout(5000)]
fn classify_final_prefix_returns_none() {
    assert_eq!(
        classify_var_name("final_x"),
        None,
        "FinalPrefix should not be returned by classify_var_name"
    );
}

#[test]
#[timeout(5000)]
fn classify_empty_name() {
    assert_eq!(classify_var_name(""), None);
}

/// Compound name: old_ + _current → Current wins (suffix priority).
#[test]
#[timeout(5000)]
fn classify_compound_suffix_wins() {
    assert_eq!(
        classify_var_name("old_x_current"),
        Some(DerivedKind::Current),
    );
}

// ── is_derived_var_name ──────────────────────────────────────────

#[test]
#[timeout(5000)]
fn is_derived_true_for_suffixed() {
    assert!(is_derived_var_name("x_view"));
    assert!(is_derived_var_name("x_current"));
    assert!(is_derived_var_name("x_final"));
    assert!(is_derived_var_name("x_prime"));
}

#[test]
#[timeout(5000)]
fn is_derived_true_for_old_prefix() {
    assert!(is_derived_var_name("old_x"));
}

#[test]
#[timeout(5000)]
fn is_derived_false_for_source() {
    assert!(!is_derived_var_name("x"));
    assert!(!is_derived_var_name("counter"));
    assert!(!is_derived_var_name(""));
}

/// `final_x` is FinalPrefix, which classify_var_name excludes → not derived.
#[test]
#[timeout(5000)]
fn is_derived_false_for_final_prefix() {
    assert!(!is_derived_var_name("final_x"));
}

// ── DerivedKind::strip_old_prefix ────────────────────────────────

#[test]
#[timeout(5000)]
fn strip_old_prefix_present() {
    assert_eq!(DerivedKind::strip_old_prefix("old_x"), Some("x"));
}

#[test]
#[timeout(5000)]
fn strip_old_prefix_absent() {
    assert_eq!(DerivedKind::strip_old_prefix("x"), None);
    assert_eq!(DerivedKind::strip_old_prefix("x_current"), None);
}

#[test]
#[timeout(5000)]
fn strip_old_prefix_nested() {
    assert_eq!(DerivedKind::strip_old_prefix("old_old_x"), Some("old_x"));
}

#[test]
#[timeout(5000)]
fn strip_old_prefix_compound() {
    // Strips only the leading old_, preserving the suffix.
    assert_eq!(
        DerivedKind::strip_old_prefix("old_x_current"),
        Some("x_current")
    );
}

// ── DerivedKind::peel_final_view_prefix ──────────────────────────

#[test]
#[timeout(5000)]
fn peel_final_view_simple() {
    assert_eq!(
        DerivedKind::peel_final_view_prefix("final_v_view"),
        Some("v_view".to_string()),
    );
}

#[test]
#[timeout(5000)]
fn peel_final_view_nested_current() {
    assert_eq!(
        DerivedKind::peel_final_view_prefix("final_v_current_view"),
        Some("v_current_view".to_string()),
    );
}

#[test]
#[timeout(5000)]
fn peel_final_view_with_old() {
    assert_eq!(
        DerivedKind::peel_final_view_prefix("final_old_v_view"),
        Some("old_v_view".to_string()),
    );
}

#[test]
#[timeout(5000)]
fn peel_final_view_not_a_view_returns_none() {
    assert_eq!(DerivedKind::peel_final_view_prefix("final_x"), None);
    assert_eq!(DerivedKind::peel_final_view_prefix("final_x_current"), None);
}

#[test]
#[timeout(5000)]
fn peel_final_view_no_final_prefix_returns_none() {
    assert_eq!(DerivedKind::peel_final_view_prefix("x_view"), None);
    assert_eq!(DerivedKind::peel_final_view_prefix("old_x_view"), None);
}

#[test]
#[timeout(5000)]
fn peel_final_view_source_name_returns_none() {
    assert_eq!(DerivedKind::peel_final_view_prefix("counter"), None);
}

// ── DerivedKind::peel_old_prefixes ───────────────────────────────

#[test]
#[timeout(5000)]
fn peel_old_prefixes_none_for_source() {
    let names: Vec<&str> = DerivedKind::peel_old_prefixes("x").collect();
    assert!(names.is_empty());
}

#[test]
#[timeout(5000)]
fn peel_old_prefixes_single() {
    let names: Vec<&str> = DerivedKind::peel_old_prefixes("old_x").collect();
    assert_eq!(names, vec!["x"]);
}

#[test]
#[timeout(5000)]
fn peel_old_prefixes_double() {
    let names: Vec<&str> = DerivedKind::peel_old_prefixes("old_old_x").collect();
    assert_eq!(names, vec!["old_x", "x"]);
}

#[test]
#[timeout(5000)]
fn peel_old_prefixes_triple() {
    let names: Vec<&str> = DerivedKind::peel_old_prefixes("old_old_old_v_current").collect();
    assert_eq!(
        names,
        vec!["old_old_v_current", "old_v_current", "v_current"]
    );
}

#[test]
#[timeout(5000)]
fn peel_old_prefixes_stops_at_non_old() {
    // "x_current" has no old_ prefix → empty iterator
    let names: Vec<&str> = DerivedKind::peel_old_prefixes("x_current").collect();
    assert!(names.is_empty());
}

// ── Round-trip: format_name → strip_from ─────────────────────────

#[test]
#[timeout(5000)]
fn format_strip_roundtrip_all_kinds() {
    let kinds = [
        DerivedKind::View,
        DerivedKind::Current,
        DerivedKind::Final,
        DerivedKind::Prime,
        DerivedKind::Old,
        DerivedKind::FinalPrefix,
    ];
    for kind in kinds {
        let formatted = kind.format_name("test_var");
        let (stripped_kind, stripped_base) = DerivedKind::strip_from(&formatted)
            .unwrap_or_else(|| panic!("strip_from should parse {formatted:?}"));
        assert_eq!(stripped_kind, kind, "round-trip kind mismatch for {kind:?}");
        assert_eq!(
            stripped_base, "test_var",
            "round-trip base mismatch for {kind:?}"
        );
    }
}
