// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{super::*, helpers::*};

#[test]
fn test_lookup_duration_add_via_trait_qualified_path() {
    let spec = lookup_std_spec("<core::time::Duration as core::ops::Add>::add")
        .expect("Duration Add spec via trait-qualified path should match");
    assert_requires_contains(
        &spec,
        "self@ + rhs@ <= u64::MAX@ * 1_000_000_000 + 999_999_999",
        "Duration::add",
    );
    assert_ensures_contains(&spec, "result@ == self@ + rhs@", "Duration::add");
}

#[test]
fn test_lookup_duration_sub_via_trait_qualified_path() {
    let spec = lookup_std_spec("<core::time::Duration as core::ops::Sub>::sub")
        .expect("Duration Sub spec via trait-qualified path should match");
    assert_requires_contains(&spec, "self@ >= rhs@", "Duration::sub");
    assert_ensures_contains(&spec, "result@ == self@ - rhs@", "Duration::sub");
}

#[test]
fn test_lookup_instant_add_via_trait_qualified_path() {
    let spec = lookup_std_spec("<std::time::Instant as core::ops::Add>::add")
        .expect("Instant Add spec via trait-qualified path should match");
    assert_requires_contains(&spec, "rhs@ == 0", "Instant::add");
    assert_ensures_contains(&spec, "result@ == self@ + rhs@", "Instant::add");
}

#[test]
fn test_lookup_instant_add_core_path() {
    let spec = lookup_std_spec("core::time::Instant::add").expect("Instant Add core path");
    assert_requires_contains(&spec, "rhs@ == 0", "Instant::add core");
    assert_ensures_contains(&spec, "result@ == self@ + rhs@", "Instant::add core");
}

#[test]
fn test_lookup_instant_sub_via_trait_qualified_path() {
    let spec = lookup_std_spec("<core::time::Instant as core::ops::Sub>::sub")
        .expect("Instant Sub spec via trait-qualified path should match");
    assert_requires_contains(
        &spec,
        "__trust_wp_std_site_same_Self_Rhs() || self@ >= rhs@",
        "Instant::sub",
    );
    assert_ensures_contains(
        &spec,
        "self@ >= rhs@ ==> result@ == self@ - rhs@",
        "Instant::sub",
    );
    assert_ensures_contains(&spec, "self@ < rhs@ ==> result@ == 0", "Instant::sub");
}

// Cross-prefix lookup: std::time::X as core::ops::Y paths (#997, #1034)
// These exercise the non-redundant cross-prefix table entries: the
// normalization replaces std::ops → core::ops but NOT std::time → core::time,
// so <std::time::Duration as core::ops::Add>::add requires a table entry.

#[test]
fn test_lookup_duration_add_cross_prefix_std_type_core_trait() {
    let spec = lookup_std_spec("<std::time::Duration as core::ops::Add>::add")
        .expect("cross-prefix Duration Add path should match after normalization");
    // Must match the same spec as the canonical path (#1034)
    assert_eq!(
        spec.requires,
        ["self@ + rhs@ <= u64::MAX@ * 1_000_000_000 + 999_999_999"],
        "Duration Add owes its overflow panic"
    );
    assert_eq!(
        spec.ensures.len(),
        1,
        "Duration Add has exactly one postcondition"
    );
    assert!(
        spec.ensures[0].contains("self@ + rhs@"),
        "Duration Add ensures should reference self@ + rhs@, got: {}",
        spec.ensures[0]
    );
}

#[test]
fn test_lookup_instant_add_cross_prefix_core_type_std_trait() {
    // <core::time::Instant as std::ops::Add>::add normalizes to
    // <core::time::Instant as core::ops::Add>::add (std::ops → core::ops).
    let spec = lookup_std_spec("<core::time::Instant as std::ops::Add>::add")
        .expect("cross-prefix Instant Add path should match after normalization");
    // Must match the same spec as the canonical path (#1034)
    assert_eq!(
        spec.requires,
        ["rhs@ == 0"],
        "Instant Add owes the zero duration `checked_add` promises `Some` for"
    );
    assert_eq!(spec.ensures.len(), 1, "Instant Add has one postcondition");
    assert!(
        spec.ensures.iter().any(|e| e.contains("self@ + rhs@")),
        "Instant Add ensures should reference self@ + rhs@, got: {:?}",
        spec.ensures
    );
}

// Generic trait paths must NOT match type-specific specs (#980)
#[test]
fn test_lookup_duration_partial_cmp() {
    let spec = lookup_std_spec("<core::time::Duration as core::cmp::PartialOrd>::partial_cmp")
        .expect("Duration::partial_cmp spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "match result", "Duration::partial_cmp");
}

#[test]
fn test_lookup_duration_partial_cmp_std_prefix() {
    let spec = lookup_std_spec("std::time::Duration::partial_cmp")
        .expect("Duration::partial_cmp via std prefix should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Ordering::Less", "Duration::partial_cmp std");
}

// ── Raw pointer spec lookups (#1126) ───────────────────────────
