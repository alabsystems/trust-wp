// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::encoder::state::adt::AdtState`].
//!
//! Coverage gap: `set_field_ranges`, `field_ranges_for`, `decl_for_name`,
//! and `insert_decl_if_absent` had zero direct tests despite being
//! `pub(crate)`. The `decl_for_name` method has non-trivial fallback
//! logic (`rsplit("::").next()` bare-name lookup).

use ntest::timeout;
use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldRanges, AdtKind, FieldRangeKind};

use crate::encoder::AdtState;

fn make_simple_decl(name: &str) -> AdtDecl {
    AdtDecl::new(
        format!("crate::module::{name}"),
        name.to_string(),
        AdtKind::Enum,
        vec![AdtConstructorDecl::new(
            "Variant1".to_string(),
            "Variant1".to_string(),
            vec![],
        )],
    )
}

// --- new / field_ranges_for ---

#[test]
#[timeout(30000)]
fn new_adt_state_has_no_field_ranges() {
    let state = AdtState::new();
    assert!(state.field_ranges_for("Foo").is_none());
}

// --- set_field_ranges / field_ranges_for ---

#[test]
#[timeout(30000)]
fn set_and_retrieve_field_ranges() {
    let mut state = AdtState::new();
    let mut ranges = AdtFieldRanges::new();
    ranges.insert(
        "MyEnum".to_string(),
        vec![(
            "Variant1".to_string(),
            vec![(0, FieldRangeKind::Unsigned(8))],
        )],
    );
    state.set_field_ranges(ranges);

    let result = state
        .field_ranges_for("MyEnum")
        .expect("field ranges should exist");
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].0, "Variant1");
    assert_eq!(result[0].1.len(), 1);
    assert!(matches!(result[0].1[0].1, FieldRangeKind::Unsigned(8)));
}

#[test]
#[timeout(30000)]
fn field_ranges_for_missing_type_returns_none() {
    let mut state = AdtState::new();
    let mut ranges = AdtFieldRanges::new();
    ranges.insert("Present".to_string(), vec![]);
    state.set_field_ranges(ranges);

    assert!(state.field_ranges_for("Absent").is_none());
}

#[test]
#[timeout(30000)]
fn set_field_ranges_replaces_previous() {
    let mut state = AdtState::new();

    let mut ranges1 = AdtFieldRanges::new();
    ranges1.insert("T".to_string(), vec![("A".to_string(), vec![])]);
    state.set_field_ranges(ranges1);

    let mut ranges2 = AdtFieldRanges::new();
    ranges2.insert(
        "T".to_string(),
        vec![("A".to_string(), vec![]), ("B".to_string(), vec![])],
    );
    state.set_field_ranges(ranges2);

    let result = state.field_ranges_for("T").unwrap();
    assert_eq!(
        result.len(),
        2,
        "second set_field_ranges should replace first"
    );
}

// --- insert_decl_if_absent / decl_for_name ---

#[test]
#[timeout(30000)]
fn insert_and_retrieve_decl_by_exact_name() {
    let mut state = AdtState::new();
    state.insert_decl_if_absent("MyType".to_string(), make_simple_decl("MyType"));

    let decl = state.decl_for_name("MyType").expect("decl should exist");
    assert_eq!(decl.adt_name, "MyType");
}

#[test]
#[timeout(30000)]
fn decl_for_name_returns_none_when_absent() {
    let state = AdtState::new();
    assert!(state.decl_for_name("Missing").is_none());
}

#[test]
#[timeout(30000)]
fn insert_decl_if_absent_does_not_overwrite() {
    let mut state = AdtState::new();
    let decl1 = AdtDecl::new(
        "path::A".to_string(),
        "first".to_string(),
        AdtKind::Struct,
        vec![],
    );
    let decl2 = AdtDecl::new(
        "path::A".to_string(),
        "second".to_string(),
        AdtKind::Struct,
        vec![],
    );
    state.insert_decl_if_absent("A".to_string(), decl1);
    state.insert_decl_if_absent("A".to_string(), decl2);

    let decl = state.decl_for_name("A").unwrap();
    assert_eq!(decl.adt_name, "first", "or_insert should keep first entry");
}

/// A later declaration under a kept name can only add the mark that a value
/// may hold a `&mut`, never remove it (D-126).
#[test]
#[timeout(30000)]
fn insert_decl_if_absent_keeps_the_borrow_mark_of_either() {
    let mut state = AdtState::new();
    state.insert_decl_if_absent("A".to_string(), make_simple_decl("A"));
    state.insert_decl_if_absent(
        "A".to_string(),
        make_simple_decl("A").with_may_hold_a_borrow(true),
    );
    state.insert_decl_if_absent("A".to_string(), make_simple_decl("A"));
    assert!(state.decl_for_name("A").unwrap().may_hold_a_borrow);
}

// --- decl_for_name bare-name fallback ---

#[test]
#[timeout(30000)]
fn decl_for_name_falls_back_to_bare_name() {
    let mut state = AdtState::new();
    // Insert with bare name "Option"
    state.insert_decl_if_absent("Option".to_string(), make_simple_decl("Option"));

    // Query with qualified path — should fall back to bare name
    let decl = state
        .decl_for_name("std::option::Option")
        .expect("should find via bare name fallback");
    assert_eq!(decl.adt_name, "Option");
}

#[test]
#[timeout(30000)]
fn decl_for_name_prefers_exact_match_over_bare() {
    let mut state = AdtState::new();
    // Insert both bare and qualified
    let bare_decl = AdtDecl::new(
        "bare".to_string(),
        "bare_version".to_string(),
        AdtKind::Enum,
        vec![],
    );
    let qualified_decl = AdtDecl::new(
        "qualified".to_string(),
        "qualified_version".to_string(),
        AdtKind::Enum,
        vec![],
    );
    state.insert_decl_if_absent("Result".to_string(), bare_decl);
    state.insert_decl_if_absent("std::result::Result".to_string(), qualified_decl);

    // Exact match should take precedence
    let decl = state
        .decl_for_name("std::result::Result")
        .expect("should find exact match");
    assert_eq!(decl.adt_name, "qualified_version");
}

#[test]
#[timeout(30000)]
fn decl_for_name_bare_fallback_with_deeply_nested_path() {
    let mut state = AdtState::new();
    state.insert_decl_if_absent("Color".to_string(), make_simple_decl("Color"));

    // Deep nesting: a::b::c::d::Color → bare = "Color"
    let decl = state
        .decl_for_name("a::b::c::d::Color")
        .expect("deeply nested path should fall back to bare");
    assert_eq!(decl.adt_name, "Color");
}

#[test]
#[timeout(30000)]
fn decl_for_name_no_colons_returns_exact_match() {
    let mut state = AdtState::new();
    state.insert_decl_if_absent("Foo".to_string(), make_simple_decl("Foo"));

    // No "::" in name — rsplit("::") returns the whole string, which equals
    // the original, so exact match is tried (and found) immediately.
    let decl = state.decl_for_name("Foo").expect("bare name should match");
    assert_eq!(decl.adt_name, "Foo");
}

// --- signed field range ---

#[test]
#[timeout(30000)]
fn field_ranges_signed_variant() {
    let mut state = AdtState::new();
    let mut ranges = AdtFieldRanges::new();
    ranges.insert(
        "SignedStruct".to_string(),
        vec![("new".to_string(), vec![(0, FieldRangeKind::Signed(16))])],
    );
    state.set_field_ranges(ranges);

    let result = state.field_ranges_for("SignedStruct").unwrap();
    assert!(matches!(result[0].1[0].1, FieldRangeKind::Signed(16)));
}
