// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for ghost erasure check helpers.
//!
//! These test the pure logic of span containment and local classification.
//! Full MIR integration tests require rustc and live in the integration
//! test files (`tests/ghost_write_validation.rs`, etc.).

use rustc_span::{BytePos, Span, DUMMY_SP};

use super::is_in_ghost_region;

#[test]
fn test_is_in_ghost_region_empty_spans() {
    let stmt_span = DUMMY_SP;
    assert!(!is_in_ghost_region(stmt_span, &[]));
}

#[test]
fn test_is_in_ghost_region_contained() {
    // Ghost region spans bytes 10..50, statement spans bytes 20..30
    let ghost_span = Span::new(
        BytePos(10),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_span = Span::new(
        BytePos(20),
        BytePos(30),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(is_in_ghost_region(stmt_span, &[ghost_span]));
}

#[test]
fn test_is_in_ghost_region_not_contained() {
    let ghost_span = Span::new(
        BytePos(10),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_span = Span::new(
        BytePos(60),
        BytePos(70),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(!is_in_ghost_region(stmt_span, &[ghost_span]));
}

#[test]
fn test_is_in_ghost_region_multiple_spans() {
    let ghost1 = Span::new(
        BytePos(10),
        BytePos(20),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let ghost2 = Span::new(
        BytePos(50),
        BytePos(80),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_in_second = Span::new(
        BytePos(55),
        BytePos(65),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_outside = Span::new(
        BytePos(30),
        BytePos(40),
        rustc_span::SyntaxContext::root(),
        None,
    );

    assert!(is_in_ghost_region(stmt_in_second, &[ghost1, ghost2]));
    assert!(!is_in_ghost_region(stmt_outside, &[ghost1, ghost2]));
}

#[test]
fn test_is_in_ghost_region_exact_boundary() {
    // Statement exactly at the ghost region boundary
    let ghost_span = Span::new(
        BytePos(10),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_span = Span::new(
        BytePos(10),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(is_in_ghost_region(stmt_span, &[ghost_span]));
}

// ── Boundary and edge-case tests ──────────────────────────────────────

/// Statement that starts inside the ghost region but extends past it.
/// `Span::contains` requires the inner span to be fully within the outer,
/// so this should return false.
#[test]
fn test_is_in_ghost_region_partial_overlap_extending_past() {
    let ghost_span = Span::new(
        BytePos(10),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_span = Span::new(
        BytePos(40),
        BytePos(60),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(
        !is_in_ghost_region(stmt_span, &[ghost_span]),
        "statement extending past ghost region should NOT be considered inside"
    );
}

/// Statement that starts before the ghost region but ends inside it.
/// Should return false — partial overlap is not containment.
#[test]
fn test_is_in_ghost_region_partial_overlap_starting_before() {
    let ghost_span = Span::new(
        BytePos(10),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_span = Span::new(
        BytePos(5),
        BytePos(20),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(
        !is_in_ghost_region(stmt_span, &[ghost_span]),
        "statement starting before ghost region should NOT be considered inside"
    );
}

/// Statement starting exactly at ghost region's end byte.
/// Span [50, 60) when ghost is [10, 50) — should NOT be contained.
#[test]
fn test_is_in_ghost_region_starts_at_end() {
    let ghost_span = Span::new(
        BytePos(10),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_span = Span::new(
        BytePos(50),
        BytePos(60),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(
        !is_in_ghost_region(stmt_span, &[ghost_span]),
        "statement starting at ghost region end should be outside"
    );
}

/// Zero-width span at a position inside the ghost region.
#[test]
fn test_is_in_ghost_region_zero_width_inside() {
    let ghost_span = Span::new(
        BytePos(10),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_span = Span::new(
        BytePos(25),
        BytePos(25),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(
        is_in_ghost_region(stmt_span, &[ghost_span]),
        "zero-width span inside ghost region should be considered inside"
    );
}

/// Zero-width span at a position outside the ghost region.
#[test]
fn test_is_in_ghost_region_zero_width_outside() {
    let ghost_span = Span::new(
        BytePos(10),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_span = Span::new(
        BytePos(55),
        BytePos(55),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(
        !is_in_ghost_region(stmt_span, &[ghost_span]),
        "zero-width span outside ghost region should be outside"
    );
}

/// Adjacent ghost regions with a gap — statement in the gap is outside both.
#[test]
fn test_is_in_ghost_region_gap_between_adjacent() {
    let ghost1 = Span::new(
        BytePos(10),
        BytePos(20),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let ghost2 = Span::new(
        BytePos(25),
        BytePos(40),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_in_gap = Span::new(
        BytePos(21),
        BytePos(24),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(
        !is_in_ghost_region(stmt_in_gap, &[ghost1, ghost2]),
        "statement in gap between two ghost regions should be outside"
    );
}

/// Nested ghost regions — statement inside the inner (smaller) region.
/// Both regions should match, but we only need one to return true.
#[test]
fn test_is_in_ghost_region_nested_regions() {
    let outer = Span::new(
        BytePos(10),
        BytePos(100),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let inner = Span::new(
        BytePos(30),
        BytePos(60),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt = Span::new(
        BytePos(35),
        BytePos(45),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(
        is_in_ghost_region(stmt, &[outer, inner]),
        "statement inside nested ghost regions should be inside"
    );
}

/// Statement at ghost region start boundary (lo matches, hi is inside).
#[test]
fn test_is_in_ghost_region_starts_at_ghost_start() {
    let ghost_span = Span::new(
        BytePos(10),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_span = Span::new(
        BytePos(10),
        BytePos(20),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(
        is_in_ghost_region(stmt_span, &[ghost_span]),
        "statement starting at ghost region start should be inside"
    );
}

/// Statement ending at ghost region end boundary (lo inside, hi matches).
#[test]
fn test_is_in_ghost_region_ends_at_ghost_end() {
    let ghost_span = Span::new(
        BytePos(10),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    let stmt_span = Span::new(
        BytePos(40),
        BytePos(50),
        rustc_span::SyntaxContext::root(),
        None,
    );
    assert!(
        is_in_ghost_region(stmt_span, &[ghost_span]),
        "statement ending at ghost region end should be inside"
    );
}
