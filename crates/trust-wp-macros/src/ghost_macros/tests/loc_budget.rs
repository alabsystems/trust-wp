// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Anti-regrowth LOC budget tests for ghost_macros module files.
//!
//! These tests fail when any ghost_macros production or test file exceeds its
//! LOC budget, preventing the module from regrowing into a monolith.

fn count_lines(source: &str) -> usize {
    source.lines().count()
}

#[test]
fn mod_rs_loc_budget() {
    let source = include_str!("../mod.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 220,
        "ghost_macros/mod.rs has {lines} lines, exceeding budget of 220"
    );
}

#[test]
fn ident_capture_loc_budget() {
    let source = include_str!("../ident_capture.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 350,
        "ghost_macros/ident_capture.rs has {lines} lines, exceeding budget of 350"
    );
}

#[test]
fn proof_assert_loc_budget() {
    let source = include_str!("../proof_assert.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 350,
        "ghost_macros/proof_assert.rs has {lines} lines, exceeding budget of 350"
    );
}

#[test]
fn snapshot_loc_budget() {
    let source = include_str!("../snapshot.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 350,
        "ghost_macros/snapshot.rs has {lines} lines, exceeding budget of 350"
    );
}

#[test]
fn ghost_block_loc_budget() {
    let source = include_str!("../ghost_block.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 350,
        "ghost_macros/ghost_block.rs has {lines} lines, exceeding budget of 350"
    );
}

#[test]
fn ghost_let_loc_budget() {
    let source = include_str!("../ghost_let.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 350,
        "ghost_macros/ghost_let.rs has {lines} lines, exceeding budget of 350"
    );
}

#[test]
fn test_ident_capture_loc_budget() {
    let source = include_str!("ident_capture.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 350,
        "ghost_macros/tests/ident_capture.rs has {lines} lines, exceeding budget of 350"
    );
}

#[test]
fn test_proof_assert_loc_budget() {
    let source = include_str!("proof_assert.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 350,
        "ghost_macros/tests/proof_assert.rs has {lines} lines, exceeding budget of 350"
    );
}

#[test]
fn test_ghost_let_loc_budget() {
    let source = include_str!("ghost_let.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 350,
        "ghost_macros/tests/ghost_let.rs has {lines} lines, exceeding budget of 350"
    );
}
