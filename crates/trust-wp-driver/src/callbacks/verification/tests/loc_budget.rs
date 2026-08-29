// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Anti-regrowth LOC budget tests for the callbacks/verification subtree.

fn count_lines(source: &str) -> usize {
    source.lines().count()
}

#[test]
fn verification_root_loc_budget() {
    let source = include_str!("../../verification.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 400,
        "callbacks/verification.rs has {lines} lines, exceeding budget of 400"
    );
}

#[test]
fn verification_per_contract_loc_budget() {
    let source = include_str!("../per_contract.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 600,
        "callbacks/verification/per_contract.rs has {lines} lines, exceeding budget of 600"
    );
}

#[test]
fn verification_prep_loc_budget() {
    let source = include_str!("../prep.rs");
    let lines = count_lines(source);
    assert!(
        lines <= 450,
        "callbacks/verification/prep.rs has {lines} lines, exceeding budget of 450"
    );
}
