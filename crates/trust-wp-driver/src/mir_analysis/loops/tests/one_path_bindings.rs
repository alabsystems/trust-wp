// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The loop lane states no entry value for a local set on one path to the
//! loop's header (D-243).

use trust_wp_core::formula::PureExpr;

use super::analyze_function;

#[test]
fn binding_set_on_one_arm_is_dropped() {
    let source = r"
pub fn f(c: bool) -> u32 {
    let mut m = 1u32;
    if c {
        m = 2;
    }
    let mut i = 0u32;
    while i < 3 {
        i += 1;
    }
    m
}
";
    let (_, loop_body) = analyze_function(source, "f", &["c"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        !loop_body.pre_loop_assignments.contains_key("m"),
        "`m` is 1 or 2 at the header, never the one arm's value: {:?}",
        loop_body.pre_loop_assignments
    );
    assert_eq!(
        loop_body.pre_loop_assignments.get("i").map(|b| &b.value),
        Some(&PureExpr::Int(0)),
        "`i` is assigned on the one path to the header"
    );
}

#[test]
fn binding_computed_from_a_local_set_on_one_arm_is_dropped() {
    let source = r"
pub fn f(c: bool) -> u32 {
    let mut m = 1u32;
    if c {
        m = 2;
    }
    let j = m;
    let mut i = 0u32;
    while i < 3 {
        i += 1;
    }
    j
}
";
    let (_, loop_body) = analyze_function(source, "f", &["c"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        !loop_body.pre_loop_assignments.contains_key("j"),
        "`j` copies a local set on one arm: {:?}",
        loop_body.pre_loop_assignments
    );
}

#[test]
fn binding_on_the_one_path_beside_an_unrelated_branch_is_kept() {
    let source = r"
pub fn f(c: bool) -> u32 {
    let mut m = 1u32;
    m = m + 1;
    let mut n = 0u32;
    if c {
        n = 1;
    }
    let mut i = 0u32;
    while i < 3 {
        i += 1;
    }
    m + n
}
";
    let (_, loop_body) = analyze_function(source, "f", &["c"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.pre_loop_assignments.contains_key("m"),
        "both assignments of `m` dominate the header: {:?}",
        loop_body.pre_loop_assignments
    );
    assert!(
        !loop_body.pre_loop_assignments.contains_key("n"),
        "`n` is set on one arm: {:?}",
        loop_body.pre_loop_assignments
    );
}
