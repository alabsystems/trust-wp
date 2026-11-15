// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop write sites reached through a `&mut` call argument.

use super::analyze_all_loops;

const SETNEG: &str = r"
    fn setneg(x: &mut i32) { *x = -5; }
    fn need(_x: i32) {}
";

#[test]
fn mut_call_argument_is_a_write_site_of_the_loop() {
    let source = format!(
        "{SETNEG}
        pub fn f(n: u32) {{
            let mut x: i32 = 1;
            let mut i: u32 = 0;
            while i < n {{ setneg(&mut x); need(x); i += 1; }}
        }}"
    );
    let loops = analyze_all_loops(&source, "f", &["n"]);
    assert_eq!(loops.len(), 1, "one loop expected");
    assert!(
        loops[0].modified_vars.iter().any(|name| name == "x"),
        "`setneg(&mut x)` is a write site of x: {:?}",
        loops[0].modified_vars
    );
    assert!(
        loops[0].changed_places.0.contains_key("x"),
        "`setneg(&mut x)` changes x: {:?}",
        loops[0].changed_places
    );
}

#[test]
fn mut_call_argument_in_a_prior_loop_drops_the_binding_of_a_later_loop() {
    let source = format!(
        "{SETNEG}
        pub fn f(n: u32) {{
            let mut x: i32 = 1;
            let mut i: u32 = 0;
            while i < n {{ setneg(&mut x); i += 1; }}
            let mut j: u32 = 0;
            while j < n {{ need(x); j += 1; }}
        }}"
    );
    let loops = analyze_all_loops(&source, "f", &["n"]);
    assert_eq!(loops.len(), 2, "two loops expected");
    let later = loops
        .iter()
        .find(|loop_body| loop_body.pre_loop_assignments.contains_key("j"))
        .expect("the later loop binds j");
    assert!(
        !later.pre_loop_assignments.contains_key("x"),
        "a prior loop's `setneg(&mut x)` rewrites x: {:?}",
        later.pre_loop_assignments
    );
    // The prior loop's own counter is dropped for the same reason; the later
    // loop's own pre-loop binding survives.
    assert!(
        later.pre_loop_assignments.contains_key("j"),
        "j is assigned only after the prior loop: {:?}",
        later.pre_loop_assignments
    );
}

#[test]
fn a_local_no_loop_writes_keeps_its_binding() {
    let source = format!(
        "{SETNEG}
        pub fn f(n: u32) {{
            let mut x: i32 = 1;
            let y: i32 = n as i32 + 3;
            let mut i: u32 = 0;
            while i < n {{ setneg(&mut x); i += 1; }}
            let mut j: u32 = 0;
            while j < n {{ need(y); j += 1; }}
        }}"
    );
    let loops = analyze_all_loops(&source, "f", &["n"]);
    let later = loops
        .iter()
        .find(|loop_body| loop_body.pre_loop_assignments.contains_key("j"))
        .expect("the later loop binds j");
    assert!(
        later.pre_loop_assignments.contains_key("y"),
        "no loop writes y: {:?}",
        later.pre_loop_assignments
    );
    assert!(
        !later.pre_loop_assignments.contains_key("x"),
        "the prior loop writes x: {:?}",
        later.pre_loop_assignments
    );
    let first = loops
        .iter()
        .find(|loop_body| loop_body.modified_vars.iter().any(|name| name == "i"))
        .expect("the first loop writes i");
    assert!(
        !first.modified_vars.iter().any(|name| name == "y"),
        "the first loop does not write y: {:?}",
        first.modified_vars
    );
    assert!(
        !first.modified_vars.iter().any(|name| name == "n"),
        "the first loop does not write n: {:?}",
        first.modified_vars
    );
}
