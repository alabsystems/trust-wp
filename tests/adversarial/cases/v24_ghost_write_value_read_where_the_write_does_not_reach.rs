//@ expect: reject
//@ mechanism: a whole-value ghost write `*g = v` is recovered from the source and overrides `g`'s
//@ mechanism: substitution at a later assertion. The last write in source order was taken whether
//@ mechanism: or not it reaches the assertion: one in an `if` the assertion need not pass (gdb),
//@ mechanism: and one in an `if` after a write that does (gds). The override now holds only where
//@ mechanism: the write's MIR store dominates the assertion and neither `g` nor a name its value
//@ mechanism: reads is written on a path between; otherwise `g` is left unconstrained (FactScope,
//@ mechanism: D-190). gdc is the shape the override exists for, and it still verifies.
//@ also-verified-assertion: creusot_test::gdc
//@ accept-means: a ghost write in a branch is read as the value at a later assertion.
//@ WHY THE CONTRACT IS FALSE: with c = false, g holds 0 (gdb) and 1 (gds).
//@ fixed-by: D-190
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on a3819cee the assertions of gdb and gds VERIFIED; with D-190 both are unknown, and
//@ teeth: gdc's assertion verifies on both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn gdb(c: bool) {
    let mut g = ghost! {0i32};
    if c {
        let _ = ghost! {
            *g = 1i32;
        };
    }
    let _ = ghost! {
        proof_assert!(*g == 1i32);
    };
}

pub fn gds(c: bool) {
    let mut g = ghost! {0i32};
    let _ = ghost! {
        *g = 1i32;
    };
    if c {
        let _ = ghost! {
            *g = 2i32;
        };
    }
    let _ = ghost! {
        proof_assert!(*g == 2i32);
    };
}

pub fn gdc() {
    let mut g = ghost! {0i32};
    let _ = ghost! {
        *g = 1i32;
    };
    let _ = ghost! {
        proof_assert!(*g == 1i32);
    };
}
