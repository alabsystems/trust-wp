//@ expect: reject
//@ mechanism: wp-s41 v2 — the post-loop re-bind skipped parameters, so a loop-written by-value
//@ mechanism: parameter was read at its ENTRY name, which `requires` constrains.
//@ accept-means: `result == 0` proved from `requires(x == 0)` although the loop raised x to 5
//@ fixed-by: wp-s41 v2 PrimaryVisitor::havoc_skipped_loop_state parameters
//@ also-verified: need_zero, never, fine
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
fn need_zero(x: i32) {}

#[requires(false)]
fn never() {}

#[requires(true)]
fn fine(x: i32) {}

fn set5(x: &mut i32) {
    *x = 5;
}

#[requires(x@ == 0)]
#[ensures(result@ == 0)]
pub fn f(mut x: i32) -> i32 {
    while x < 5 {
        x += 1;
    }
    x
}
