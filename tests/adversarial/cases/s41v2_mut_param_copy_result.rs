//@ expect: reject
//@ mechanism: wp-s41 v2 — the post-loop re-bind skipped parameters, so a loop-written by-value
//@ mechanism: parameter was read at its ENTRY name, which `requires` constrains.
//@ accept-means: a loop-written parameter copied after the loop read at its entry value (w10)
//@ fixed-by: wp-s41 v2 havoc_skipped_loop_state parameters
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
    let mut i = 0;
    while i < 3 {
        x = 9;
        i += 1;
    }
    let y = x;
    y
}
