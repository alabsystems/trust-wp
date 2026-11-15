//@ expect: reject
//@ mechanism: wp-s41 v2 — the loop-invariant path models only the resolved exit edge (`!cond`, the
//@ mechanism: invariant at the exit, a path-insensitive post-loop return walk); a break / in-loop return
//@ mechanism: was verified from that exit state.
//@ accept-means: `!cond` (i >= 10) assumed at a break with i == 3 (y06)
//@ fixed-by: wp-s41 v2 extraction.rs::loop_has_unmodeled_exit
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

#[ensures(result@ >= 10)]
pub fn f() -> i32 {
    let mut i = 0;
    #[invariant(true)]
    while i < 10 {
        if i == 3 {
            break;
        }
        i += 1;
    }
    i
}
