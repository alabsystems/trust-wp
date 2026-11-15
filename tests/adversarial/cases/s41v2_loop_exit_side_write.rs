//@ expect: reject
//@ mechanism: wp-s41 v2 — the primary extractor skips a loop to its resolved exit arm; a break or
//@ mechanism: in-loop return that joins the post-loop code was never modelled, so the walked exit state
//@ mechanism: alone proved the postcondition. Creusot havocs loop-written places (implicit invariant true)
//@ mechanism: and checks every path out of the loop.
//@ accept-means: the exit arm's `y = 3` assumed on the `i == 5` break path
//@ fixed-by: wp-s41 v2 loop_merges.rs exit-side writes at the join
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

#[ensures(result@ == 3)]
pub fn f() -> i32 {
    let mut y = 0;
    let mut i = 0;
    loop {
        if i >= 10 {
            y = 3;
            break;
        }
        if i == 5 {
            break;
        }
        i += 1;
    }
    y
}
