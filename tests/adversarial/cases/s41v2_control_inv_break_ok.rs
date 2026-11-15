//@ expect: verify
//@ xfail: over-refusal (Creusot verifies): loops with a break/return besides the resolved exit fail closed on the invariant path (loop_has_unmodeled_exit). Re-entry: model the break states in the loop postcondition VC.
//@ mechanism: wp-s41 v2 — invariant loop with a break whose state satisfies the postcondition.
//@ accept-means: n/a (control) — i <= 10 on both exits
//@ fixed-by: wp-s41 v2 extraction.rs::loop_has_unmodeled_exit
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

#[ensures(result@ <= 10)]
pub fn f() -> i32 {
    let mut i = 0;
    #[invariant(i@ <= 10)]
    while i < 10 {
        if i == 3 {
            break;
        }
        i += 1;
    }
    i
}
