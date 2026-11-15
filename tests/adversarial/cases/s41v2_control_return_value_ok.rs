//@ expect: verify
//@ xfail: over-refusal (Creusot verifies): the merge havoc re-binds the return place at the shared return block, losing `_0 = 7` on the return path. Re-entry: check in-loop returns against the postcondition from the havocked walk state instead of havocking the result.
//@ mechanism: wp-s41 v2 — in-loop return whose value satisfies the postcondition.
//@ accept-means: n/a (control) — both returns satisfy the ensures
//@ fixed-by: wp-s41 v2 loop_merges.rs
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

#[ensures(result@ == 7 || result@ == 0)]
pub fn f() -> i32 {
    let mut i = 0;
    while i < 10 {
        if i == 3 {
            return 7;
        }
        i += 1;
    }
    0
}
