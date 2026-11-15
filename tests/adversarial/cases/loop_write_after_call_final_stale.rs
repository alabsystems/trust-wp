//@ expect: reject
//@ mechanism: the loop spelling of mut_ref_call_then_direct_write_final_stale: the write
//@ mechanism: that invalidates the call's prophecy credit is inside a loop body, so the
//@ mechanism: mut-borrow traversal (which gives up on a body with a back edge) sees
//@ mechanism: nothing and the post-loop lane rebuilds the body from the invariant alone.
//@ mechanism: A guard that rides the traversal's own state closes the straight-line
//@ mechanism: spellings and leaves this one live, which is why the credit has to be
//@ mechanism: disqualified from MIR directly.
//@ accept-means: any write reached through a loop back edge is invisible to the call
//@ accept-means: assumption that pinned the parameter's final value.
//@ WHY THE PROGRAM IS WRONG: the loop runs once and sets `*x` to 2; `^x` is 2, not 1.
//@ teeth: LIVE on the same probe binary that accepted the straight-line twin: ACCEPTED,
//@ teeth: `trust-wp: f verified`. Rejected once the credit is disqualified from MIR.
//@ also-verified: set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[requires(*x == 0i32)]
#[ensures(^x == 1i32)]
pub fn f(x: &mut i32) {
    set(x);
    let mut i = 0i32;
    #[invariant(i@ <= 1)]
    while i < 1i32 {
        *x = 2i32;
        i += 1i32;
    }
}
