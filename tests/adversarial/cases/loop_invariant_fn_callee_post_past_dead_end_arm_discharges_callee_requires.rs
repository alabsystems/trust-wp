//@ expect: reject
//@ mechanism: the reach formula of the block-slice walker (`call_effect_reach::BlockReach`) passes a join as its
//@ mechanism: immediate dominator when every path from the dominator reaches it. A path that enters a loop with no
//@ mechanism: exit (`if d { need_small(x); loop {} }`) reaches no return either, and a walk that only asked that no
//@ mechanism: path ENDS on the way read the join after `if c { if d { .. } }` as running whenever the entry does:
//@ mechanism: `below`'s postcondition `x@ < 100` became a premise of every goal, and `need_small`'s precondition, owed
//@ mechanism: on the arm that never reaches `below`, was discharged by it. Found probing sideways from D-243.
//@ accept-means: a precondition owed on a path that never reaches the call establishing it is discharged by that
//@ accept-means: call's postcondition, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, true, true)` calls `need_small(200)`.
//@ also-verified: below, need_small
//@ fixed-by: D-243: a join passes as its dominator only when every block met on the way can still reach it.
//@ teeth: ACCEPTED at exit 0 before D-243, and with D-243's reach formula before that rule; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
pub fn need_small(x: u32) {}

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

pub fn f(x: u32, c: bool, d: bool) {
    if c {
        if d {
            need_small(x);
            #[invariant(true)]
            loop {}
        }
    }
    below(x);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
}
