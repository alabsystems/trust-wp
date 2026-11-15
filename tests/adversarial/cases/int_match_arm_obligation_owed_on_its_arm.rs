//@ expect: reject
//@ mechanism: `guard_int_arm_obligations` turns each obligation an integer match arm records into
//@ mechanism: `edge ==> obligation`, the edge being the arm's (`x % 3 == 0`). The guard must weaken the goal
//@ mechanism: only on executions that take another arm: arm 0 panics for `y >= 100`, and nothing excludes it.
//@ accept-means: a body that panics on arm 0 is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(0, 200)` takes arm 0 and panics.
//@ teeth: accepted if the arm's obligation were guarded by an edge that arm 0's executions falsify, or dropped.
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; an integer match arm's obligations are owed under the edge its premises are scoped by).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(x: u32, y: u32) {
    match x % 3 {
        0 => {
            if y >= 100 {
                panic!()
            }
        }
        _ => {}
    }
}
