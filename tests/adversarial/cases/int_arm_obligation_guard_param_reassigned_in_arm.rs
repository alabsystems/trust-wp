//@ expect: reject
//@ mechanism: each obligation one walk of a plain integer match arm records is owed under that arm's edge
//@ mechanism: (`guard_int_arm_obligations`), spelled over the condition `PremiseEdge` admits as denoting the
//@ mechanism: value the switch tests.
//@ mechanism: here the arm reassigns the parameter the switch read: the edge is refused (`x` is not
//@ mechanism: value-stable), so the goal stays unconditional; an edge over `x` would read the new value.
//@ accept-means: a body that panics on arm 0 is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(0)` takes arm 0, sets `x = 1`, and `1 % 3 != 0` panics.
//@ teeth: accepted if the edge `x % 3 == 0` read the reassigned `x`, making the goal `x % 3 == 0 ==> x % 3 == 0`.
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; an integer match arm's obligations are owed under the edge its premises are scoped by).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(mut x: u32) {
    match x % 3 {
        0 => {
            x = 1;
            if x % 3 != 0 {
                panic!()
            }
        }
        _ => {}
    }
}
