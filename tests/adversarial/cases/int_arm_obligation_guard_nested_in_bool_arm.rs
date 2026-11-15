//@ expect: reject
//@ mechanism: an integer match nested in a boolean arm: the inner arm's panic goal is owed under the inner
//@ mechanism: edge (`guard_int_arm_obligations`) and then the outer condition; both hold on the panicking path.
//@ accept-means: a body that panics on the inner arm is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(true, 0, 200)` panics.
//@ teeth: accepted if either edge weakened the goal on the path that panics.
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; an integer match arm's obligations are owed under the edge its premises are scoped by).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(b: bool, x: u32, y: u32) {
    if b {
        match x % 3 {
            0 => {
                if y >= 100 {
                    panic!()
                }
            }
            _ => {}
        }
    }
}
