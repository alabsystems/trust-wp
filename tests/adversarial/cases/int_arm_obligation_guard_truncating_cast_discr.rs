//@ expect: reject
//@ mechanism: each obligation one walk of a plain integer match arm records is owed under that arm's edge
//@ mechanism: (`guard_int_arm_obligations`), spelled over the condition `PremiseEdge` admits as denoting the
//@ mechanism: value the switch tests.
//@ mechanism: here the switch tests `x as u8`: the edge must read the truncation, since `x == 0` is false
//@ mechanism: for `x == 256`, which takes arm 0.
//@ accept-means: a body that panics on arm 0 is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(256)` takes arm 0 (`256 as u8 == 0`) and panics.
//@ teeth: accepted if the edge read the cast's operand for its value, weakening arm 0's goal where `x == 256`.
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; an integer match arm's obligations are owed under the edge its premises are scoped by).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(x: u32) {
    match x as u8 {
        0 => {
            if x == 256 {
                panic!()
            }
        }
        _ => {}
    }
}
