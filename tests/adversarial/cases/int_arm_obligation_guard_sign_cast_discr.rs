//@ expect: reject
//@ mechanism: each obligation one walk of a plain integer match arm records is owed under that arm's edge
//@ mechanism: (`guard_int_arm_obligations`), spelled over the condition `PremiseEdge` admits as denoting the
//@ mechanism: value the switch tests.
//@ mechanism: here the switch tests `x as i8` with `x: u8`: the edge must read the reinterpretation, so
//@ mechanism: `x == 255` takes the `-1` arm.
//@ accept-means: a body that panics on the `-1` arm is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(255)` takes the `-1` arm and panics.
//@ teeth: accepted if the edge compared the unsigned operand with `-1`, which no `u8` equals.
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; an integer match arm's obligations are owed under the edge its premises are scoped by).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(x: u8) {
    match x as i8 {
        -1 => {
            if x == 255 {
                panic!()
            }
        }
        _ => {}
    }
}
