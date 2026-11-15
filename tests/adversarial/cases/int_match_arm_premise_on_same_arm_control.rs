//@ expect: verify
//@ mechanism: an integer match arm's premises and its in-arm obligations are scoped by one edge
//@ mechanism: (`PremiseEdge`, `guard_int_arm_obligations`): here the translated condition `x % 3 == 0`, whose
//@ mechanism: discriminant reads only the parameter `x` and is value-stable.
//@ mechanism: control: `below(y)` and the panic switch are on arm 0, so the postcondition holds wherever the
//@ mechanism: panic goal is owed. With the premise scoped and the obligation unconditional, the goal is
//@ mechanism: refuted.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

#[ensures(true)]
pub fn f(x: u32, y: u32) {
    match x % 3 {
        0 => {
            below(y);
            if y >= 100 {
                panic!()
            }
        }
        _ => {}
    }
}
