//@ expect: reject
//@ mechanism: the call-result edge (`PremiseEdge`, `$call == 0`) guards arm 0's obligations
//@ mechanism: (`guard_int_arm_obligations`); the arm writes through the argument the switched call read and
//@ mechanism: calls it again, so the second result is another symbol over the written value.
//@ accept-means: an assert that fails on every execution of arm 0 is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(&mut 0)` takes arm 0, sets `*a = 1`, and `pick(a)` is 1.
//@ teeth: accepted if the second call read the pointee's entry value, the edge making the goal `$call == 0 ==> $call == 0`.
//@ also-verified: pick
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; an integer match arm's obligations are owed under the edge its premises are scoped by).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@ % 3)]
pub fn pick(x: &u32) -> u32 {
    *x % 3
}

#[ensures(true)]
pub fn f(a: &mut u32) {
    match pick(a) {
        0 => {
            *a += 1;
            assert!(pick(a) == 0);
        }
        _ => {}
    }
}
