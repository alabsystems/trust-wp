//@ expect: reject
//@ mechanism: a value-stable edge read through a shared reference (`*p % 3 == 0`) guards arm 0's obligations
//@ mechanism: (`guard_int_arm_obligations`); the arm writes another place and asserts a fact about `*p` the edge
//@ mechanism: does not give.
//@ accept-means: an assert that fails on arm 0 is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(&0, &mut 0)` takes arm 0 and `*p == 1` is false.
//@ teeth: accepted if the edge made the goal vacuous.
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; an integer match arm's obligations are owed under the edge its premises are scoped by).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(p: &u32, q: &mut u32) {
    match *p % 3 {
        0 => {
            *q = 1;
            assert!(*p == 1);
        }
        _ => {}
    }
}
