//@ expect: reject
//@ mechanism: `let mut b = 50; if d { b = small() }; let a = if c { b } else { 5 }` before an annotated
//@ mechanism: loop whose invariant claims `a@ < 10`. D-244 lets a loop-entry value read a local the walk
//@ mechanism: follows through every whole definition (`names_its_walk_value`); `b`'s join keeps the arm
//@ mechanism: that leaves it 50.
//@ accept-means: a loop invariant is initiated from the value of one arm of a join.
//@ WHY IT IS FALSE: `go(true, false, 1)` enters the loop with `a == 50`.
//@ also-verified: small
//@ teeth: rejected with D-243 and with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ < 10)]
pub fn small() -> u32 { 3 }

#[requires(n@ < 100)]
pub fn go(c: bool, d: bool, n: u32) {
    let mut b = 50u32;
    if d { b = small(); }
    let a = if c { b } else { 5u32 };
    let mut i = 0u32;
    #[invariant(i@ <= n@ && a@ < 10)]
    while i < n { i += 1; }
}
