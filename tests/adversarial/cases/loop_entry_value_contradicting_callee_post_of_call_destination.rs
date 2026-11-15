//@ expect: reject
//@ mechanism: `let mut m = big(); if c { m = 2 }` (`big` ensures `result > 100u32`) before an annotated loop,
//@ mechanism: then `m` is returned under `ensures(c ==> result == 7u32)`. Were `big`'s postcondition stated
//@ mechanism: over the name `m`, the loop-entry value D-243 states over the same name (`c ==> m == 2`) would
//@ mechanism: contradict it on the arm and prove anything there.
//@ accept-means: a function that returns 2 when `c` holds is credited with returning 7.
//@ WHY THE CONTRACT IS FALSE: `f(true)` returns 2.
//@ also-verified: big
//@ teeth: rejected before and with D-243; it pins the scope of D-243 (f): a call whose destination may change again
//@ teeth: before a loop is entered names its result by a symbol of its site. A draft of D-243 (e) that named it
//@ teeth: `m` and stated the loop-entry value ACCEPTED it at exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result > 100u32)]
pub fn big() -> u32 {
    255
}

#[ensures(c ==> result == 7u32)]
pub fn f(c: bool) -> u32 {
    let mut m = big();
    if c {
        m = 2;
    }
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3 {
        i += 1;
    }
    m
}
