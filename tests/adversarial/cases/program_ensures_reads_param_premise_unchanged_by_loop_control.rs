//@ expect: verify
//@ mechanism: a control for D-243's retirement of a premise a later loop may change: `below(x)` before a loop that
//@ mechanism: does not write `x`, so the premise `x@ < 100` stays a premise after the loop and proves the
//@ mechanism: postcondition about the returned `x`.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
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

#[ensures(result@ < 100)]
pub fn f(x: u32) -> u32 {
    below(x);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
    x
}
