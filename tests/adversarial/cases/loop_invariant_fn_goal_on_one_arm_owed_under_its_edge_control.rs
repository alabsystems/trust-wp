//@ expect: verify
//@ mechanism: a goal of the block-slice walker is owed under a formula that holds wherever its block runs (D-243):
//@ mechanism: `need_small(x)` on the `c` arm is owed as `c ==> x@ < 100`, which the precondition proves. Before
//@ mechanism: D-243 the walker owed it on every path, and the control failed.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
pub fn need_small(x: u32) {}

#[requires(c ==> x@ < 100)]
pub fn f(x: u32, c: bool) {
    if c {
        need_small(x);
    }
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
}
