//@ expect: verify
//@ mechanism: `let mut m = 10u32; if c { m = 20 }`, a loop that leaves `m` alone, and a postcondition that holds
//@ mechanism: for either path's value (D-243).
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result >= 10u32 && result <= 20u32)]
pub fn f(c: bool) -> u32 {
    let mut m = 10u32;
    if c {
        m = 20;
    }
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3 {
        i += 1;
    }
    m
}
