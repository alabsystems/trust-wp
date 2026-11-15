//@ expect: verify
//@ mechanism: a branch before the loop that sets `n` on one path leaves `m`'s entry binding alone (D-243 drops
//@ mechanism: only the bindings that read a local set on one path).
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(c: bool) {
    let m = 5u32;
    let mut n = 0u32;
    if c {
        n = 1;
    }
    let mut i = 0u32;
    #[invariant(m == 5u32)]
    while i < 3 {
        i += 1;
    }
    let _ = n;
}
