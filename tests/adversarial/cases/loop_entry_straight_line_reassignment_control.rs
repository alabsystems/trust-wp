//@ expect: verify
//@ mechanism: `let mut m = 1u32; m = m + 1;` on the one path to the loop: both assignments dominate the
//@ mechanism: header, so the loop lane keeps its entry binding `m == 2` (D-243 drops only a binding set on one path).
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let mut m = 1u32;
    m = m + 1;
    let mut i = 0u32;
    #[invariant(m == 2u32)]
    while i < 3 {
        i += 1;
    }
}
