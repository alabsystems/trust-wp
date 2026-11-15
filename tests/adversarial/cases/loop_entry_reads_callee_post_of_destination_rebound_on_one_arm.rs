//@ expect: reject
//@ mechanism: `let mut m = one(); if c { m = 5; }` before an annotated loop whose invariant reads `m == 1u32`.
//@ mechanism: The walker names `one`'s result by `m` and states `m == 1`; the loop lane drops `m`'s entry
//@ mechanism: binding, set on one path (D-243 (d)), so that postcondition alone would initiate the invariant.
//@ accept-means: an invariant is initiated from a callee's postcondition about a value the arm rebinds.
//@ WHY THE CONTRACT IS FALSE: `f(n, true)` enters the loop with `m == 5`.
//@ also-verified: one
//@ teeth: `error` before D-243; a draft of D-243 (d) without the site symbol ACCEPTED it at exit 0; `failed`
//@ teeth: with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 1u32)]
pub fn one() -> u32 {
    1
}

#[requires(n < 10u32)]
pub fn f(n: u32, c: bool) {
    let mut m = one();
    if c {
        m = 5;
    }
    let mut i = 0u32;
    #[invariant(m == 1u32)]
    while i < n {
        i += 1;
    }
}
