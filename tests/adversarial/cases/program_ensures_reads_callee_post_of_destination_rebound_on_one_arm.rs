//@ expect: reject
//@ mechanism: `let mut m = one(); if c { m = 5; }`, an annotated loop that leaves `m` alone, then `m` is
//@ mechanism: returned under `ensures(result == 1u32)`. The code after the loop reads `m` by its name, the
//@ mechanism: name the walker gave `one`'s result; with the loop lane's entry binding dropped (D-243 (d)),
//@ mechanism: `one`'s postcondition alone would prove the claim.
//@ accept-means: a function that returns 5 on one path is credited with returning 1.
//@ WHY THE CONTRACT IS FALSE: `f(n, true)` returns 5.
//@ also-verified: one
//@ teeth: `failed` before D-243; a draft of D-243 (d) without the site symbol ACCEPTED it at exit 0;
//@ teeth: `failed` with D-243.
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
#[ensures(result == 1u32)]
pub fn f(n: u32, c: bool) -> u32 {
    let mut m = one();
    if c {
        m = 5;
    }
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    m
}
