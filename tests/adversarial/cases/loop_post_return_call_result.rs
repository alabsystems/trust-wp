//@ expect: reject
//@ mechanism: the value returned after the loop is a call's result, `r = inc(i)`, stored after the
//@ mechanism: loop into a local that held 0 before it. The post-loop return walk ends at a call it
//@ mechanism: does not model; keeping `r` at the value it held before the call proves `result == 0`.
//@ accept-means: `g(0)` returns 1, so `ensures(result == 0u32)` is FALSE, and trust-wp proved it.
//@ teeth: UNVERIFIED as a false-accept gate: rejected on every build measured. Before
//@ teeth: D-223, `g FAILED (postcondition)`; since D-165 the refutation is withheld as `unknown` (the
//@ teeth: post-loop walk does not read a call's result, so `result` is unbound), a genuine refutation
//@ teeth: that D-165 prices.
//@ also-verified: inc
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k < 100u32)]
#[ensures(result == k + 1u32)]
pub fn inc(k: u32) -> u32 { k + 1 }

#[requires(n < 50u32)]
#[ensures(result == 0u32)]
#[allow(unused_assignments)]
pub fn g(n: u32) -> u32 {
    let mut i = 0u32;
    let mut r = 0u32;
    #[invariant(i <= n)]
    while i < n { i += 1; }
    r = inc(i);
    r
}
