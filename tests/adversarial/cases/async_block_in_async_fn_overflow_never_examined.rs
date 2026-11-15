//@ expect: reject
//@ mechanism: an `async` block inside an `async fn`: a coroutine body nested in another, neither admitted by any discovery, and the inner one overflows.
//@ accept-means: an addition that overflows, in a nested async block, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: at `x == 1`, `x + u32::MAX` overflows.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `zero verified ✓` and no line for the coroutine; REFUSED at the fix (`outer::{closure#0}::{closure#0} error: ... refused instead of credited`).
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub async fn outer(x: u32) -> u32 {
    let _inner = async move { x + u32::MAX };
    x
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
