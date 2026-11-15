//@ expect: reject
//@ mechanism: an overflow after an `.await`: the coroutine body suspends at a `Yield` no lane models, then adds, and the awaiting body was admitted by no discovery.
//@ accept-means: an addition that overflows after an `.await` is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: `b(x)` returns `x`, and at `x == 1` the sum overflows.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `zero verified ✓` and no line for the coroutine; REFUSED at the fix (`a::{closure#0} error: ... refused instead of credited`).
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub async fn b(x: u32) -> u32 {
    x
}

pub async fn a(x: u32) -> u32 {
    b(x).await + u32::MAX
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
