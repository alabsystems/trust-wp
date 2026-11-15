//@ expect: reject
//@ mechanism: the division spelling of contract_free_async_fn_overflow_never_examined: `x / y` in a contract-free `async fn` owes `y != 0`, and its coroutine body was admitted by no discovery.
//@ accept-means: a division by a possibly-zero divisor, in an `async fn`, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: at `y == 0` the division panics.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `zero verified ✓` and no line for the coroutine; REFUSED at the fix (`d::{closure#0} error: ... refused instead of credited`).
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub async fn d(x: u32, y: u32) -> u32 {
    x / y
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
