//@ expect: reject
//@ mechanism: the inherent-method spelling of contract_free_async_fn_overflow_never_examined: an `async fn` in an `impl` block lowers to the same item-plus-coroutine pair, and the coroutine body was admitted by no discovery.
//@ accept-means: an addition that overflows, in an async method, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: at `x == 1`, `x + u32::MAX` overflows.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `zero verified ✓` and no line for the coroutine; REFUSED at the fix (`S::m::{closure#0} error: ... refused instead of credited`).
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;

impl S {
    pub async fn m(&self, x: u32) -> u32 {
        x + u32::MAX
    }
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
