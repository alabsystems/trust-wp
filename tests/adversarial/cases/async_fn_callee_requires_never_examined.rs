//@ expect: reject
//@ mechanism: a callee's `#[requires]` violated inside a contract-free `async fn`. The call sits in the coroutine body, not in the item's MIR, so `body_calls_requires_bearing_callee` never saw it and the precondition `0 < x` was owed by nobody.
//@ accept-means: a call that violates its callee's precondition, in an `async fn`, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: `needs_pos(0)` violates `x@ > 0` for every run of `c`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `needs_pos verified ✓` and no line for `c`; REFUSED at the fix (`c::{closure#0} error: ... refused instead of credited`).
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: needs_pos
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ > 0)]
#[ensures(result@ == x@)]
pub fn needs_pos(x: u32) -> u32 {
    x
}

pub async fn c() -> u32 {
    needs_pos(0)
}
