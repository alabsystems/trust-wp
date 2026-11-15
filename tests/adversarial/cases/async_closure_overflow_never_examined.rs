//@ expect: reject
//@ mechanism: the async-closure spelling of async_block_overflow_never_examined: an async closure's body is a coroutine (`is_coroutine_body` says so), but a coroutine body with arithmetic and no `proof_assert!` is admitted by no discovery (`has_arithmetic_panic_sites` returns false on a `coroutine_kind`), so D-106's refusal never meets it and the crate exits 0.
//@ accept-means: an addition that overflows, in an async closure the crate compiles, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: at `x == 1`, which the precondition admits, `x + u32::MAX` overflows.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-106 and on the commit before it: `f verified ✓` and no line for the closure. REFUSED at D-117: `f::{closure#2}::{closure#0} error: ... refused instead of credited`.
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(0 < x@ && x@ < 100)]
#[ensures(result@ == x@)]
pub fn f(x: u32) -> u32 {
    let _c = async move || x + u32::MAX;
    x
}
