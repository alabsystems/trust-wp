//@ expect: reject
//@ mechanism: an `unreachable!()` the precondition does not rule out, in an async block: a diverging call, Creusot's `Abort` goal, in a coroutine body admitted by no discovery.
//@ accept-means: a reachable `unreachable!()`, in an async block, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: at `x == 1`, which the precondition admits, the block reaches `unreachable!()`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `f verified ✓` and no line for the coroutine; REFUSED at the fix (`f::{closure#2} error: ... refused instead of credited`).
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
    let _fut = async move {
        if x == 1 {
            unreachable!()
        }
    };
    x
}
