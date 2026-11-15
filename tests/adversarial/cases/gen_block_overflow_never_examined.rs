//@ expect: reject
//@ mechanism: the `gen` block spelling of async_block_overflow_never_examined: a generator block is a coroutine body of its own, admitted by no discovery, and the addition it yields overflows.
//@ accept-means: an addition that overflows, in a `gen` block, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: at `x == 1`, which the precondition admits, `x + u32::MAX` overflows.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `f verified ✓` and no line for the coroutine; REFUSED at the fix (`f::{closure#2} error: ... refused instead of credited`).
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(gen_blocks)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(0 < x@ && x@ < 100)]
#[ensures(result@ == x@)]
pub fn f(x: u32) -> u32 {
    let _g = gen move {
        yield x + u32::MAX;
    };
    x
}
