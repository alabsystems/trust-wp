//@ expect: reject
//@ mechanism: async_block_overflow_never_examined with the block written by a `macro_rules!` expansion. The plain-closure arithmetic discovery skips a closure whose span comes from an expansion (that is how it tells ghost and snapshot machinery apart), so a coroutine discovery that copied that rule would miss this one.
//@ accept-means: an addition that overflows, in a macro-expanded async block, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: at `x == 1`, which the precondition admits, `x + u32::MAX` overflows.
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

macro_rules! mk {
    ($x:expr) => {
        async move { $x + u32::MAX }
    };
}

#[requires(0 < x@ && x@ < 100)]
#[ensures(result@ == x@)]
pub fn f(x: u32) -> u32 {
    let _f = mk!(x);
    x
}
