//@ expect: reject
//@ verdict: failed
//@ fn-failed: hop
//@ mechanism: the RED twin of deref_copy_guard_callee_requires_control: the guard is `x != 1`, so
//@ mechanism: `hop(&0)` reaches `needs_nonzero(0)`. A frozen-memory guard that wrapped the obligation
//@ mechanism: in the wrong condition, or dropped it, would verify this.
//@ accept-means: `hop(&0)` divides by zero in `needs_nonzero` and the crate is credited.
//@ fixed-by: D-118
//@ teeth: refuted before and after D-118; the pair separates a guard that discharges from one that
//@ teeth: is merely present.
//@ also-verified: needs_nonzero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ != 0)]
#[ensures(result@ == 10 / x@)]
pub fn needs_nonzero(x: u32) -> u32 {
    10 / x
}

pub fn hop(x: &u32) -> u32 {
    let x = *x;
    if x != 1 { needs_nonzero(x) } else { 0 }
}
