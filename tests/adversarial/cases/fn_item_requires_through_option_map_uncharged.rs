//@ expect: reject
//@ mechanism: a FUNCTION ITEM carrying `#[requires]` handed to `Option::map`. The combinator calls
//@ mechanism: it with whatever the option holds, and its builtin spec owes nothing for the item's
//@ mechanism: precondition: `needs_nonzero`'s `x != 0` was granted to its body and owed by nobody.
//@ mechanism: No verification of the item can pay for it (its body is verified UNDER the
//@ mechanism: precondition), so the host that hands it over is refused.
//@ accept-means: `pick` is reported `verified` although `pick(Some(0))` divides by zero in
//@ accept-means: `needs_nonzero`.
//@ fixed-by: D-118
//@ teeth: ACCEPTED, exit 0, `needs_nonzero verified` and `pick verified`, on the binary before
//@ teeth: D-118. After it `pick`'s credit is withdrawn.
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

// FALSE: `pick(Some(0))` calls `needs_nonzero(0)`.
#[ensures(result@ == 1)]
pub fn pick(o: Option<u32>) -> u32 {
    let _ = o.map(needs_nonzero);
    1
}
