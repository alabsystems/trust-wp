//@ expect: reject
//@ mechanism: the store the frozen-memory guard of D-118 must never see past: the guard reads `*x`
//@ mechanism: through a `&mut`, the arm writes `*x = 0`, then calls `needs_nonzero(*x)`. Guard and
//@ mechanism: argument print as the same term, so `guard ==> obligation` would be `X ==> X`. The
//@ mechanism: switch operand's dependency is `&mut`-typed and written through, so the guard stays
//@ mechanism: refused and the obligation unconditional.
//@ accept-means: `hop(&mut 5)` stores 0 and divides by zero in `needs_nonzero`.
//@ fixed-by: D-118
//@ teeth: rejected before and after D-118 (`hop unknown`, the write through the `&mut` refused
//@ teeth: fail-closed); a guard rule that admitted every dereference would verify it.
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

pub fn hop(x: &mut u32) -> u32 {
    if *x != 0 {
        *x = 0;
        needs_nonzero(*x)
    } else {
        0
    }
}
