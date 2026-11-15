//@ expect: reject
//@ mechanism: the interior-mutability store the frozen-memory guard of D-118 must never see past: the
//@ mechanism: guard reads a `Cell` through a SHARED reference, the arm `set`s it to 0, then passes
//@ mechanism: `get()` to `needs_nonzero`. No `&mut` is taken and nothing is written through a
//@ mechanism: projection, so the value-stability walk alone admits the switch; the frozen-memory rule
//@ mechanism: refuses it because `Cell` reaches an `UnsafeCell`.
//@ accept-means: `hop(&Cell::new(5))` sets 0 and divides by zero in `needs_nonzero`.
//@ fixed-by: D-118
//@ teeth: refuted before and after D-118.
//@ also-verified: needs_nonzero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::cell::Cell;

#[requires(x@ != 0)]
#[ensures(result@ == 10 / x@)]
pub fn needs_nonzero(x: u32) -> u32 {
    10 / x
}

pub fn hop(c: &Cell<u32>) -> u32 {
    if c.get() != 0 {
        c.set(0);
        needs_nonzero(c.get())
    } else {
        0
    }
}
