//@ expect: reject
//@ verdict: unknown
//@ refused-with: `__lfidU__ambiguous__constant__K` was not resolved to one definition by the driver
//@ mechanism: an inherent associated constant `W::K` (10) was keyed by its short name beside the free
//@ mechanism: constant `K` (0), and overwrote it. A bare `K` never denotes an associated constant in
//@ mechanism: Rust; `f`'s clause means the free `K`.
//@ accept-means: `f` claims `result == K`, which is 0, and returns 10.
//@ fixed-by: D-111 (a bare constant name the crate gives more than one meaning is refused wherever the table substitutes it)
//@ teeth: MEASURED before D-111: ACCEPTED, exit 0, `f verified ✓`. At the fix every clause spelling the name is refused and no function in the crate is credited on it; const_short_name_unique_control.rs, one constant spelled everywhere, verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub const K: u32 = 0;

#[ensures(result == K)]
pub fn f() -> u32 {
    10
}

pub struct W;

impl W {
    pub const K: u32 = 10;
}
