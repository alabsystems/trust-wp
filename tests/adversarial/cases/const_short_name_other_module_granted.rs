//@ expect: reject
//@ verdict: unknown
//@ refused-with: `__lfidU__ambiguous__constant__K` was not resolved to one definition by the driver
//@ mechanism: a bare constant name in a clause was given the value of whichever local constant item
//@ mechanism: of that short name was collected last. `a::f` claims `result == K`, where `K` in module
//@ mechanism: `a` is `a::K` (0); the table keyed constants by short name only, so `b::K` (10) overwrote
//@ mechanism: `a::K` and `f`, which returns 10, verified.
//@ accept-means: `a::f` claims `result == a::K`, which is 0, and returns 10.
//@ fixed-by: D-111 (a bare constant name the crate gives more than one meaning is refused wherever the table substitutes it)
//@ teeth: MEASURED before D-111: ACCEPTED, exit 0, `a::f verified ✓`. With the modules in the other order `a::K` wins the table and `b::f` (returning 0) FAILED, so the verdict followed declaration order, not scope. At the fix every clause spelling the name is refused and no function in the crate is credited on it; const_short_name_unique_control.rs, one constant spelled everywhere, verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    pub const K: u32 = 0;
    #[ensures(result == K)]
    pub fn f() -> u32 {
        10
    }
}

pub mod b {
    pub const K: u32 = 10;
}
