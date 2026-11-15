//@ expect: reject
//@ verdict: unknown
//@ refused-with: `__lfidU__ambiguous__constant__K` was not resolved to one definition by the driver
//@ mechanism: a `proof_assert!` spells `K` in module `a` (0); the proof-assert lane built its own
//@ mechanism: copy of the short-name table and gave it `b::K` (10).
//@ accept-means: `a::f` asserts `a::K == 10`, which is `0 == 10`.
//@ fixed-by: D-111 (a bare constant name the crate gives more than one meaning is refused wherever the table substitutes it)
//@ teeth: MEASURED before D-111: ACCEPTED, exit 0, `proof_assert in creusot_test::a::f verified ✓` and `a::f verified ✓`. At the fix every clause spelling the name is refused and no function in the crate is credited on it; const_short_name_unique_control.rs, one constant spelled everywhere, verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    pub const K: u32 = 0;
    #[ensures(true)]
    pub fn f() {
        proof_assert!(K == 10u32);
    }
}

pub mod b {
    pub const K: u32 = 10;
}
