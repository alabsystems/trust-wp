//@ expect: reject
//@ mechanism: the assertion side of bare_call_mixed_arity_family_block_program_fn_granted.rs: `host`
//@ mechanism: asserts `m(s) == 10u32` where Rust's `m` is the program function of `host`'s block (0).
//@ mechanism: The family holds the method `S::m` (10) and the free `other::m(a, b)`, so the resolver
//@ mechanism: leaves the bare call under its written name and the encoder dispatches it on `s`'s sort
//@ mechanism: to `S::m`: the assertion is proved.
//@ fixed-by: D-200 — REFUSED: a bare call is method-style exactly where every definition of its
//@ fixed-by: arity is a method (`identity::dispatches_on_receiver`, the predicate the encoder's
//@ fixed-by: receiver dispatch asks), so the program function's call is spelled with the refusal
//@ fixed-by: marker instead of being left for the dispatch.
//@ accept-means: the assertion `m(s) == 10u32` about the block's program function (0) is credited
//@ accept-means: and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`proof_assert in creusot_test::host verified ✓`) with D-199
//@ teeth: in force.
//@ teeth: With D-200: REFUSED (`unknown`): the assertion in `creusot_test::host` errors on the
//@ teeth: unresolved marker `__lfidU__m`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;
impl S {
    #[logic(open)]
    pub fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}

pub mod other {
    use crate::S;
    use creusot_std::prelude::*;

    #[logic(open)]
    pub fn m(_a: S, _b: S) -> u32 {
        pearlite! { 5u32 }
    }
}

pub fn host(s: S) -> u32 {
    fn m(_x: S) -> u32 {
        0
    }
    proof_assert!(m(s) == 10u32);
    m(s)
}
