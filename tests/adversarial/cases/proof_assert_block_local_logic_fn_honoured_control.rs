//@ expect: verify
//@ xfail: `k` is declared in a nested block of `host`'s body, and D-195 refuses such a name for a body
//@ xfail: clause rather than place the assertion: the assertion is refused, not refuted. Before D-195
//@ xfail: the resolver read the crate root's `k` (10) and refuted it. The isolating twin of
//@ xfail: proof_assert_block_local_logic_fn_granted.rs.
//@ mechanism: control: the assertion `k() == 0` holds of the block's `k`, the function it names.
//@ fixed-by: n/a (control; resolving it needs the assertion's position in the body)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

pub fn host() -> u32 {
    {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
        proof_assert!(k() == 0);
    }
    0
}
