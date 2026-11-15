//@ expect: reject
//@ mechanism: a program function builds a tuple `(0, 0)`, runs an annotated loop, writes its input `x` into the first field and asserts `t.0 == 0`. The assertion is proved: the post-loop assertion lane reads the tuple at its loop-exit value `(0, 0)`, not after the write (the same shape as program_ensures_after_loop_field_write_fact_meets_loop_exit_fact.rs, in the `proof_assert!` lane, which its fix does not touch).
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means an assertion after a loop reads a local at the value the post-loop code leaves it, never at its loop-exit value.
//@ accept-means: an assertion that fails for every nonzero input is credited, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, 1)` leaves `t.0 == 1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: proof_assert in creusot_test::prog verified ✓`, `trust-wp: prog verified ✓ (loop invariant + call obligations)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn prog(n: u32, x: u32) {
    let mut t = (0u32, 0u32);
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    t.0 = x;
    proof_assert!(t.0 == 0u32);
}
