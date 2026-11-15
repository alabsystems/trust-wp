//@ expect: reject
//@ mechanism: the sharpest spelling of proof_assert_after_loop_assigned_local_reads_pre_loop_value.rs: the same function asserts `x == 0` about its INPUT, which no statement writes. The `proof_assert!` lane after a loop holds `t == 0` (before the loop) and `t == x` (after it) under one name, so its premises imply `x == 0` and any assertion about `x` that follows from it is proved. A function with no loop is refuted on the same body.
//@ fixed-by: OPEN — committed RED rather than hidden; closes with proof_assert_after_loop_assigned_local_reads_pre_loop_value.rs.
//@ accept-means: the post-loop assertion lane's premises are contradictory for every nonzero input, and an assertion about an unwritten parameter is credited; the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, 1)` reaches the assertion with `x == 1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with D-165: `trust-wp: proof_assert in creusot_test::prog verified ✓`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn prog(n: u32, x: u32) {
    let mut t = 0u32;
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    t = x;
    proof_assert!(x == 0u32);
}
