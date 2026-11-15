//@ expect: reject
//@ mechanism: the loan spelling of proof_assert_after_loop_assigned_local_reads_pre_loop_value.rs: a program function sets `t` to `0`, borrows it mutably, runs an annotated loop, writes its input through the borrow and asserts `t == 0`. The `proof_assert!` lane after a loop reads `t` at its value before the loop; the write names the loan, never `t` (the shape D-165 item 3 closes for `result`, in a lane it does not touch).
//@ fixed-by: OPEN — committed RED rather than hidden.
//@ accept-means: an assertion that fails for every nonzero input is credited, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, 1)` leaves `t == 1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with D-165: `trust-wp: proof_assert in creusot_test::prog verified ✓`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn prog(n: u32, x: u32) {
    let mut t = 0u32;
    let r = &mut t;
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    *r = x;
    proof_assert!(t == 0u32);
}
