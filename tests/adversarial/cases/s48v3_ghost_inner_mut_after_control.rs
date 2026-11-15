//@ expect: verify
//@ xfail: the honest twin of s48v3_ghost_inner_mut_handback is NOT provable today, and that is the residual defect this front did not close: advancing the ghost receiver havocs the cell, so `*g` after the write is unconstrained and the TRUE value is unrecoverable. Measured on this program: `proof_assert in creusot_test::k FAILED ✗`, base_exit_code=1. It was ALSO refuted before the audit (the same probe at 4c05ec5a), when the false twin was being ACCEPTED — so the build never had a consistent view of this cell. Retire this xfail when a write through a ghost-forwarded reborrow flows back to the ghost cell; that fix also empties MUT_REBORROW_PROJECTION_PATHS_KNOWN_UNSOUND.
//@ mechanism: control for the `::Ghost::inner_mut` arm — the same program asserting the value the write actually leaves behind.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn k() {
    let mut g = ghost!(5i32);
    ghost! {
        let r: &mut i32 = g.inner_mut();
        *r = 7;
    };
    proof_assert!(*g == 7i32);
}
