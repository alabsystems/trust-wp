//@ expect: verify
//@ mechanism: the TRUE twin of ghost_marker_written_by_hand_runs_ghost_deref: the ghost-block marker
//@ mechanism: `ghost!` and `ghost_let!` write is honoured, so a deref in the block they keep under
//@ mechanism: `cfg(trust_wp)` is ghost code, which never runs.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — verified with every marker honoured, and with only the expansion's.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 7i32)]
pub fn f() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    ghost_let!(h = *g + 1i32);
    let _k = ghost! {
        let x: i32 = *g;
        x
    };
    proof_assert!(*h == 6i32);
    7
}
