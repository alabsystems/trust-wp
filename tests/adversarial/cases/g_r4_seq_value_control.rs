//@ expect: verify
//@ xfail: this IS the `ghost_vec` obligation R4 blocks —
//@ xfail: `reference/creusot/tests/should_succeed/ghost/ghost_vec.rs` asserts exactly this line.
//@ xfail: `Seq::GET_MUT_GHOST` carries no `(^self)[arg1] == ^v` write-back and the `Option<&mut T>`
//@ xfail: payload has no prophecy slot, so `(^v)[0]` is unconstrained. Measured today: rejected.
//@ mechanism: R4 (`root_unnamed`) — the TRUE twin of `g_r4_seq_scrutinee_stale_value`
//@ fixed-by: n/a (open; this is the R4 target in the Seq lane)
//@ accept-means: n/a (control). An XPASS shows the Seq-lane closure did real work. It only counts
//@ accept-means: alongside a still-rejecting `g_r4_seq_scrutinee_stale_value` — the two bodies differ
//@ accept-means: ONLY in `42` vs `21`, so a fix that flips both has landed the inversion, not a fix.
//@
//@ WHY THE CONTRACT IS TRUE: index 0 is in range, the arm runs and writes 42, and the borrow dies at
//@ the end of the arm.
//@ teeth: n/a — over-refusal control, currently xfail. Not demonstrated in either direction.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn seq_honest_value() {
    let mut v = Seq::new();
    ghost! {
        v.push_back_ghost(21);
        if let Some(x) = v.get_mut_ghost(0int) {
            *x = 42;
        }
        proof_assert!(v[0] == 42i32);
    };
}
