//@ expect: verify
//@ mechanism: R4 (`root_unnamed`) — LIVE blast-radius control in the Seq lane. The `get_mut_ghost`
//@ mechanism: shape is present in this body and adjudicated; the obligation sits BEFORE it.
//@ fixed-by: n/a (this is the standing gate an R4 closure must not break)
//@ accept-means: n/a (control) — this contract is TRUE and verifies TODAY.
//@
//@ The `Seq` half of `g_r4_prior_obligation_control`, and it is needed separately because the two
//@ lanes have different std contracts (see `g_r4_seq_scrutinee_stale_value` for the asymmetry) and
//@ different carrier encodings. A closure that only disturbs the sequence carrier would leave the
//@ FMap control green.
//@
//@ WHY THE CONTRACT IS TRUE: the assertion is discharged against the sequence right after the push,
//@ before the `get_mut_ghost` call.
//@ teeth: n/a — over-refusal control. ★MEASURED verifying on main (ACCEPTED) with the R4 candidate
//@ teeth: shape present in the same body.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn seq_prior_obligation_survives() {
    let mut v = Seq::new();
    ghost! {
        v.push_back_ghost(21);
        proof_assert!(v[0] == 21i32);
        if let Some(x) = v.get_mut_ghost(0int) {
            *x = 42;
        }
    };
}
