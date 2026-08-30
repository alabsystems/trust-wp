//@ expect: verify
//@ xfail: this IS the obligation R4 blocks. `reference/creusot/tests/should_succeed/ghost/ghost_map.rs`
//@ xfail: asserts exactly this line, and it is why the R4 closure is wanted at all: the payload of an
//@ xfail: `Option<&mut V>` has no prophecy slot, so `(^map)[1]` is unconstrained and the claim is
//@ xfail: unprovable. Measured today: rejected, and STILL rejected when the case budget is raised
//@ xfail: from 120s to 300s — this is a real wall, not a solver-budget artifact. Creusot proves it.
//@ mechanism: R4 (`root_unnamed`) — the TRUE twin of `g_r4_scrutinee_stale_value`
//@ fixed-by: n/a (open; this is the R4 target)
//@ accept-means: n/a (control). An XPASS here is the ONLY thing that shows an R4 closure did real
//@ accept-means: work rather than merely refusing more. Pair it with `g_r4_scrutinee_stale_value`,
//@ accept-means: which must still reject: the two bodies differ ONLY in `43` vs `21`, so nothing but
//@ accept-means: a pin carrying the correct DEATH value can separate them. A fix that flips both is
//@ accept-means: the prophecy inversion, not a fix.
//@
//@ WHY THE CONTRACT IS TRUE: key 1 is present, so the arm runs and writes 43; the borrow dies at the
//@ end of the arm and the entry's final value is 43.
//@ teeth: n/a — over-refusal control, currently xfail. Not demonstrated in either direction.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{logic::FMap, prelude::*};

pub fn scrutinee_honest_value() {
    let mut map = FMap::<i32, i32>::new();
    ghost! {
        map.insert_ghost(1, 21);
        if let Some(x) = map.get_mut_ghost(&1) {
            *x = 43;
        }
        proof_assert!(map.lookup(1i32) == 43i32);
    };
}
