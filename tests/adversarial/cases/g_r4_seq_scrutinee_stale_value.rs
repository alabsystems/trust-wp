//@ expect: reject
//@ mechanism: R4 (`root_unnamed`) in the SECOND live census lane — `ghost_vec`'s
//@ mechanism: `if let Some(x) = v.get_mut_ghost(0int) { *x = 42 }`, carrying a FALSE claim about the
//@ mechanism: element's value after the write.
//@ fixed-by: n/a (OPEN — R4 refuses to pin; prerequisite gate for closing it)
//@ accept-means: `(^v)[0]` was equated to the payload's PRE-write value. Same inversion as
//@ accept-means: `g_r4_scrutinee_stale_value`, reached through `Seq` rather than `FMap`.
//@
//@ ★WHY BOTH LANES ARE HERE AND NOT JUST ONE: the M6 census emitted exactly two `root_unnamed`
//@ disarms, one in `ghost_map` and one in `ghost_vec`, and their std contracts are NOT the same
//@ strength. `FMap::GET_MUT_GHOST` pins the `None` branch hard (`!self.contains(*k)`,
//@ `!(^self).contains(*k)`, plus frame and length clauses). `Seq::GET_MUT_GHOST`'s `None` branch is
//@ only `arg1 < 0 || arg1 >= self.len()` — it says NOTHING about `^self` at all, so after an
//@ out-of-range call the whole post-sequence is unconstrained. A closure that gets the guard wrong
//@ therefore has a wider opening in the `Seq` lane than in the `FMap` lane, and a case that covered
//@ only `FMap` would gate the narrower one.
//@
//@ WHY THE CONTRACT IS FALSE: the sequence holds `[21]`, index 0 is in range, the arm runs and
//@ writes 42. Refutable by running `seq_scrutinee_stale_value()`.
//@ teeth: PROSPECTIVE — NOT an A/B-demonstrated accept. Measured today: rejected (`unknown`, ~26s),
//@ teeth: unchanged when the case budget is raised to 300s. Rejected trivially: `Seq::GET_MUT_GHOST`
//@ teeth: carries no `(^self)[arg1] == ^v` clause and R4 emits no pin, so `(^v)[0]` is unconstrained
//@ teeth: in both directions.
//@ teeth: WHAT A WRONG R4 FIX MUST DO TO START ACCEPTING THIS: add the missing `(^self)[arg1] == ^v`
//@ teeth: write-back to `Seq::GET_MUT_GHOST` (the R4 closure needs it — a caller-side pin on `^x`
//@ teeth: reaches the sequence through no other clause) while the payload's `Final` still collapses
//@ teeth: onto the binder. Then `(^v)[0] == *x == 21` and this contract is proved.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn seq_scrutinee_stale_value() {
    let mut v = Seq::new();
    ghost! {
        v.push_back_ghost(21);
        if let Some(x) = v.get_mut_ghost(0int) {
            *x = 42;
        }
        proof_assert!(v[0] == 21i32);
    };
}
