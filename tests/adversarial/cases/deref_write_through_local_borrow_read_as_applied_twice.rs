//@ expect: reject
//@ mechanism: `*b += 1` through `b = &mut x` translates to `x + 1`, an rvalue naming the owner's
//@ mechanism: PRE-write value. The governed write-back binds `x` to it resolved (`12 + 1`); the
//@ mechanism: legacy single-deref handler that runs after it records the raw rvalue for the borrow
//@ mechanism: chain, which the name lane reads at the POST-write binding as `(12 + 1) + 1`. The
//@ mechanism: doubled value must never stand alone (D-171).
//@ accept-means: a write through a local borrow is applied twice to the value an assertion reads.
//@
//@ WHY THE ASSERTION IS FALSE, as a concrete execution: after `*b += 1`, x is 13, not 14.
//@ teeth: UNVERIFIED — rejected with the raw rvalue recorded, where the doubled value sits beside
//@ teeth: the single one and the vacuity guard refuses the contradiction, and rejected with the
//@ teeth: resolved value recorded; it would verify only if the doubled value stood alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn doubled() {
    let mut x = 12i32;
    let b = &mut x;
    *b += 1;
    proof_assert!(x@ == 14);
}
