//@ expect: reject
//@ mechanism: `*b += 1` through `b = &mut x` on ONE arm, `x` a by-value parameter. The write's
//@ mechanism: rvalue names `x`, whose binding on entry to the arm is the parameter's own symbol, and
//@ mechanism: the name lane reads that symbol at the post-write state too, so the arm's premises
//@ mechanism: state `x == (x + 1) + 1`: contradictory on the arm alone. The vacuity guard judges the
//@ mechanism: whole premise set, which the other arm satisfies, and the arm's guarded assertion is
//@ mechanism: credited.
//@ accept-means: a write through a local borrow of a parameter makes the premises of the path that
//@ accept-means: writes contradictory, and an assertion guarded by that path is credited.
//@
//@ WHY THE ASSERTION IS FALSE, as a concrete execution: f(0, true) leaves x at 1, not 999.
//@ teeth: UNVERIFIED — ACCEPTED at exit 0 whether the legacy deref handlers record the rvalue as
//@ teeth: written or the governed write's resolved value; the defect is live. It would reject if
//@ teeth: the parameter's entry symbol and its post-write value were never read by one name, or if
//@ teeth: a path's own premises were checked for vacuity.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100 && x@ > -100)]
pub fn f(mut x: i32, c: bool) {
    if c {
        let b = &mut x;
        *b += 1;
    }
    proof_assert!(c ==> x@ == 999);
}
