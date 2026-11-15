//@ expect: reject
//@ mechanism: `*b += 1` through `b = &mut x`, where the by-value parameter `x` was reassigned on
//@ mechanism: one arm only. The governed write-back resolves the rvalue's `x` against the binding
//@ mechanism: the walk holds on each path: `10` on the arm that reassigned, and on the other `x`
//@ mechanism: itself, the entry symbol the name lane also reads the POST-write state by. The fact
//@ mechanism: is `x == if c { 10 + 1 } else { (x + 1) + 1 }`, contradictory on `!c` alone. Handed
//@ mechanism: the resolved value, the legacy deref handlers no longer double the `c` arm, so the
//@ mechanism: premises are satisfiable and the vacuity guard, which judges the whole premise set,
//@ mechanism: passes an assertion the `!c` contradiction proves. Recording the rvalue as written
//@ mechanism: doubles the `c` arm too, and the whole set is UNSAT (D-171).
//@ accept-means: a write through a local borrow of a parameter makes a reachable path's premises
//@ accept-means: contradictory, and an assertion guarded by that path is credited.
//@
//@ WHY THE ASSERTION IS FALSE, as a concrete execution: f(0, false) leaves x at 1, not 11.
//@ verdict: unknown
//@ refused-with: vacuous proof
//@ fixed-by: fix(write-back): the legacy deref handlers record the rvalue as written again (D-171)
//@ teeth: ACCEPTED at exit 0 with the governed write's resolved value handed to the legacy deref
//@ teeth: handlers; refused as vacuous with the rvalue recorded as written, where the arm that
//@ teeth: reassigned is doubled too and the whole premise set is UNSAT. The rejection rests on that
//@ teeth: contradiction, not on the post-write value: the path-local defect underneath is
//@ teeth: deref_write_through_local_borrow_of_param_in_one_arm, which is live.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100 && x@ > -100)]
pub fn f(mut x: i32, c: bool) {
    if c {
        x = 10;
    }
    let b = &mut x;
    *b += 1;
    proof_assert!(!c ==> x@ == 11);
}
