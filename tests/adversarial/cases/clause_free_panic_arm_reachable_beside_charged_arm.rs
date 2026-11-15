//@ expect: reject
//@ mechanism: D-142 lets a clause-free `verified` stand when every panic call sits behind a switch
//@ mechanism: edge the walk proved dead. Here the first arm is proved dead (`x > 10 && x < 5`) and
//@ mechanism: the `assert!` arm is reachable: its own charge is refuted, so the body is FAILED, and
//@ mechanism: the proof of the first arm must not cover the second.
//@ accept-means: a proved-dead edge was read as covering a panic reached through another edge.
//@ WHY THE CONTRACT IS FALSE: a clause-free `verified` claims no execution panics; `hop(7)` panics.
//@ verdict: failed
//@ fn-failed: hop
//@ teeth: UNVERIFIED for the cap — the reachable arm's charge is refuted before the cap reads it;
//@ teeth: the case pins that a charged arm beside it never turns the refutation into a credit.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn hop(x: u32) -> u32 {
    if x > 10 && x < 5 {
        unreachable!();
    }
    assert!(x < 7 || x > 7);
    x
}
