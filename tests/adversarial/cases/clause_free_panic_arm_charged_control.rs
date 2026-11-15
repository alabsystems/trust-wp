//@ expect: verify
//@ mechanism: control for D-142 — a clause-free body whose only panic sites are arms the switch
//@ mechanism: lane charges unreachable and discharges: an `unreachable!()` under a guard no `x`
//@ mechanism: satisfies, and the failing arm of an `assert!` every `x` passes. Before D-142
//@ mechanism: `cap_clause_free_verdict` counted every reachable panic entry point unchecked and
//@ mechanism: demoted this body to `unknown (partial: panic paths unchecked (panic call))`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn hop(x: u32) -> u32 {
    if x > 10 && x < 5 {
        unreachable!();
    }
    assert!(x < 11 || x > 4);
    x
}
