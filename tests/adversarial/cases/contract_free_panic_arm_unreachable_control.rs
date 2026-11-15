//@ expect: verify
//@ mechanism: the clause-free cap (`unchecked_panic_sites`) skips a switch edge only when EVERY walk visit of the switch stated the edge unreachable as a goal of the verified VC (`ProvedDeadEdges`, D-142: recorded by the lane that pushed the goal, only where `primary_arithmetic_is_exact`).
//@ mechanism: control: the arm's goal `x > 200 ==> !(x < 100)` holds, so the charged edge leaves the cap and the body verifies. Twin of contract_free_panic_arm_reachable.rs.
//@ accept-means: n/a (control)
//@ teeth: capped at `unknown (partial: panic paths unchecked (panic call))` without the credit.
//@ fixed-by: D-142 — the switch lanes record the edges their charges prove dead, and the clause-free cap does not walk them
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(x: u8) {
    if x > 200 {
        if x < 100 {
            panic!()
        }
    }
}
