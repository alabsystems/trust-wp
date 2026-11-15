//@ expect: reject
//@ mechanism: the clause-free cap (`unchecked_panic_sites`) skips a switch edge only when EVERY walk visit of the switch stated the edge unreachable as a goal of the verified VC (`ProvedDeadEdges`, D-142: recorded by the lane that pushed the goal, only where `primary_arithmetic_is_exact`).
//@ mechanism: here the panic arm is reachable, so its goal `x > 200 ==> !(x < 250)` is refuted and nothing is credited.
//@ accept-means: a contract-free body whose `panic!` arm is taken for `x == 201` is credited as panic-free.
//@ WHY THE CONTRACT IS FALSE: `f(201)` panics (a contract-free fn is checked under `requires true`).
//@ teeth: control pair for the credit, not a regression test of a hole: rejected (`f FAILED`) with and without the credit. The isolating twin is contract_free_panic_arm_unreachable_control.rs, identical but for `x < 100`, which verifies only with the credit.
//@ verdict: failed
//@ fn-failed: f
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(x: u8) {
    if x > 200 {
        if x < 250 {
            panic!()
        }
    }
}
