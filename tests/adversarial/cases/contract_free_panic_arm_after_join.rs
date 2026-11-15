//@ expect: reject
//@ mechanism: the clause-free cap (`unchecked_panic_sites`) skips a switch edge only when EVERY walk visit of the switch stated the edge unreachable as a goal of the verified VC (`ProvedDeadEdges`, D-142: recorded by the lane that pushed the goal, only where `primary_arithmetic_is_exact`).
//@ mechanism: the panic switch is reached along two paths with different values of `v`; each visit states its own goal, and the `c == false` visit's `!(10 > 5)` is refuted.
//@ accept-means: a panic reached on one of two paths into its switch is credited because the other path's goal holds.
//@ WHY THE CONTRACT IS FALSE: `f(false)` panics.
//@ teeth: rejected (`f FAILED`) with and without the credit; the isolating twin contract_free_panic_arm_after_join_control.rs (`4` in place of `10`) verifies only with it.
//@ verdict: failed
//@ fn-failed: f
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(c: bool) {
    let v = if c { 0u32 } else { 10u32 };
    if v > 5 {
        panic!()
    }
}
