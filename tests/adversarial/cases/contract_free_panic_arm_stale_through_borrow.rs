//@ expect: reject
//@ mechanism: the clause-free cap (`unchecked_panic_sites`) skips a switch edge only when EVERY walk visit of the switch stated the edge unreachable as a goal of the verified VC (`ProvedDeadEdges`, D-142: recorded by the lane that pushed the goal, only where `primary_arithmetic_is_exact`).
//@ mechanism: the condition reads a local written through a `&mut`; the walk's value for it is the stale `0`, so a goal stated from it would hold. The switch is not value-stable (its goal is the fail-closed `false`) and the body is not exact (no edge is recorded).
//@ accept-means: a panic behind a condition the walk reads stale is credited as unreachable.
//@ WHY THE CONTRACT IS FALSE: `*r = 10` makes `x > 5` true, so `f()` always panics.
//@ teeth: UNVERIFIED as a regression gate for the recording guard: two guards (the value-stability `false` and `primary_arithmetic_is_exact`) each refuse it, and disabling one leaves the other.
//@ verdict: unknown
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let mut x = 0u32;
    let r = &mut x;
    *r = 10;
    if x > 5 {
        panic!()
    }
}
