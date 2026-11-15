//@ expect: reject
//@ mechanism: the isolating twin of clause_free_int_match_computed_arm_dead_control.rs: the `panic!`
//@ mechanism: arm is on `256`, which `x as u16 + 1` reaches at `x = 255`. The switch lane's charge
//@ mechanism: that the arm is not taken is refuted, so no edge is cut and the body is not verified.
//@ accept-means: a clause-free body that panics at `x = 255` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `widened(255)` panics.
//@ verdict: failed
//@ teeth: `failed` with and without D-142's proved edges; the twin verifies only with them.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn widened(x: u8) {
    match x as u16 + 1 {
        256 => panic!(),
        _ => {}
    }
}
