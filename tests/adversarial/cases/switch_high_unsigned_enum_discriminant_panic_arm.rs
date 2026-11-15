//@ expect: reject
//@ mechanism: the clause-free cap skips a switch edge the walk proved dead on every crossing (`ProvedDeadEdges`, D-142): the credit is only as good as the arm guard the charging goal states, and a `SwitchInt` value is a bit pattern (`u128`) that must be read at the discriminant's sign and width.
//@ mechanism: here the switch reads the discriminant of a `#[repr(u8)]` enum whose `B` is `255`, the value a sign-extending read would take for `-1`, and `B`'s arm panics.
//@ accept-means: `255` was read as `-1`, the arm's guard is false in the model, and the charged edge credited a body that panics as panic-free.
//@ WHY THE CONTRACT IS FALSE: `f(E::B)` panics (a contract-free fn is checked under `requires true`).
//@ teeth: UNVERIFIED as a hole: rejected (`f FAILED`) with and without D-142's proved edges; it pins that an unsigned discriminant is not sign-extended under the charged edge.
//@ verdict: failed
//@ fn-failed: f
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[repr(u8)]
pub enum E {
    A = 200,
    B = 255,
}

pub fn f(e: E) -> u32 {
    match e {
        E::A => 0,
        E::B => panic!(),
    }
}
