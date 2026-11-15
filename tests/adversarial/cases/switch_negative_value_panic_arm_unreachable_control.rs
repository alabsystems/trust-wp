//@ expect: verify
//@ mechanism: the clause-free cap skips a switch edge the walk proved dead on every crossing (`ProvedDeadEdges`, D-142): the credit is only as good as the arm guard the charging goal states, and a `SwitchInt` value is a bit pattern (`u128`) that must be read at the discriminant's sign and width.
//@ mechanism: control: the arm's goal `x > 0 ==> !(x == -1)` holds, so the charged edge leaves the cap and the body verifies. Twin of switch_negative_value_panic_arm.rs.
//@ accept-means: n/a (control)
//@ teeth: capped at `unknown (partial: panic paths unchecked (panic call))` without the credit.
//@ fixed-by: D-142 — the switch lanes record the edges their charges prove dead, and the clause-free cap does not walk them
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(x: i32) -> i32 {
    if x > 0 {
        match x {
            -1 => panic!(),
            _ => return 0,
        }
    }
    1
}
