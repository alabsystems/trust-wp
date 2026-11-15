//@ expect: reject
//@ mechanism: the clause-free cap skips a switch edge the walk proved dead on every crossing (`ProvedDeadEdges`, D-142): the credit is only as good as the arm guard the charging goal states, and a `SwitchInt` value is a bit pattern (`u128`) that must be read at the discriminant's sign and width.
//@ mechanism: here the `-1` arm is reachable (`x < 0`), so its goal `x < 0 ==> !(x == -1)` is refuted and nothing is credited.
//@ accept-means: the switch value `-1` was read as its bit pattern (`4294967295`), an `i32` never equals it, and the charged edge credited a body that panics as panic-free.
//@ WHY THE CONTRACT IS FALSE: `f(-1)` panics (a contract-free fn is checked under `requires true`).
//@ teeth: UNVERIFIED as a hole: rejected (`f FAILED`) with and without D-142's proved edges. It pins the sign of the value the charged edge rests on; the isolating twin is switch_negative_value_panic_arm_unreachable_control.rs, identical but for `x > 0`, which verifies only with the credit.
//@ verdict: failed
//@ fn-failed: f
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(x: i32) -> i32 {
    if x < 0 {
        match x {
            -1 => panic!(),
            _ => return 0,
        }
    }
    1
}
