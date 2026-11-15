//@ expect: reject
//@ mechanism: the clause-free cap skips a switch edge the walk proved dead on every crossing (`ProvedDeadEdges`, D-142): the credit is only as good as the arm guard the charging goal states, and a `SwitchInt` value is a bit pattern (`u128`) that must be read at the discriminant's sign and width.
//@ mechanism: here the `i8::MIN` arm is reachable, the value whose bit pattern (`128`) lies outside `i8`'s range when read unsigned.
//@ accept-means: `-128` was read as `128`, no `i8` equals it, and the charged edge credited a body that panics as panic-free.
//@ WHY THE CONTRACT IS FALSE: `f(-128)` panics (a contract-free fn is checked under `requires true`).
//@ teeth: UNVERIFIED as a hole: rejected (`f FAILED`) with and without D-142's proved edges; it pins the value's sign at the narrowest width.
//@ verdict: failed
//@ fn-failed: f
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(x: i8) -> i8 {
    match x {
        -128 => panic!(),
        _ => 0,
    }
}
