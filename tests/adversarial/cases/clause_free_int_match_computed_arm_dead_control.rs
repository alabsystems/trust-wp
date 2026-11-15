//@ expect: verify
//@ mechanism: D-142 over the integer-switch lane with a computed discriminant: `x as u16 + 1` is at
//@ mechanism: least 1, so the `panic!` arm on `0` is charged unreachable, the charge is proved from
//@ mechanism: the parameter's range, and the arm leaves the clause-free cap. Isolating twin of
//@ mechanism: clause_free_int_match_computed_arm_live.rs, which differs in the arm's literal.
//@ teeth: control; `unknown (partial: panic paths unchecked)` with D-142's proved edges withheld.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn widened(x: u8) {
    match x as u16 + 1 {
        0 => panic!(),
        _ => {}
    }
}
