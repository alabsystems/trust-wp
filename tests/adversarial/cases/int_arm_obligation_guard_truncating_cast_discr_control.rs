//@ expect: verify
//@ mechanism: each obligation one walk of a plain integer match arm records is owed under that arm's edge
//@ mechanism: (`guard_int_arm_obligations`), spelled over the condition `PremiseEdge` admits as denoting the
//@ mechanism: value the switch tests.
//@ mechanism: control: arm 0 panics only for `x == 5`, and `5 as u8` is 5, so no execution that takes
//@ mechanism: arm 0 panics; the goal is owed under the edge `x as u8 == 0`. Refuted before D-169, where a plain
//@ mechanism: integer match arm's goals were owed on every path. Twin of int_arm_obligation_guard_truncating_cast_discr.rs.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(x: u32) {
    match x as u8 {
        0 => {
            if x == 5 {
                panic!()
            }
        }
        _ => {}
    }
}
