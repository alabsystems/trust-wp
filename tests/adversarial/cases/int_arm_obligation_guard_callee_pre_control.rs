//@ expect: verify
//@ mechanism: each obligation one walk of a plain integer match arm records is owed under that arm's edge
//@ mechanism: (`guard_int_arm_obligations`): arm 0 passes `x % 3 * 1000`, which is below 100 only where
//@ mechanism: `x % 3 == 0`, the edge of the arm that makes the call.
//@ mechanism: control: refuted at the campaign tip, where a plain integer match arm's goals are owed on every
//@ mechanism: path. Twin of int_arm_obligation_guard_callee_pre.rs.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
pub fn need_small(x: u32) {}

#[ensures(true)]
pub fn f(x: u32) {
    match x % 3 {
        0 => need_small(x % 3 * 1000),
        1 => need_small(5),
        _ => {}
    }
}
