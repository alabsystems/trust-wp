//@ expect: reject
//@ mechanism: an integer match on a `Cell` read; the arm writes the cell and passes a re-read to a callee
//@ mechanism: whose precondition the switched value would satisfy. The edge that guards the arm's goals
//@ mechanism: (`guard_int_arm_obligations`) and the re-read must not be one term.
//@ accept-means: a call that violates its callee's precondition on arm 0 is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(&Cell::new(0))` takes arm 0 and calls `need_zero(5)`.
//@ teeth: accepted if the edge `get(c) == 0` and the re-read shared one term.
//@ also-verified: need_zero
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; an integer match arm's obligations are owed under the edge its premises are scoped by).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::cell::Cell;

#[requires(x@ == 0)]
pub fn need_zero(x: u32) {}

#[ensures(true)]
pub fn f(c: &Cell<u32>) {
    match c.get() {
        0 => {
            c.set(5);
            need_zero(c.get());
        }
        _ => {}
    }
}
