//@ expect: reject
//@ mechanism: an integer match on a `Cell` read: the discriminant reads a shared reference to interior-mutable
//@ mechanism: memory, and the arm writes the cell and reads it again. The edge that guards the arm's goals
//@ mechanism: (`guard_int_arm_obligations`) and the re-read must not be one term.
//@ accept-means: an assert that fails on every execution of arm 0 is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(&Cell::new(0))` takes arm 0, sets 5, and the assert panics.
//@ teeth: accepted if the edge `get(c) == 0` and the re-read shared one term.
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; an integer match arm's obligations are owed under the edge its premises are scoped by).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::cell::Cell;

#[ensures(true)]
pub fn f(c: &Cell<u32>) {
    match c.get() {
        0 => {
            c.set(5);
            assert!(c.get() == 0);
        }
        _ => {}
    }
}
