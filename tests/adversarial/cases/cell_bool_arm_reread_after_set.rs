//@ expect: reject
//@ mechanism: a boolean switch on a `Cell` read; the arm writes the cell and reads it again. The condition
//@ mechanism: that guards the arm's goals (`guard_bool_branch_obligations`) and the re-read must not be one term.
//@ accept-means: an assert that fails on every execution of the then arm is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(&Cell::new(0))` takes the then arm, sets 5, and the assert panics.
//@ teeth: accepted if the guard `get(c) == 0` and the re-read shared one term.
//@ fixed-by: n/a (pins the boolean lane's guard beside the integer lane's).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::cell::Cell;

#[ensures(true)]
pub fn f(c: &Cell<u32>) {
    if c.get() == 0 {
        c.set(5);
        assert!(c.get() == 0);
    }
}
