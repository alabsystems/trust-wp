//@ expect: verify
//@ mechanism: IEEE-754 `!=` is exactly the negation of `==` (both operands NaN included), unlike `<`
//@ mechanism: and `>=`, which are not each other's negation. The IEEE model must still decide it, in a loop
//@ mechanism: too; the control for f64_ne_self_is_false.rs and f64_loop_carried_self_eq_despite_nan.rs.
//@ accept-means: n/a (control) — `(x != y) == !(x == y)` holds for every pair of floats.
//@ fixed-by: n/a (control)
//@ teeth: verified before and after D-215.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn ne_negates_eq(x: f64, y: f64) -> bool {
    (x != y) == !(x == y)
}

#[ensures(result)]
pub fn loop_carried_ne_negates_eq(x: f64) -> bool {
    let mut y = x;
    let mut i = 0;
    #[invariant(i <= 1)]
    while i < 1 {
        y = y + 0.0;
        i += 1;
    }
    (y != y) == !(y == y)
}
