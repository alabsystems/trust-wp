//@ expect: verify
//@ mechanism: control for v13_parameter_borrow_assigned_into_a_holder_place_write_unseen: a borrow
//@ mechanism: that is NOT the parameter's, stored into a holder's field and written through it,
//@ mechanism: charges nothing to the parameter, whose own write keeps its exact final value. D-128
//@ mechanism: havocs the roots the stored value carries, not every parameter of a function that
//@ mechanism: stores a borrow into a place.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^x == 3i32)]
pub fn other_borrow_stored(x: &mut i32) {
    let mut b = 0i32;
    let mut c = 1i32;
    let mut t = (&mut b, 0i32);
    t.0 = &mut c;
    *t.0 = 5i32;
    *x = 3i32;
}
