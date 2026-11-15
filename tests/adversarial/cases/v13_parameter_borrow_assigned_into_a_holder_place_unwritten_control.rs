//@ expect: verify
//@ xfail: D-128 charges the escape at the STORE of the parameter's borrow into a holder's place, not
//@ xfail: at a later write that reaches it, so a store never written through refuses the TRUE `^x ==
//@ xfail: *x` (stored_unwritten, verified before D-128), and the write the holder carries is not
//@ xfail: carried to the parameter's final value (stored_written_true, TRUE `^x == 5`, unknown before
//@ xfail: and after). Retiring either needs the tracker to record WHICH borrow the place holds.
//@ mechanism: the price of v13_parameter_borrow_assigned_into_a_holder_place_write_unseen's fix,
//@ mechanism: kept visible: a refusal of a true claim, never a credit.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^x == *x)]
pub fn stored_unwritten(x: &mut i32) {
    let mut b = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = x;
}

#[ensures(^x == 5i32)]
pub fn stored_written_true(x: &mut i32) {
    let mut b = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = x;
    *t.0 = 5i32;
}
