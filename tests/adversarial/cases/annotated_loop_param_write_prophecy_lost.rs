//@ expect: reject
//@ mechanism: A `&mut` parameter is written DIRECTLY inside an annotated loop body, and the
//@ mechanism: identity resolve `r_final == r_current` is emitted anyway. ROOT-CAUSED by
//@ mechanism: bisection on the driver: making the post-loop final-value injection
//@ mechanism: (`inject_post_loop_final_values`) a no-op rejects this case and its three
//@ mechanism: siblings. That injection stands in a mut-borrow body built from the LOOP
//@ mechanism: lane's final values and covers every `&mut` parameter, including ones whose
//@ mechanism: writes it never observed — the code that GRANTS the resolve is not the code
//@ mechanism: that saw the body. Disabling it wholesale also breaks
//@ mechanism: annotated_loop_unwritten_control, so the fix is not the disable.
//@ accept-means: any `^`-bearing postcondition is worthless on a function that contains one
//@ accept-means: annotated loop; the grant is keyed on the SHAPE of the function rather than
//@ accept-means: on having seen the writes.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut v = 0; f(&mut v); afterwards
//@ v == 9, so `^r` is 9 while `*r` is 0.
//@ teeth: OPEN. Measured ACCEPTED, exit 0, "trust-wp: f verified ✓". Dropping the
//@ teeth: `#[invariant]` attribute from this same loop makes the verdict `failed`, and
//@ teeth: `loop { *r = 9; break; }` is rejected as well, so it is the annotated-loop lane
//@ teeth: that grants the identity resolve, not loops in general.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    let mut i = 0i32;
    #[invariant(true)]
    while i < 1 {
        *r = 9;
        i += 1;
    }
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 9);
}
