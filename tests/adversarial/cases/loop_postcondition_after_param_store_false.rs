//@ expect: reject
//@ mechanism: reject twin of loop_postcondition_after_param_store_control: `(^a)@ == 0` holds of
//@ mechanism: the entry value the exit VC reads, and not of the `7` the store leaves.
//@ accept-means: `f` stores 7 and the loop keeps it, so `(^a)@ == 0` is FALSE, and trust-wp proved it.
//@ teeth: UNVERIFIED as a false-accept gate: rejected `unknown` before and after D-225; it pins that
//@ teeth: the withheld exit refutation of the control never turns into a proof.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
#[ensures((^a)@ == 0)]
pub fn f(a: &mut u32) {
    *a = 7;
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
}
