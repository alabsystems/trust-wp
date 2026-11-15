//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so the bounds check of `a[i]` through `a: &mut [T]` (`PtrMetadata` of a fake raw borrow of `*a`) demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee; the fake borrow translates as the reborrow `&*a`.
//@ mechanism: here the slice local is shrunk by one element on every iteration of a loop that carries an invariant, so the loop lanes read the loop-carried pointer.
//@ accept-means: the bounds check inside the loop read the length the slice had on entry.
//@ WHY THE CONTRACT IS FALSE: on the third iteration `s` has one element and `s[1]` panics.
//@ teeth: control pair for the loop lanes, not a regression test of a hole: rejected before and after.
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@.len() == 3)]
pub fn f(a: &mut [u32]) {
    let mut s: &mut [u32] = a;
    let mut i = 0;
    #[invariant(i@ <= 3)]
    while i < 3 {
        s[1] = 7;
        s = &mut s[1..];
        i += 1;
    }
}
