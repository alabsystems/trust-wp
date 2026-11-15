//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so the bounds check of `a[i]` through `a: &mut [T]` (`PtrMetadata` of a fake raw borrow of `*a`) demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee; the fake borrow translates as the reborrow `&*a`.
//@ mechanism: here the check's condition joins the path after the check, and the slice local traded pointers with a LONGER slice through `std::mem::swap`: a length read of the stale pointer would make the path fact `2 < 1` and every later goal vacuous.
//@ accept-means: `never()`'s precondition was discharged by a false path fact about a stale length.
//@ WHY THE CONTRACT IS FALSE: `s1` is `b` (five elements), `s1[2]` succeeds and `never()` is called, whose precondition is `false`.
//@ teeth: UNVERIFIED: the fact is the same term as the check's own goal, so a false fact is an unprovable goal at the same point; with the own-storage rule disabled by a local knob this is `f FAILED`. It pins that argument.
//@ also-verified: never
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(false)]
fn never() {}

#[requires(a@.len() == 1 && b@.len() == 5)]
pub fn f<'a>(a: &'a mut [u32], b: &'a mut [u32]) {
    let mut s1: &mut [u32] = a;
    let mut s2: &mut [u32] = b;
    std::mem::swap(&mut s1, &mut s2);
    s1[2] = 3;
    never();
}
