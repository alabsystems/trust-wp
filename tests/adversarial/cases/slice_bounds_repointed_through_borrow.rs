//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so the bounds check of `a[i]` through `a: &mut [T]` (`PtrMetadata` of a fake raw borrow of `*a`) demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee; the fake borrow translates as the reborrow `&*a`.
//@ mechanism: here the slice local itself is re-pointed through a `&mut` borrow of its own storage, which the length demand must refuse.
//@ accept-means: the bounds check read the length of the slice `s` pointed to BEFORE `*r = b` re-pointed it.
//@ WHY THE CONTRACT IS FALSE: `s` is `b` (one element) when `s[2]` runs, so every call panics.
//@ teeth: UNVERIFIED as a gate on the own-storage rule alone: with that rule disabled by a local knob this is still `f FAILED`, the primary lane does not keep `s` bound to `a` past the borrow. It pins the shape.
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@.len() == 5 && b@.len() == 1)]
pub fn f<'a>(a: &'a mut [u32], b: &'a mut [u32]) {
    let mut s: &mut [u32] = a;
    let r = &mut s;
    *r = b;
    s[2] = 3;
}
