//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so the bounds check of `a[i]` through `a: &mut [T]` (`PtrMetadata` of a fake raw borrow of `*a`) demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee; the fake borrow translates as the reborrow `&*a`.
//@ mechanism: here two slice locals trade pointers through `std::mem::swap` of their own storage.
//@ accept-means: the bounds check read the length `s1` had before the swap.
//@ WHY THE CONTRACT IS FALSE: `s1` is `b` (one element) when `s1[2]` runs, so every call panics.
//@ teeth: UNVERIFIED as a gate on the own-storage rule alone: with that rule disabled by a local knob this is still `f FAILED` (the call lane binds `s1` to `swap`'s `^x == *y`). It pins the shape.
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@.len() == 5 && b@.len() == 1)]
pub fn f<'a>(a: &'a mut [u32], b: &'a mut [u32]) {
    let mut s1: &mut [u32] = a;
    let mut s2: &mut [u32] = b;
    std::mem::swap(&mut s1, &mut s2);
    s1[2] = 3;
}
