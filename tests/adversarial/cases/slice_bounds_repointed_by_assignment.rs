//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so the bounds check of `a[i]` through `a: &mut [T]` (`PtrMetadata` of a fake raw borrow of `*a`) demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee; the fake borrow translates as the reborrow `&*a`.
//@ mechanism: here the slice local is re-assigned directly between two writes, and a `mut` parameter is re-assigned the same way.
//@ accept-means: the second bounds check read the length of the slice assigned first.
//@ WHY THE CONTRACT IS FALSE: `s` is `b` (one element) when `s[2] = 4` runs, so every call panics.
//@ teeth: control pair for the def-use walk, not a regression test of a hole: rejected before and after.
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@.len() == 5 && b@.len() == 1)]
pub fn f<'a>(a: &'a mut [u32], b: &'a mut [u32]) {
    let mut s: &mut [u32] = a;
    s[2] = 3;
    s = b;
    s[2] = 4;
}
