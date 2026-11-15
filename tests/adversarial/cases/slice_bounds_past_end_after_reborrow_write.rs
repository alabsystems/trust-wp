//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so the bounds check of `a[i]` through `a: &mut [T]` (`PtrMetadata` of a fake raw borrow of `*a`) demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee; the fake borrow translates as the reborrow `&*a`.
//@ mechanism: here a first write goes through a reborrow `r = &mut *a`, which borrows the pointee and leaves the length demand free, and the second write is past the end.
//@ accept-means: the reborrow's write was taken to change the length, or the bounds check read another slice.
//@ WHY THE CONTRACT IS FALSE: `a` has five elements and `a[5]` panics on every call.
//@ teeth: control pair for the length demand, not a regression test of a hole: rejected before and after.
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@.len() == 5)]
pub fn f(a: &mut [u32]) {
    let r = &mut *a;
    r[0] = 1;
    a[5] = 3;
}
