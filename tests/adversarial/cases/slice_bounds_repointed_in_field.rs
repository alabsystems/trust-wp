//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so the bounds check of `a[i]` through `a: &mut [T]` (`PtrMetadata` of a fake raw borrow of `*a`) demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee; the fake borrow translates as the reborrow `&*a`.
//@ mechanism: here the slice pointer lives in a struct field that is re-assigned; the length demand follows only a place that is exactly `*p`, so the field read is demanded whole.
//@ accept-means: the bounds check read the length of the slice the field held first.
//@ WHY THE CONTRACT IS FALSE: `h.s` is `b` (one element) when `h.s[2]` runs, so every call panics.
//@ teeth: control pair for the def-use walk, not a regression test of a hole: rejected before and after (the fail-closed `false`).
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Holder<'a> {
    s: &'a mut [u32],
}

#[requires(a@.len() == 3 && b@.len() == 1)]
pub fn f<'a>(a: &'a mut [u32], b: &'a mut [u32]) {
    let mut h = Holder { s: a };
    h.s = b;
    h.s[2] = 3;
}
