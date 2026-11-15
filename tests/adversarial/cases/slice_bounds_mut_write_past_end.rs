//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so the bounds check of `a[i]` through `a: &mut [T]` (`PtrMetadata` of a fake raw borrow of `*a`) demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee; the fake borrow translates as the reborrow `&*a`.
//@ mechanism: here the slice has two elements and index 2 is written.
//@ accept-means: the length read by the bounds check is not the length of the slice the write goes to.
//@ WHY THE CONTRACT IS FALSE: `f(&mut [0, 0])` panics at `a[2]`.
//@ teeth: isolating twin of slice_bounds_mut_write_control.rs (identical but for `2` vs `5`); rejected before (withheld over the fail-closed `false`) and after (the bounds goal `2 < 2` is not proved).
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@.len() == 2)]
pub fn f(a: &mut [u32]) {
    a[2] = 3;
}
