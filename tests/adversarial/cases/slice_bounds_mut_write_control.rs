//@ expect: verify
//@ mechanism: a slice pointer's length is part of the pointer value, so the bounds check of `a[i]` through `a: &mut [T]` (`PtrMetadata` of a fake raw borrow of `*a`) demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee; the fake borrow translates as the reborrow `&*a`.
//@ mechanism: control: a write in bounds of a five-element slice. Twin of slice_bounds_mut_write_past_end.rs.
//@ accept-means: n/a (control)
//@ teeth: without the length demand the check read `a`, which is `&mut`-typed and written through, so its obligation was the fail-closed `false` and this TRUE contract was `unknown (refutation withheld)`.
//@ fixed-by: D-168 — a bounds check through a `&mut [T]` reads only the pointer's length
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@.len() == 5)]
#[ensures((^a)[2]@ == 3)]
pub fn f(a: &mut [u32]) {
    a[2] = 3;
}
