//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so the bounds check of `a[i]` through `a: &mut [T]` (`PtrMetadata` of a fake raw borrow of `*a`) demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee; the fake borrow translates as the reborrow `&*a`.
//@ mechanism: here two slice locals trade pointers inside a loop through `std::mem::swap` of their own storage, and the check's condition joins the path after the loop: a stale length would make the path fact `2 < 1` and the later goal vacuous.
//@ accept-means: `never()`'s precondition was discharged by a false path fact about a stale length.
//@ WHY THE CONTRACT IS FALSE: `s` is `b` (three elements) after the loop, `s[2]` succeeds and `never()` is called, whose precondition is `false`.
//@ teeth: control pair for the same-term argument of D-168 in a loop, not a regression test of a hole: rejected before and after.
//@ also-verified: never
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(false)]
fn never() {}

#[requires(a@.len() == 1 && b@.len() == 3)]
pub fn f<'a>(a: &'a mut [u32], b: &'a mut [u32]) {
    let mut s: &mut [u32] = a;
    let mut t: &mut [u32] = b;
    let mut i = 0;
    while i < 1 {
        std::mem::swap(&mut s, &mut t);
        i += 1;
    }
    s[2] = 7;
    never();
}
