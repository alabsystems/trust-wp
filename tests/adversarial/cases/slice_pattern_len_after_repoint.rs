//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so a switch on `PtrMetadata` of a borrow of `*a` demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee. A slice pattern (`match &*a { [_x, _y] => .. }`) switches on exactly that length, so its arms are walked after a write through `a` where the switch used to owe the fail-closed `false`.
//@ mechanism: here the slice local itself is re-pointed from a one-element slice to a two-element one through a `&mut` borrow of its own storage before the write and the match, which the length demand must refuse.
//@ accept-means: the pattern's length switch read the length of the slice `s` pointed to BEFORE `*r = b` re-pointed it, so the two-element arm looked unreachable.
//@ WHY THE CONTRACT IS FALSE: `s` is `b` (two elements) when the match runs, so `never()`, whose precondition is `false`, is called.
//@ teeth: UNVERIFIED as a gate on the own-storage rule alone: `unknown (refutation withheld)` before and after D-168, the primary lane does not keep `s` bound to `a` past the borrow. It pins the slice-pattern spelling of slice_bounds_repointed_through_borrow.rs.
//@ also-verified: never
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(false)]
fn never() {}

#[requires(a@.len() == 1 && b@.len() == 2)]
pub fn f<'a>(a: &'a mut [u32], b: &'a mut [u32]) {
    let mut s: &mut [u32] = a;
    {
        let r = &mut s;
        *r = b;
    }
    s[0] = 1;
    match &*s {
        [_x, _y] => never(),
        _ => {}
    }
}
