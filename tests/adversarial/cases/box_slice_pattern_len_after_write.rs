//@ expect: reject
//@ mechanism: a slice pointer's length is part of the pointer value, so a switch on `PtrMetadata` of a borrow of `*a` demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee. A slice pattern (`match &*a { [_x, _y] => .. }`) switches on exactly that length, so its arms are walked after a write through `a` where the switch used to owe the fail-closed `false`.
//@ mechanism: here the slice is owned through a `Box<[u32]>`, written in place and then matched, and a one-element box reaches the `never()` arm.
//@ accept-means: the arm the pattern's length selects was not charged, so `never()`'s precondition was never owed.
//@ WHY THE CONTRACT IS FALSE: `f(Box::new([0]))` writes `b[0]` and then calls `never()`, whose precondition is `false`.
//@ teeth: UNVERIFIED: rejected before and after D-168. Before, the refutation rested on the switch's own fail-closed `false` under the `len != 0` guard; after, on `never()`'s `false` under `len != 0` and `len == 1`. It pins the `Box` spelling of slice_pattern_len_after_mut_write_reachable_arm.rs.
//@ also-verified: never
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(false)]
fn never() {}

pub fn f(mut b: Box<[u32]>) {
    if b.len() == 0 {
        return;
    }
    b[0] = 1;
    match &*b {
        [_x] => never(),
        _ => {}
    }
}
