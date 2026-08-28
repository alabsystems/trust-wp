//@ expect: reject
//@ mechanism: sibling CARRIER fusion inside one tuple payload — both elements sharing a single
//@ mechanism: prophecy carrier (or a single borrow id) would make `^a == ^b` provable
//@ fixed-by: n/a (this is the P3 risk the Fix B M2 lowering must NOT introduce)
//@ accept-means: the two `&mut` elements of one `Option<(&mut T, &mut T)>` payload were lowered
//@ accept-means: onto the SAME record carrier, or onto carriers whose `id` components were
//@ accept-means: conflated. `mk` congruence then forces the two distinct borrows equal — the
//@ accept-means: bug/869 id-distinctness hole, relocated into a tuple payload. Every multi-borrow
//@ accept-means: postcondition in the corpus becomes untrustworthy.
//@
//@ WHY THE CONTRACT IS FALSE: `a` and `b` borrow DIFFERENT locals; the caller may write 1 through
//@ one and 2 through the other, so their final values need not agree.
//@ teeth: VERIFIED PRE/POST — rejected on the pre-M2 build (05e6373) and on the M2 build. This is
//@ teeth: the standing separability gate for the new carrier-tuple lowering; its encoder-level
//@ teeth: sibling is the M0 pin `m0_option_mutref_distinct_ids_keep_carriers_separable`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(match result {
    Some((a, b)) => ^a == ^b,
    None => true,
})]
pub fn pair_fused<'a>(x: &'a mut i32, y: &'a mut i32) -> Option<(&'a mut i32, &'a mut i32)> {
    Some((x, y))
}

// The refutation, in executable Rust: `^a` is 1 and `^b` is 2.
pub fn caller() {
    let mut v = 0i32;
    let mut w = 0i32;
    if let Some((a, b)) = pair_fused(&mut v, &mut w) {
        *a = 1;
        *b = 2;
    }
}
