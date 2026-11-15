//@ expect: reject
//@ mechanism: the const-generic spelling of raw_ptr_unsize_array_lengths_read_as_identity. A pair that
//@ mechanism: names a generic parameter prints alike in every body; its function is keyed by the
//@ mechanism: body's owner too, and `[u8; N]` and `[u8; M]` are two pairs. Read as the identity, or
//@ mechanism: as one function for every generic pair, the two fat pointers were equal.
//@ fixed-by: D-145
//@ accept-means: a generic raw-pointer unsizing is read as its operand.
//@ WHY THE CONTRACT IS FALSE: `f::<4, 8>` at one address compares a length-4 and a length-8 slice
//@ WHY THE CONTRACT IS FALSE: pointer and returns false.
//@ teeth: ACCEPTED at the merge base, and under a draft that kept the identity for generic pairs.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn f<const N: usize, const M: usize>(p: *const [u8; N], q: *const [u8; M]) -> bool {
    if p as *const u8 != q as *const u8 {
        return true;
    }
    let a: *const [u8] = p;
    let b: *const [u8] = q;
    a == b
}
