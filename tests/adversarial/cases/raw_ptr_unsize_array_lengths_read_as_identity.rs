//@ expect: reject
//@ mechanism: unsizing a raw pointer (`PointerCoercion::Unsize`) ADDS metadata: `*const [u8; 4]`
//@ mechanism: and `*const [u8; 8]` of one address unsized to `*const [u8]` carry lengths 4 and 8, so
//@ mechanism: they differ. The MIR translation read every unsizing as its operand, as for a
//@ mechanism: reference, so both were `p` and the comparison was proved true.
//@ fixed-by: D-145
//@ accept-means: a raw-pointer unsizing is read as its operand, and two fat pointers that differ
//@ accept-means: only in their length are proved equal.
//@ WHY THE CONTRACT IS FALSE: `same_fat(p)` compares a length-4 and a length-8 slice pointer at one
//@ WHY THE CONTRACT IS FALSE: address and returns false.
//@ teeth: ACCEPTED (`same_fat verified`) at the merge base, before raw-pointer unsizing was read as
//@ teeth: its type pair's function; the twin raw_ptr_unsize_same_length_control verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn same_fat(p: *const u8) -> bool {
    let a: *const [u8] = p as *const [u8; 4];
    let b: *const [u8] = p as *const [u8; 8];
    a == b
}
