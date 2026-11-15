//@ expect: reject
//@ mechanism: the `dyn` spelling of raw_ptr_unsize_array_lengths_read_as_identity: `*const u8` and
//@ mechanism: `*const u16` of one address unsized to `*const dyn Tr` carry the vtables of two
//@ mechanism: different types (their sizes differ, so no deduplication can merge them). Read as the
//@ mechanism: identity, equal thin pointers made the fat pointers equal.
//@ fixed-by: D-145
//@ accept-means: a raw-pointer unsizing to `dyn` is read as its operand.
//@ WHY THE CONTRACT IS FALSE: with `p` and `q` at one address the function reaches `a == b`, whose
//@ WHY THE CONTRACT IS FALSE: vtables differ, and returns false.
//@ teeth: ACCEPTED at the merge base.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {}
impl Tr for u8 {}
impl Tr for u16 {}

#[ensures(result)]
pub fn f(p: *const u8, q: *const u16) -> bool {
    if p != q as *const u8 {
        return true;
    }
    let a: *const dyn Tr = p;
    let b: *const dyn Tr = q;
    a == b
}
