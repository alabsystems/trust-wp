//@ expect: reject
//@ mechanism: the converse direction of raw_ptr_fat_to_thin_cast_read_as_operand: with the cast read
//@ mechanism: as its operand, equal thin casts made the fat pointers equal, so the branch that
//@ mechanism: compares the fat pointers was proved to return true.
//@ fixed-by: D-145
//@ accept-means: equal thin casts are read as equal fat pointers.
//@ WHY THE CONTRACT IS FALSE: `same(slice_from_raw_parts(a, 1), slice_from_raw_parts(a, 2))` takes the
//@ WHY THE CONTRACT IS FALSE: first branch (the thin casts are equal) and returns `p == q`, false.
//@ teeth: ACCEPTED (`same verified`) before the cast was classified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn same(p: *const [u8], q: *const [u8]) -> bool {
    let a = p as *const u8;
    let b = q as *const u8;
    if a == b { p == q } else { true }
}
