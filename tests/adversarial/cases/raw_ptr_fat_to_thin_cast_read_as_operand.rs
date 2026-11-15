//@ expect: reject
//@ mechanism: a cast from a fat raw pointer to a thin one drops the metadata. Two slice pointers
//@ mechanism: that differ only in length are different and their thin casts are EQUAL. The MIR
//@ mechanism: translation read every `PtrToPtr` cast as its operand, so `p1 as *const u8 !=
//@ mechanism: p2 as *const u8` became `p1 != p2` and the precondition proved it.
//@ fixed-by: D-145
//@ accept-means: a metadata-dropping cast is read as the identity, and the thin casts of two
//@ accept-means: pointers that differ only in their metadata are proved different.
//@ WHY THE CONTRACT IS FALSE: `thin_differs(slice_from_raw_parts(a, 1), slice_from_raw_parts(a, 2))`
//@ WHY THE CONTRACT IS FALSE: meets the precondition (the lengths differ) and returns false.
//@ teeth: ACCEPTED (`thin_differs verified`) before the cast was classified; the twin
//@ teeth: raw_ptr_fat_to_thin_cast_equal_operands_control verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p1 != p2)]
#[ensures(result)]
pub fn thin_differs(p1: *const [u8], p2: *const [u8]) -> bool {
    (p1 as *const u8) != (p2 as *const u8)
}
