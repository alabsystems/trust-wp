//@ expect: reject
//@ mechanism: the `*const str` spelling of raw_ptr_fat_to_thin_cast_read_as_operand.rs: a MIR
//@ mechanism: `PtrToPtr` cast from a `str` pointer to a thin one drops the byte length. Read as its
//@ mechanism: operand, `p1 as *const u8 != p2 as *const u8` became `p1 != p2`, which the
//@ mechanism: precondition proves; D-145 reads it as `thin(p1) != thin(p2)`.
//@ fixed-by: D-145
//@ accept-means: a metadata-dropping cast of a `str` pointer is read as the identity.
//@ WHY THE CONTRACT IS FALSE: two `str` pointers at one address with lengths 1 and 2 meet the
//@ WHY THE CONTRACT IS FALSE: precondition, and their thin casts are equal.
//@ teeth: ACCEPTED with the MIR `PtrToPtr` cast read as its operand, as at the merge base (A/B
//@ teeth: knob); the twin raw_ptr_str_fat_to_fat_cast_control.rs differs in the target alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(p1 != p2)]
#[ensures(result)]
pub fn str_thin_differs(p1: *const str, p2: *const str) -> bool {
    (p1 as *const u8) != (p2 as *const u8)
}
