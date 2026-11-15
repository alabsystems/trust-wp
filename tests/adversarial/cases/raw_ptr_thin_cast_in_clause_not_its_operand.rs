//@ expect: reject
//@ mechanism: the clause spelling of raw_ptr_fat_to_thin_cast_read_as_operand. A clause's
//@ mechanism: `p as *const u8` is read at `p`'s type by the same classifier as the body's cast: for
//@ mechanism: a `*const [u8]` it is `thin(p)`, so the postcondition does not follow from `p != q`.
//@ fixed-by: D-145
//@ accept-means: a clause's metadata-dropping cast is read as its operand.
//@ WHY THE CONTRACT IS FALSE: two slice pointers with one address and different lengths meet the
//@ WHY THE CONTRACT IS FALSE: precondition, and their thin casts are equal.
//@ teeth: before clause casts were read at all the clause was a parse error (refused); the twin
//@ teeth: raw_ptr_thin_cast_in_clause_control, whose postcondition is the congruence, verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p != q)]
#[ensures(p as *const u8 != q as *const u8)]
pub fn claims_distinct(p: *const [u8], q: *const [u8]) {}
