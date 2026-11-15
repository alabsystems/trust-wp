//@ expect: reject
//@ mechanism: the `Box` spelling of raw_ptr_fat_to_thin_cast_read_as_operand: the cast's operand is a
//@ mechanism: field behind a `Box` deref, whose type the classifier follows like a reference's, so
//@ mechanism: the metadata-dropping cast is `thin`, not its operand.
//@ fixed-by: D-145
//@ accept-means: a metadata-dropping cast of a boxed field is read as the identity.
//@ WHY THE CONTRACT IS FALSE: two slice pointers with one address and different lengths meet the
//@ WHY THE CONTRACT IS FALSE: precondition, and their thin casts are equal.
//@ teeth: ACCEPTED with the MIR cast read as its operand, as at the merge base (probe pK-base);
//@ teeth: the twin raw_ptr_box_field_thin_cast_control verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub p: *const [u8],
    pub q: *const [u8],
}

#[requires(s.p != s.q)]
#[ensures(result)]
pub fn f(s: Box<S>) -> bool {
    s.p as *const u8 != s.q as *const u8
}
