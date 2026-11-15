//@ expect: verify
//@ mechanism: control for raw_ptr_fat_to_thin_cast_read_as_operand: `thin` is a function, so equal
//@ mechanism: fat pointers have equal thin casts (congruence), which is all this claims.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p1 == p2)]
#[ensures(result)]
pub fn thin_equal(p1: *const [u8], p2: *const [u8]) -> bool {
    (p1 as *const u8) == (p2 as *const u8)
}
