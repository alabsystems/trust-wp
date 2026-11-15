//@ expect: verify
//@ mechanism: twin of raw_ptr_str_fat_to_thin_cast_read_as_operand.rs: `*const str as *const [u8]`
//@ mechanism: keeps the address and the length, so it is the identity and the contract is true.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(p1 != p2)]
#[ensures(result)]
pub fn str_fat_differs(p1: *const str, p2: *const str) -> bool {
    (p1 as *const [u8]) != (p2 as *const [u8])
}
