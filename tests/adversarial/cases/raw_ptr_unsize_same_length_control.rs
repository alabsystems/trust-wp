//@ expect: verify
//@ mechanism: control for raw_ptr_unsize_array_lengths_read_as_identity: one type pair is one
//@ mechanism: function, so two unsizings of one array pointer are equal (congruence).
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn same_fat(p: *const [u8; 4]) -> bool {
    let a: *const [u8] = p;
    let b: *const [u8] = p;
    a == b
}
