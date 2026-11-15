//@ expect: verify
//@ mechanism: control for D-148: the body declares a block item, but not one named `T`, so the
//@ mechanism: written target `T` is still read as the generic parameter and the identity cast is
//@ mechanism: proved. Twin of raw_ptr_proof_assert_cast_to_generic_shadowed_by_block_alias.rs, which
//@ mechanism: names its alias `T`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn pa_same_differs<T: ?Sized>(p1: *const T, p2: *const T) {
    #[allow(dead_code)]
    type U = u8;
    if p1 != p2 {
        proof_assert!((p1 as *const T) != (p2 as *const T));
    }
}
