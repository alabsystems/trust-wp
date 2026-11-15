//@ expect: verify
//@ mechanism: twin of raw_ptr_proof_assert_cast_to_generic_shadowed_by_block_alias.rs without the
//@ mechanism: alias: `*const T as *const T` is the identity, so the assertion is true.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn pa_same_differs<T: ?Sized>(p1: *const T, p2: *const T) {
    if p1 != p2 {
        proof_assert!((p1 as *const T) != (p2 as *const T));
    }
}
