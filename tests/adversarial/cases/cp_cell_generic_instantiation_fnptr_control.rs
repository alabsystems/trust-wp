//@ expect: verify
//@ mechanism: over-refusal control for cp_cell_generic_instantiation_fnptr — the SAME fn-pointer
//@ mechanism: coercion of a local generic, instantiated at an ordinary (Freeze, drop-free) type.
//@ mechanism: Following the pointer must add the obligation only where the instantiation carries
//@ mechanism: one; a generic reached through a pointer is not by itself a refusal.
//@ fixed-by: s44 v3 (wp-s44)
//@ accept-means: n/a (control) — the contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == *x)]
pub fn gen_id<T: Copy>(x: &T) -> T {
    *x
}

#[ensures(result == 7u8)]
pub fn via_ptr() -> u8 {
    let f: fn(&u8) -> u8 = gen_id::<u8>;
    f(&7u8)
}
