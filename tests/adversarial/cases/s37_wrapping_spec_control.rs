//@ expect: verify
//@ mechanism: control for s37_wrapping_spec_off_by_one — exact wrapping results must verify.
//@ fixed-by: wp-s37 607bb1f6
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn wrap_add_true() {
    let r = (-128i8).wrapping_add(-1);
    proof_assert!(r@ == 127);
}

pub fn wrap_sub_true() {
    let r = 0u8.wrapping_sub(1);
    proof_assert!(r@ == 255);
}

pub fn wrap_mul_true() {
    let r = (-3i8).wrapping_mul(50);
    proof_assert!(r@ == 106);
}

pub fn ovf_mul_true() {
    let r = (-3i8).overflowing_mul(50);
    proof_assert!(r.0@ == 106 && r.1);
}
