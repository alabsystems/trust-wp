//@ expect: reject
//@ mechanism: std wrapping_add/wrapping_sub/wrapping_mul specs reduce modulo 2^n; wrapping_mul
//@ mechanism: must use the EUCLIDEAN rem_euclid (dividend self*rhs - MIN can be negative).
//@ fixed-by: wp-s37 607bb1f6
//@ accept-means: a wrapping spec lost its exact value (off-by-one results accepted).
//@ WHY THE CONTRACTS ARE FALSE: -128i8 wrapping_add -1 == 127; 0u8 wrapping_sub 1 == 255;
//@ WHY THE CONTRACTS ARE FALSE: -3i8 wrapping_mul 50 == -150 + 256 == 106.
//@ teeth: UNVERIFIED (honest) — guards the rem_euclid rewrite; a truncating reduction in
//@ teeth: wrapping_mul would make its result -150 % 256 - 128 == -22 (inconsistent with 106).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn wrap_add_false() {
    let r = (-128i8).wrapping_add(-1);
    proof_assert!(r@ == 126);
}

pub fn wrap_sub_false() {
    let r = 0u8.wrapping_sub(1);
    proof_assert!(r@ == 254);
}

pub fn wrap_mul_false() {
    let r = (-3i8).wrapping_mul(50);
    proof_assert!(r@ == 105);
}

pub fn ovf_mul_false() {
    let r = (-3i8).overflowing_mul(50);
    proof_assert!(r.0@ == 105);
}
