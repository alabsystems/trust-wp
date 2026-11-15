//@ expect: reject
//@ mechanism: constant-argument Rem::rem / Div::div trait calls in proof_assert. The rem result
//@ mechanism: was pinned to 1 (closure shortcut, see s43_closure_shortcut_receiver), which looked
//@ mechanism: like the Euclidean remainder; div must be truncating (DivTrunc), not Euclidean.
//@ fixed-by: wp-s43 afef1166 + the s43 integer Div/Rem spec commit (truncating REM spec)
//@ accept-means: rem/div on machine integers is modelled Euclidean (or pinned) again.
//@ WHY THE CONTRACTS ARE FALSE: Rust truncates: (-7) % 2 == -1 and (-7) / 2 == -3.
//@ teeth: rem_call_false (s37 review probe r5b) verified with base_exit_code=0 on wp-campaign
//@ teeth: 033943a2, measured 2026-09-13; the other rem/div shapes are regression guards.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::ops::{Div, Rem, RemAssign};

pub fn rem_call_false() {
    let r = (-7i32).rem(2);
    proof_assert!(r@ == 1);
}

pub fn rem_op_assign_false() {
    let mut r = -7i32;
    r %= 2;
    proof_assert!(r@ == 1);
}

pub fn rem_assign_call_false() {
    let mut r = -7i32;
    r.rem_assign(2);
    proof_assert!(r@ == 1);
}

pub fn rem_ref_i64_false() {
    let a = -7i64;
    let r = (&a).rem(2);
    proof_assert!(r@ == 1);
}

pub fn rem_ref_ref_i64_false() {
    let a = -7i64;
    let b = 2i64;
    let r = (&a).rem(&b);
    proof_assert!(r@ == 1);
}

pub fn div_call_false() {
    let r = (-7i32).div(2);
    proof_assert!(r@ == -4);
}

pub fn div_op_false() {
    let a = -7i32;
    let r = a / 2;
    proof_assert!(r@ == -4);
}

#[requires(x@ == -7)]
#[ensures(result@ == -4)]
pub fn div_contract_false(x: i32) -> i32 {
    x.div(2)
}

#[requires(x@ == -7)]
#[ensures(result@ == 1)]
pub fn rem_contract_false(x: i32) -> i32 {
    x.rem(2)
}

pub fn euclid_swapped_false() {
    let r = (-7i32).rem_euclid(2);
    let q = (-7i32).div_euclid(2);
    proof_assert!(r@ == -1 || q@ == -3);
}
