//@ expect: verify
//@ xfail: the contract-free body is now a verification target, and `cap_clause_free_verdict`
//@ xfail: then demotes its clause-free `verified` to `unknown (partial: panic paths
//@ xfail: unchecked)`. The cap counts a call to a callee with a builtin std spec as an
//@ xfail: unaccounted panic site even though the call lane charges that spec's `requires`,
//@ xfail: and it counts an `assert!` arm the switch lane has just charged. An XPASS here is
//@ xfail: the signal that the cap learned to read what the extraction lane actually charged.
//@ mechanism: constant-argument Rem::rem / Div::div / rem_euclid / div_euclid on machine integers.
//@ fixed-by: wp-s43 integer Div/Rem spec commit (REM, REM_EUCLID, DIV_EUCLID specs)
//@ teeth: control for s43_rem_div_trait_call - the Rust (truncating / Euclidean) answers verify;
//@ teeth: rem_call_true, u_rem_call_true and the euclid pair did NOT verify on wp-campaign 033943a2.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::ops::{Div, Rem};

pub fn rem_call_true() {
    let r = (-7i32).rem(2);
    proof_assert!(r@ == -1);
}

pub fn div_call_true() {
    let r = (-7i32).div(2);
    proof_assert!(r@ == -3);
}

pub fn u_rem_call_true() {
    let r = 7u32.rem(3);
    proof_assert!(r@ == 1);
}

pub fn rem_euclid_true() {
    let r = (-7i32).rem_euclid(2);
    proof_assert!(r@ == 1);
}

pub fn div_euclid_true() {
    let r = (-7i32).div_euclid(2);
    proof_assert!(r@ == -4);
}

pub fn div_op_true() {
    let a = -7i32;
    let r = a / 2;
    proof_assert!(r@ == -3);
}

pub fn int_div_logic_true() {
    proof_assert!((-7) / 2 == -3);
}
