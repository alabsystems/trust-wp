//@ expect: verify
//@ xfail: the contract-free body is now a verification target, and `cap_clause_free_verdict`
//@ xfail: then demotes its clause-free `verified` to `unknown (partial: panic paths
//@ xfail: unchecked)`. The cap counts a call to a callee with a builtin std spec as an
//@ xfail: unaccounted panic site even though the call lane charges that spec's `requires`,
//@ xfail: and it counts an `assert!` arm the switch lane has just charged. An XPASS here is
//@ xfail: the signal that the cap learned to read what the extraction lane actually charged.
//@ mechanism: control for the s43v2 signed-overflow rejects: div/rem calls that cannot overflow.
//@ fixed-by: wp-s43 v2 (signed-overflow precondition on DIV/REM/REM_EUCLID/DIV_EUCLID)
//@ teeth: control - (-127).div_euclid(-1), MIN.rem(2) and unsigned rem_euclid must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::ops::Rem;

pub fn div_euclid_near_min_true() {
    let r = (-127i8).div_euclid(-1);
    proof_assert!(r@ == 127);
}

pub fn rem_min_by_two_true() {
    let x = i32::MIN;
    let r = x.rem(2);
    proof_assert!(r@ == 0);
}

pub fn unsigned_rem_euclid_true() {
    let x = 10u32;
    let r = x.rem_euclid(3);
    proof_assert!(r@ == 1);
}
