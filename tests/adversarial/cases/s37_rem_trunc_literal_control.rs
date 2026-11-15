//@ expect: verify
//@ mechanism: pearlite `%` on Int lowered to the EUCLIDEAN BinOp::Mod; Creusot`s Int `%` is
//@ mechanism: int.ComputerDivision.mod (truncating, sign of the dividend: -3 % 2 == -1).
//@ fixed-by: wp-s37 607bb1f6 (contract `%` -> BinOp::RemTrunc; std wrapping_mul uses rem_euclid)
//@ teeth: control for s37_rem_trunc_literal — the Creusot (truncating) answers must verify.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn l_rem_true() {
    proof_assert!(-3 % 2 == -1);
}

pub fn l_rem_true2() {
    proof_assert!((-7) % 3 == -1);
}

pub fn l_rem_true3() {
    proof_assert!(7 % -3 == 1);
}

pub fn l_euclid_true() {
    proof_assert!((-3).rem_euclid(2) == 1);
}
