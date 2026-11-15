//@ expect: reject
//@ mechanism: pearlite `%` on Int lowered to the EUCLIDEAN BinOp::Mod; Creusot`s Int `%` is
//@ mechanism: int.ComputerDivision.mod (truncating, sign of the dividend: -3 % 2 == -1).
//@ fixed-by: wp-s37 607bb1f6 (contract `%` -> BinOp::RemTrunc; std wrapping_mul uses rem_euclid)
//@ accept-means: the logic % is Euclidean again - a claim false under Creusot semantics verifies.
//@ WHY THE CONTRACTS ARE FALSE: -3 % 2 == -1 and (-7) % 3 == -1 in Creusot, not 1 / 2.
//@ teeth: before 607bb1f6 l_rem_false verified (base_exit_code=0), measured under an
//@ teeth: audit of Creusot's Int `%` semantics.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn l_rem_false() {
    proof_assert!(-3 % 2 == 1);
}

pub fn l_rem_false2() {
    proof_assert!((-7) % 3 == 2);
}
