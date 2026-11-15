//@ expect: verify
//@ mechanism: pearlite `%` on Int lowered to the EUCLIDEAN BinOp::Mod; Creusot`s Int `%` is
//@ mechanism: int.ComputerDivision.mod (truncating, sign of the dividend: -3 % 2 == -1).
//@ fixed-by: wp-s37 607bb1f6 (contract `%` -> BinOp::RemTrunc; std wrapping_mul uses rem_euclid)
//@ teeth: control — before 607bb1f6 this TRUE program FAILED (spec Euclidean vs body truncating).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x@ < 0 && x@ > -100)]
#[ensures(result@ == x@ % 2)]
pub fn s4_true(x: i32) -> i32 {
    x % 2
}
