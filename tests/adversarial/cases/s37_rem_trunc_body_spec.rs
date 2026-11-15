//@ expect: reject
//@ mechanism: pearlite `%` on Int lowered to the EUCLIDEAN BinOp::Mod; Creusot`s Int `%` is
//@ mechanism: int.ComputerDivision.mod (truncating, sign of the dividend: -3 % 2 == -1).
//@ fixed-by: wp-s37 607bb1f6 (contract `%` -> BinOp::RemTrunc; std wrapping_mul uses rem_euclid)
//@ accept-means: body % and spec % disagree in sign, or the spec % is Euclidean.
//@ WHY THE CONTRACT IS FALSE: x = -1 returns -1, and -(x@ % 2) == 1.
//@ teeth: before 607bb1f6 this errored rather than failing; accept would need sign confusion.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x@ < 0 && x@ > -100)]
#[ensures(result@ == -(x@ % 2))]
pub fn s5_false(x: i32) -> i32 {
    x % 2
}
