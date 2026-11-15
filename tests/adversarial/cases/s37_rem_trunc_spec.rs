//@ expect: reject
//@ mechanism: pearlite `%` on Int lowered to the EUCLIDEAN BinOp::Mod; Creusot`s Int `%` is
//@ mechanism: int.ComputerDivision.mod (truncating, sign of the dividend: -3 % 2 == -1).
//@ fixed-by: wp-s37 607bb1f6 (contract `%` -> BinOp::RemTrunc; std wrapping_mul uses rem_euclid)
//@ accept-means: a negative dividend's remainder was assumed non-negative (Euclidean).
//@ WHY THE CONTRACT IS FALSE: x = -1 gives x % 2 == -1 < 0.
//@ teeth: before 607bb1f6 ay returned unsat (withheld only by strict certification), measured
//@ teeth: on this spec-only shape, where `%` lowered to the Euclidean remainder.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x@ < 0 && x@ > -100)]
#[ensures(x@ % 2 >= 0)]
pub fn l_spec_false(x: i32) {}
