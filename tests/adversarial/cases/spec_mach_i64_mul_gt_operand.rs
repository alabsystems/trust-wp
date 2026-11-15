//@ expect: reject
//@ mechanism: `a * 2i64 > a` over `i64` with `a@ > 0` -- an arithmetic operator on machine-
//@ mechanism: integer operands in spec text. D-135 item 3: in the pinned oracle it means creusot-
//@ mechanism: std's logic impl, the type's bit-vector operation, which WRAPS (`u32 + u32` is
//@ mechanism: `creusot.int.UInt32$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = 2^62: the wrapping product is i64::MIN, below a.
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a@ > 0)]
#[ensures(a * 2i64 > a)]
pub fn mul_gt_operand(a: i64) {}
