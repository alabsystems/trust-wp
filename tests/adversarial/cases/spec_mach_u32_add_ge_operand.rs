//@ expect: reject
//@ mechanism: `a + b >= a` over `u32`, an empty body (D-135 item 3's named probe) -- an arithmetic
//@ mechanism: operator on machine-integer operands in spec text. D-135 item 3: in the pinned oracle
//@ mechanism: it means creusot-std's logic impl, the type's bit-vector operation, which WRAPS (`u32
//@ mechanism: + u32` is `creusot.int.UInt32$BW$.add`); a reading of it as mathematical integer
//@ mechanism: arithmetic proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = u32::MAX, b = 1: the wrapping sum is 0, below a.
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(a + b >= a)]
pub fn add_ge_operand(a: u32, b: u32) {}
