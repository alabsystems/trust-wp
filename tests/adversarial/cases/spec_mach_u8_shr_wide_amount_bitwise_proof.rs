//@ expect: reject
//@ mechanism: `a >> 256u32 == 0u8` over `u8` under `#[bitwise_proof]`: the oracle recasts the shift
//@ mechanism: amount to `u8`, so 256 becomes 0 -- an arithmetic operator on machine-integer
//@ mechanism: operands in spec text. D-135 item 3: in the pinned oracle it means creusot-std's
//@ mechanism: logic impl, the type's bit-vector operation, which WRAPS (`u32 + u32` is
//@ mechanism: `creusot.int.UInt32$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = 1: the amount 256 recasts to 0 and `a >> 0` is 1.
//@ fn-failed: shr_wide_amount
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[bitwise_proof]
#[ensures(a >> 256u32 == 0u8)]
pub fn shr_wide_amount(a: u8) {}
