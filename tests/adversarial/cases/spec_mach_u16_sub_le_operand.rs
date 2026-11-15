//@ expect: reject
//@ mechanism: `a - b <= a` over `u16` -- an arithmetic operator on machine-integer operands in spec
//@ mechanism: text. D-135 item 3: in the pinned oracle it means creusot-std's logic impl, the
//@ mechanism: type's bit-vector operation, which WRAPS (`u32 + u32` is
//@ mechanism: `creusot.int.UInt32$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = 0, b = 1: the wrapping difference is 65535, above a.
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(a - b <= a)]
pub fn sub_le_operand(a: u16, b: u16) {}
