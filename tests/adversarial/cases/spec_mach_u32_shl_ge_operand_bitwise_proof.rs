//@ expect: reject
//@ mechanism: `a << 1u32 >= a` over `u32` under `#[bitwise_proof]`, the lane that encodes shifts
//@ mechanism: natively -- an arithmetic operator on machine-integer operands in spec text. D-135
//@ mechanism: item 3: in the pinned oracle it means creusot-std's logic impl, the type's bit-vector
//@ mechanism: operation, which WRAPS (`u32 + u32` is `creusot.int.UInt32$BW$.add`); a reading of it
//@ mechanism: as mathematical integer arithmetic proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = 2^31: `lsl_bv` drops the top bit and the shifted value is 0,
//@ WHY THE CONTRACT IS FALSE: below a.
//@ fn-failed: shl_ge_operand
//@ teeth: rejected `unknown` when written, so the case pins the shape and its teeth are
//@ teeth: UNVERIFIED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[bitwise_proof]
#[ensures(a << 1u32 >= a)]
pub fn shl_ge_operand(a: u32) {}
