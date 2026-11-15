//@ expect: reject
//@ mechanism: `a >> 1i32 >= 0i32` over `i32` under `#[bitwise_proof]`: the oracle's signed `shr` is
//@ mechanism: `asr_bv`, an arithmetic shift -- an arithmetic operator on machine-integer operands
//@ mechanism: in spec text. D-135 item 3: in the pinned oracle it means creusot-std's logic impl,
//@ mechanism: the type's bit-vector operation, which WRAPS (`u32 + u32` is
//@ mechanism: `creusot.int.UInt32$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = -2: the arithmetic shift is -1, below 0.
//@ fn-failed: shr_nonneg
//@ teeth: rejected `failed` when written, so the case pins the shape and its teeth are UNVERIFIED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[bitwise_proof]
#[ensures(a >> 1i32 >= 0i32)]
pub fn shr_nonneg(a: i32) {}
