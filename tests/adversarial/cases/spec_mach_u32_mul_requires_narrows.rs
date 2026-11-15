//@ expect: reject
//@ mechanism: `#[requires(a * 2u32 == 2u32)]`: read mathematically it pins a = 1 -- an arithmetic
//@ mechanism: operator on machine-integer operands in spec text. D-135 item 3: in the pinned oracle
//@ mechanism: it means creusot-std's logic impl, the type's bit-vector operation, which WRAPS (`u32
//@ mechanism: + u32` is `creusot.int.UInt32$BW$.add`); a reading of it as mathematical integer
//@ mechanism: arithmetic proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = 2^31 + 1 meets the precondition (the wrapping product is 2) and
//@ WHY THE CONTRACT IS FALSE: is not 1.
//@ teeth: rejected `unknown (proof-trusted)` when written: ay withholds the UNSAT it computes, so
//@ teeth: the case pins the shape and its teeth are UNVERIFIED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a * 2u32 == 2u32)]
#[ensures(a == 1u32)]
pub fn mul_requires_narrows(a: u32) {}
