//@ expect: reject
//@ mechanism: a `#[logic]` function's own `#[ensures(result >= a)]` over a body `a + b` on `u32` --
//@ mechanism: an arithmetic operator on machine-integer operands in spec text. D-135 item 3: in the
//@ mechanism: pinned oracle it means creusot-std's logic impl, the type's bit-vector operation,
//@ mechanism: which WRAPS (`u32 + u32` is `creusot.int.UInt32$BW$.add`); a reading of it as
//@ mechanism: mathematical integer arithmetic proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = u32::MAX, b = 1: the body's wrapping sum is 0, below a.
//@ verdict: error
//@ refused-with: add postcondition FAILED (logic postcondition)
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
#[requires(b@ >= 0)]
#[ensures(result >= a)]
pub fn add(a: u32, b: u32) -> u32 {
    a + b
}
