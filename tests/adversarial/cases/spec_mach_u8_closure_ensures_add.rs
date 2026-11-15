//@ expect: reject
//@ mechanism: a closure's one contract attribute `#[ensures(result + 1u8 > result)]` over a `u8`
//@ mechanism: result, read by the closure's own lane.
//@ mechanism: D-135 item 3: in the pinned oracle an operator on machine-integer operands means
//@ mechanism: creusot-std's logic impl, the type's bit-vector operation, which WRAPS (`u8 + u8` is
//@ mechanism: `creusot.int.UInt8$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: the operator in a closure postcondition was read as mathematical integer arithmetic.
//@ WHY THE CONTRACT IS FALSE: the closure returns its argument, and at 255 the wrapping sum is 0.
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
//@ teeth: Found probing sideways from D-232.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn closure_ensures_add() {
    let c = #[ensures(result + 1u8 > result)]
    |x: u8| -> u8 { x };
    let _ = c(255);
}
