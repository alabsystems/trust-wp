//@ expect: reject
//@ mechanism: `{ let y = x + 1u8; y > x }` over `u8`: the wrapping operator is the value of a clause
//@ mechanism: `let` binding, which the comparison reads by name.
//@ mechanism: D-135 item 3: in the pinned oracle an operator on machine-integer operands means
//@ mechanism: creusot-std's logic impl, the type's bit-vector operation, which WRAPS (`u8 + u8` is
//@ mechanism: `creusot.int.UInt8$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: the operator bound by a clause `let` was read as mathematical integer arithmetic.
//@ WHY THE CONTRACT IS FALSE: x = 255: y is 0, which is not above 255.
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
//@ teeth: Found probing sideways from D-232.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures({ let y = x + 1u8; y > x })]
pub fn add_in_let_binding(x: u8) {}
