//@ expect: reject
//@ mechanism: a callee's `#[requires(a + 1u8 > a)]` over `u8` is owed by its caller at the call
//@ mechanism: `callee(255)` -- the precondition lane, not the clause's own lane, reads the operator.
//@ mechanism: D-135 item 3: in the pinned oracle an operator on machine-integer operands means
//@ mechanism: creusot-std's logic impl, the type's bit-vector operation, which WRAPS (`u8 + u8` is
//@ mechanism: `creusot.int.UInt8$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: a caller was credited with a call whose precondition the oracle refutes: the callee's
//@ accept-means: wrapping `+` was read as mathematical integer arithmetic where the call owes it.
//@ WHY THE CONTRACT IS FALSE: caller: at a = 255 the wrapping sum is 0, which is not above 255.
//@ also-verified: callee
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
//@ teeth: Found probing sideways from D-232.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a + 1u8 > a)]
pub fn callee(a: u8) {}

pub fn caller() {
    callee(255);
}
