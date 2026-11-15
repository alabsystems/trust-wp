//@ expect: reject
//@ mechanism: `v + 1u8 > v` over `u8` inside a `match` arm of the clause, whose pattern binds the
//@ mechanism: operand `v`: the arm is read under the match's binder.
//@ mechanism: D-135 item 3: in the pinned oracle an operator on machine-integer operands means
//@ mechanism: creusot-std's logic impl, the type's bit-vector operation, which WRAPS (`u8 + u8` is
//@ mechanism: `creusot.int.UInt8$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: the operator in a match arm was read as mathematical integer arithmetic.
//@ WHY THE CONTRACT IS FALSE: o = Some(255): the wrapping sum is 0, which is not above 255.
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
//@ teeth: Found probing sideways from D-232.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(match o { Some(v) => v + 1u8 > v, None => true })]
pub fn add_in_match_arm(o: Option<u8>) {}
