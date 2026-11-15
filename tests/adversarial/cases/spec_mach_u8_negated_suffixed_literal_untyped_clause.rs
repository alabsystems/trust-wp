//@ expect: reject
//@ mechanism: `-(1u8) < 1u8` in the postcondition of a function returning `impl Sized`, whose clause
//@ mechanism: no type check reads. A minus on an integer literal is read as a negative literal, never
//@ mechanism: an operator (contract_parser::machine_arith::ContractParser::written_neg), so `-(1u8)`
//@ mechanism: is the integer -1. In the pinned oracle `1u8` is a `u8` and the minus is creusot-std's
//@ mechanism: `NegLogic` for `u8`, `UInt8$BW$.neg`, which maps 1 to 255 (D-135 item 3).
//@ accept-means: the negation of a machine-suffixed literal in a clause no type check reads was read
//@ accept-means: as mathematical negation.
//@ WHY THE CONTRACT IS FALSE: the oracle's negation of 1u8 is 255u8, which is not below 1.
//@ fixed-by: OPEN: committed RED. A minus on a literal is a negative literal only for an unsuffixed or
//@ fixed-by: `int` literal; on a machine-suffixed one it is that type's negation, read at that type or
//@ fixed-by: refused.
//@ teeth: ACCEPTED at exit 0 when written, as on the campaign base. Found probing sideways from D-232.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(-(1u8) < 1u8)]
pub fn negated_suffixed_literal(x: u8) -> impl Sized {
    x
}
