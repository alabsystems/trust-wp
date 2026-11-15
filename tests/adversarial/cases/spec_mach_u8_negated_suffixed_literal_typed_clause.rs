//@ expect: reject
//@ mechanism: `-(1u8) < 1u8` in a postcondition the type-check vehicle reads. Both sides of D-232's
//@ mechanism: count read a minus on an integer literal as a negative literal, never an operator: the
//@ mechanism: driver skips a `__spec_tc` negation whose argument is a literal
//@ mechanism: (callbacks::spec_arith::OperatorCollector::record) and the parser builds the integer -1
//@ mechanism: (contract_parser::machine_arith::ContractParser::written_neg), so the counts agree and
//@ mechanism: nothing is refused. In the pinned oracle `1u8` is a `u8` and the minus is creusot-std's
//@ mechanism: `NegLogic` for `u8`, `UInt8$BW$.neg`, which maps 1 to 255 (D-135 item 3). A negative
//@ mechanism: literal agrees with the oracle's negation on a signed type; on an unsigned one it does not.
//@ accept-means: the negation of an unsigned-suffixed literal in a typed clause was read as
//@ accept-means: mathematical negation.
//@ WHY THE CONTRACT IS FALSE: the oracle's negation of 1u8 is 255u8, which is not below 1.
//@ fixed-by: OPEN: committed RED. The driver must record a negation of a literal whose type is an
//@ fixed-by: unsigned machine integer as an operator of that type, so the parse that builds no
//@ fixed-by: operator for it is refused by the count, or read it as the type's wrapping negation.
//@ teeth: ACCEPTED at exit 0 when written, as on the campaign base. Found probing sideways from D-232.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(-(1u8) < 1u8)]
pub fn negated_suffixed_literal(x: u8) {}
