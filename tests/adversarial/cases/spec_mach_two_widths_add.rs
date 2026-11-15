//@ expect: reject
//@ mechanism: one clause holding `+` at `u64` and at `u8`: the width is the operator's own, not the
//@ mechanism: clause's -- an arithmetic operator on machine-integer operands in spec text. D-135
//@ mechanism: item 3: in the pinned oracle it means creusot-std's logic impl, the type's bit-vector
//@ mechanism: operation, which WRAPS (`u32 + u32` is `creusot.int.UInt32$BW$.add`); a reading of it
//@ mechanism: as mathematical integer arithmetic proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: x@ + y@ >= 256 makes the u8 sum wrap below x (x = 200, y = 100: 44);
//@ WHY THE CONTRACT IS FALSE: the u64 conjunct holds under every reading, so reading the u8 sum at
//@ WHY THE CONTRACT IS FALSE: 64 bits accepts.
//@ refused-with: applies `+` to more than one type
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x@ + y@ >= 256 && a@ <= 10 && b@ <= 10)]
#[ensures(a + b <= 20u64 && x + y >= x)]
pub fn two_widths_add(a: u64, b: u64, x: u8, y: u8) {}
