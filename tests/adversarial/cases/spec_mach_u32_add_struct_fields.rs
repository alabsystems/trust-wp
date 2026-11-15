//@ expect: reject
//@ mechanism: `s.x + s.y >= s.x` over `u32` fields -- an arithmetic operator on machine-integer
//@ mechanism: operands in spec text. D-135 item 3: in the pinned oracle it means creusot-std's
//@ mechanism: logic impl, the type's bit-vector operation, which WRAPS (`u32 + u32` is
//@ mechanism: `creusot.int.UInt32$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: s.x = u32::MAX, s.y = 1: the wrapping sum is 0.
//@ teeth: rejected `unknown (proof-trusted)` when written: ay withholds the UNSAT it computes, so
//@ teeth: the case pins the shape and its teeth are UNVERIFIED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S {
    pub x: u32,
    pub y: u32,
}

#[ensures(s.x + s.y >= s.x)]
pub fn add_struct_fields(s: S) {}
