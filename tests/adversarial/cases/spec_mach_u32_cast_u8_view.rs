//@ expect: reject
//@ mechanism: `(a as u8)@ == a@` over `u32` (the oracle's cast is `UInt8.of_int`, which reduces
//@ mechanism: modulo 2^8) -- an arithmetic operator on machine-integer operands in spec text. D-135
//@ mechanism: item 3: in the pinned oracle it means creusot-std's logic impl, the type's bit-vector
//@ mechanism: operation, which WRAPS (`u32 + u32` is `creusot.int.UInt32$BW$.add`); a reading of it
//@ mechanism: as mathematical integer arithmetic proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = 300: `a as u8` is 44.
//@ teeth: rejected `failed` when written: trust-wp-core lowers an integer cast to Rust's `as`
//@ teeth: arithmetic (contract_parser/helpers/casts.rs), the oracle's meaning. The case pins that
//@ teeth: lowering.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((a as u8)@ == a@)]
pub fn cast_u8_view(a: u32) {}
