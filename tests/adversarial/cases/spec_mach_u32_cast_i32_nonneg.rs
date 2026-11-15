//@ expect: reject
//@ mechanism: `(a as i32)@ >= 0` over `u32` (the oracle's cast reinterprets in two's complement) --
//@ mechanism: an arithmetic operator on machine-integer operands in spec text. D-135 item 3: in the
//@ mechanism: pinned oracle it means creusot-std's logic impl, the type's bit-vector operation,
//@ mechanism: which WRAPS (`u32 + u32` is `creusot.int.UInt32$BW$.add`); a reading of it as
//@ mechanism: mathematical integer arithmetic proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = 2^31: `a as i32` is i32::MIN.
//@ teeth: rejected `failed` when written: trust-wp-core lowers an integer cast to Rust's `as`
//@ teeth: arithmetic (contract_parser/helpers/casts.rs), the oracle's meaning. The case pins that
//@ teeth: lowering.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((a as i32)@ >= 0)]
pub fn cast_i32_nonneg(a: u32) {}
