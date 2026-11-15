//@ expect: reject
//@ mechanism: `(a + b)@ == a@ + b@` over `u32`: a machine sum under `@` beside an `Int` sum -- an
//@ mechanism: arithmetic operator on machine-integer operands in spec text. D-135 item 3: in the
//@ mechanism: pinned oracle it means creusot-std's logic impl, the type's bit-vector operation,
//@ mechanism: which WRAPS (`u32 + u32` is `creusot.int.UInt32$BW$.add`); a reading of it as
//@ mechanism: mathematical integer arithmetic proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = u32::MAX, b = 1: `(a + b)@` is 0 and `a@ + b@` is 2^32.
//@ refused-with: applies `+` to more than one type
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((a + b)@ == a@ + b@)]
pub fn add_view_of_sum(a: u32, b: u32) {}
