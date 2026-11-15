//@ expect: reject
//@ mechanism: `a + b > a` over `i8` inside an `if` of the clause -- an arithmetic operator on
//@ mechanism: machine-integer operands in spec text. D-135 item 3: in the pinned oracle it means
//@ mechanism: creusot-std's logic impl, the type's bit-vector operation, which WRAPS (`u32 + u32`
//@ mechanism: is `creusot.int.UInt32$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: the operator was read as mathematical integer arithmetic, not as the oracle's
//@ accept-means: wrapping bit-vector operation.
//@ WHY THE CONTRACT IS FALSE: a = 127, b = 1: the then-branch's wrapping sum is -128.
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(b@ > 0)]
#[ensures(if a@ >= 0 { a + b > a } else { true })]
pub fn add_under_if(a: i8, b: i8) {}
