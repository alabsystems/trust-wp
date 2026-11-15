//@ expect: verify
//@ xfail: the lowered cast is Euclidean `mod`, and the driver reports the proof of this TRUE
//@ xfail: claim as `unknown (proof-trusted)`. While the parser read the cast as its operand it
//@ xfail: was FAILED instead (`y@ >= 0` over an i64).
//@ mechanism: control for contract_cast_u64_of_i64_read_as_operand: an unsigned cast is never
//@ mechanism: negative
//@ fixed-by: n/a (control; open)
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((y as u64)@ >= 0)]
pub fn m(y: i64) {}
