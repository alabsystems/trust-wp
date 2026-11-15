//@ expect: verify
//@ xfail: the lowered cast is Euclidean `mod`, and the driver reports the proof of this TRUE
//@ xfail: claim as `unknown (proof-trusted)`. It verified only while the parser read the cast
//@ xfail: as its operand, which is the false accept contract_cast_u8_of_u64_read_as_operand.rs
//@ xfail: closes; this is the price.
//@ mechanism: control for contract_cast_u8_of_u64_read_as_operand: the same cast, on the inputs
//@ mechanism: where it keeps its operand's value
//@ fixed-by: n/a (control; open)
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x@ < 256)]
#[ensures((x as u8)@ == x@)]
pub fn k(x: u64) {}
