//@ expect: verify
//@ mechanism: control for spec_mach_u32_shl_ge_operand: a precondition keeps the top bit clear
//@ WHY THE CONTRACT IS TRUE: a < 2^31, so `a << 1` loses no bit and is 2a >= a.
//@ xfail: the oracle's `<<` by a literal is a product reduced by a Euclidean `mod`, and ay
//@ xfail: withholds the UNSAT it computes (`proof-trusted`).
//@ xfail-verdict: unknown
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a@ < 2147483648)]
#[ensures(a << 1u32 >= a)]
pub fn shl_no_overflow(a: u32) {}
