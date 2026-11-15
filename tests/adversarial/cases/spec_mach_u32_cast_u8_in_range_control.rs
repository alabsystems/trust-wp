//@ expect: verify
//@ mechanism: control for spec_mach_u32_cast_u8_view: a precondition keeps the value in u8's range
//@ WHY THE CONTRACT IS TRUE: a < 256, so `a as u8` is a.
//@ xfail: ay computes the UNSAT and withholds it (`proof-trusted`): the cast's Euclidean `mod`
//@ xfail: does not certify.
//@ xfail-verdict: unknown
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a@ < 256)]
#[ensures((a as u8)@ == a@)]
pub fn cast_u8_in_range(a: u32) {}
