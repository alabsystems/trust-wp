//@ expect: verify
//@ mechanism: control for spec_mach_u8_callee_requires_add_owed_at_call: the call passes 254
//@ WHY THE CONTRACT IS TRUE: at a = 254 the sum 255 is in range and above 254.
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a + 1u8 > a)]
pub fn callee(a: u8) {}

pub fn caller() {
    callee(254);
}
