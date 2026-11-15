//@ expect: verify
//@ mechanism: control for spec_mach_u32_add_ge_operand, differing in the `@` views alone: `Int`
//@ mechanism: arithmetic is mathematical (D-135 item 3)
//@ WHY THE CONTRACT IS TRUE: `a@ + b@ >= a@` because `b@ >= 0`.
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(a@ + b@ >= a@)]
pub fn add_ge_operand(a: u32, b: u32) {}
