//@ expect: verify
//@ mechanism: control for spec_mach_u32_add_proof_assert, differing in the `@` views alone
//@ WHY THE CONTRACT IS TRUE: `a@ + b@ >= a@` because `b@ >= 0`.
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a@ >= 0 && b@ >= 0)]
pub fn add_proof_assert(a: u32, b: u32) {
    proof_assert!(a@ + b@ >= a@);
}
