//@ expect: verify
//@ mechanism: over-refusal control for s61_vacuous_variant_termination_credit — the SAME shape with a SATISFIABLE `#[requires]` and a variant that really does decrease. Withholding credit from a vacuous variant site must not withhold it from a decided one: this crate must still report `verified ✓ (termination)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x >= 0i32)]
#[variant(x)]
pub fn countdown_ok(x: i32) -> i32 {
    if x > 0i32 {
        countdown_ok(x - 1i32)
    } else {
        0i32
    }
}
