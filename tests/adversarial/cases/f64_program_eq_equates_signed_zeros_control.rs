//@ expect: verify
//@ mechanism: the isolating twin of f64_assertion_eq_distinguishes_signed_zeros.rs: the same `z == 0.0`
//@ mechanism: over `z = -0.0`, written in the program, is IEEE-754 `==`, which equates the two zeros.
//@ accept-means: n/a (control) — the function returns `true` in every execution.
//@ fixed-by: n/a (control)
//@ teeth: verified before and after D-215.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn program_zeros_equal() -> bool {
    let z = -0.0f64;
    z == 0.0
}
