//@ expect: verify
//@ mechanism: Generic Fn-bound call obligation — over-refusal control. With the precondition
//@ mechanism: stated by the caller contract, the call-site goal `f.precondition((x,))` holds.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(f.precondition((x,)))]
pub fn apply_checked<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}
