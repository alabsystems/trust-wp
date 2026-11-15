//@ expect: verify
//@ mechanism: Generic Fn-bound call postcondition — control. After `f(x)` the caller may use
//@ mechanism: `f.postcondition((x,), result)` (Creusot `call ensures`), so an ensures that
//@ mechanism: follows from it verifies.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(f.precondition((x,)))]
#[ensures(f.postcondition((x,), result))]
pub fn apply_post<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}
