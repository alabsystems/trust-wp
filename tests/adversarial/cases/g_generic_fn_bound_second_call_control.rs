//@ expect: verify
//@ mechanism: Generic Fn-bound double call — control. `Fn::call` takes `&self`, so the closure state
//@ mechanism: is unchanged and `f.precondition((x,))` from the requires covers both call sites.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(f.precondition((x,)))]
pub fn apply_twice<F: Fn(u32) -> u32>(f: &F, x: u32) -> u32 {
    f(x);
    f(x)
}
