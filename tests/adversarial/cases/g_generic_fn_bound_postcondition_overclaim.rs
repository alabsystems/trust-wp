//@ expect: reject
//@ mechanism: Generic Fn-bound call postcondition — the call supplies ONLY
//@ mechanism: `f.postcondition((x,), result)`; nothing about the concrete value of result.
//@ fixed-by: n/a (guards against a postcondition fabricated from the call)
//@ accept-means: a generic call's result is being over-constrained.
//@ teeth: `result == x` is false for `|x| x + 1`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(f.precondition((x,)))]
#[ensures(result == x)]
pub fn apply_overclaim<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}
