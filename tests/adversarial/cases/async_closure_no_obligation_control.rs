//@ expect: verify
//@ mechanism: over-refusal control for D-117, and the isolating twin of async_closure_overflow_never_examined: the same async closure, whose body is `x` instead of `x + u32::MAX`.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — `f`'s contract is true and the closure owes nothing; a refusal here means every async closure is refused, obligation or not.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(0 < x@ && x@ < 100)]
#[ensures(result@ == x@)]
pub fn f(x: u32) -> u32 {
    let _c = async move || x;
    x
}
