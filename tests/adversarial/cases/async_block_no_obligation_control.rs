//@ expect: verify
//@ mechanism: over-refusal control for D-117, and the isolating twin of async_block_overflow_never_examined: the same `f` and the same `async move` block, whose body is `x` instead of `x + u32::MAX`. The block owes nothing, so no pass admits it and `f` verifies; the refusal is keyed on the obligation, not on the coroutine.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — `f`'s contract is true and the block owes nothing; a refusal here means every coroutine is refused, obligation or not.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(0 < x@ && x@ < 100)]
#[ensures(result@ == x@)]
pub fn f(x: u32) -> u32 {
    let _fut = async move { x };
    x
}
