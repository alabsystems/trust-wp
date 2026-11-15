//@ expect: reject
//@ mechanism: the arithmetic twin of async_fn_body_assertion_never_examined: the `async fn` item's MIR only builds the coroutine, so its VC holds none of the body, and an addition that overflows for every argument was credited as the item's `verified`. Refusing the item, not just its assertions, is what closes this one.
//@ accept-means: an `async fn` whose body panics on every call is credited `verified`.
//@ WHY IT IS FALSE: `x + u32::MAX` overflows for every `x` the precondition admits, and Creusot's program-function precondition for `+` is owed at it.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `f verified ✓`.
//@ fixed-by: D-106 — the contract loop refuses a body `is_coroutine_body` reports
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(0 < x@ && x@ < 100)]
pub async fn f(x: u32) -> u32 {
    x + u32::MAX
}
