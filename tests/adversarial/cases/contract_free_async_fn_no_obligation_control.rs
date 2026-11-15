//@ expect: verify
//@ mechanism: over-refusal control for D-117, and the isolating twin of contract_free_async_fn_overflow_never_examined: the same contract-free `async fn f`, whose body is `x` instead of `x + u32::MAX`. It owes nothing, so no pass admits it and the run is clean on `zero`.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — nothing in the crate is false; a refusal here means every `async fn` is refused, obligation or not.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub async fn f(x: u32) -> u32 {
    x
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
