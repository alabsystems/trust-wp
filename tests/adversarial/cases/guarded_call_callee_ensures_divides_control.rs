//@ expect: verify
//@ mechanism: control for the assumption-position division rule of D-118: a contract-free body calls
//@ mechanism: `needs_nonzero` under `x != 0`, and the callee's `ensures` divides by `x@`. That
//@ mechanism: postcondition is ASSUMED at the call; its logic division owes nothing, but the encoder
//@ mechanism: collected `x@ != 0` from it with no guard, and the guarded call was refuted.
//@ accept-means: n/a (control) — the call is guarded.
//@ fixed-by: n/a (control)
//@ teeth: control — `hop verified`. Refuted on the binary before D-118 (`(x != 0) ==> (x@ != 0)`
//@ teeth: violated through the ensures' divisor, with a counterexample `x = 0`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ != 0)]
#[ensures(result@ == 10 / x@)]
pub fn needs_nonzero(x: u32) -> u32 {
    10 / x
}

pub fn hop(x: u32) -> u32 {
    if x != 0 { needs_nonzero(x) } else { 0 }
}
