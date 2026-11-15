//@ expect: verify
//@ mechanism: Generic FnOnce-bound call — control. With the precondition required, the caller
//@ mechanism: receives `f.postcondition_once((x,), result)` (std spec FN_ONCE_CALL_ONCE).
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(f.precondition((x,)))]
#[ensures(f.postcondition_once((x,), result))]
pub fn apply_once_post<F: FnOnce(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}
