//@ expect: verify
//@ mechanism: Generic FnMut-bound call — control. With the precondition required, the caller
//@ mechanism: receives `(*f).postcondition_mut((x,), ^f, result)` (std spec FN_MUT_CALL_MUT).
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires((*f).precondition((x,)))]
#[ensures((*f).postcondition_mut((x,), ^f, result))]
pub fn apply_mut_post<F: FnMut(u32) -> u32>(f: &mut F, x: u32) -> u32 {
    f(x)
}
