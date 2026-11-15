//@ expect: verify
//@ mechanism: control for closure_second_param_requires_owed_at_call: the call passes (4, 2), which
//@ mechanism: meets the closure's `requires` over its second parameter.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
//@ fixed-by: D-180 — before, the `requires` over the unbound second parameter was owed as `false`
//@ fixed-by: (`h` unknown).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == 2)]
pub fn h() -> u32 {
    let f = #[requires(b > 0u32)]
    #[ensures(result == b)]
    |_a: u32, b: u32| b;
    f(4, 2)
}
