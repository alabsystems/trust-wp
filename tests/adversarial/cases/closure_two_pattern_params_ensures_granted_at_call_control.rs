//@ expect: verify
//@ mechanism: control for closure_pattern_param_ensures_read_as_other_component: the same closure and
//@ mechanism: call, with the value the call returns.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
//@ fixed-by: D-180 — before, the second parameter was unbound and the call failed closed (`h` unknown).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == 3)]
pub fn h() -> u32 {
    let f = #[ensures(result == b)] |(_c, _d): (u32, u32), (_a, b): (u32, u32)| b;
    f((0, 0), (0, 3))
}
