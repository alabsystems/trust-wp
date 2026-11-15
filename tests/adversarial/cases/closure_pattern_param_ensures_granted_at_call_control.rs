//@ expect: verify
//@ mechanism: control for closure_pattern_param_ensures_read_as_other_component: bug/594's closure
//@ mechanism: shape, `|_c, (_a, b)| b`, called with (4, (0, 3)). The pattern binding `b` is its
//@ mechanism: parameter's projection (D-177), and that parameter is the second field of the tuple the
//@ mechanism: `Fn*` call passes.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
//@ fixed-by: D-180 — the parameters are bound to the tuple's fields; before, the positional parameter
//@ fixed-by: `b` is projected from was unbound and the call failed closed (`h` unknown).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == 3)]
pub fn h() -> u32 {
    let f = #[ensures(result == b)] |_c: u32, (_a, b): (u32, u32)| b;
    f(4, (0, 3))
}
