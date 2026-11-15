//@ expect: verify
//@ mechanism: the true twin of param_pattern_projection_read_as_module_const: the body returns `a`.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control. FAILED before D-179 (the projection `(arg0.0)` was read as the
//@ teeth: module const `arg0`, so this TRUE clause was owed as `result == 5`), at the reviewed head
//@ teeth: and at the campaign base alike.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_upper_case_globals)]
pub const arg0: (u32, u32) = (5, 5);

#[ensures(result == a)]
pub fn g((a, _b): (u32, u32)) -> u32 {
    a
}
