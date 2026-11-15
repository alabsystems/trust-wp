//@ expect: verify
//@ mechanism: control for program_fn_nested_tuple_pattern_param_captures_caller_name: the caller
//@ mechanism: passes `a` in the slot the callee's pattern binds, `((7, a), 7)`.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == a)]
pub fn g(((_c, a), _d): ((u32, u32), u32)) -> u32 {
    a
}

#[ensures(result == a)]
pub fn h(a: u32) -> u32 {
    g(((7, a), 7))
}
