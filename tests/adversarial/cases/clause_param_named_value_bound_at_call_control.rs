//@ expect: verify
//@ mechanism: the control of clause_const_named_value_read_as_call_argument: `value` is `f`'s own
//@ mechanism: parameter, the name every call binds it by, so the clause is read and granted alike.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control: D-179 refuses a positional name only where the function has no
//@ teeth: parameter of that name.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == value)]
pub fn f(x: u32, value: u32) -> u32 {
    value
}

#[ensures(result == 9u32)]
pub fn c() -> u32 {
    f(1u32, 9u32)
}
