//@ expect: reject
//@ mechanism: the field-level claim the derive now emits for a payload variant, written by hand over a body that breaks it: `match result { A(x0, x1) => x0 == 0 && x1 == 0, _ => false }` must be checked field by field, not satisfied by the variant alone
//@ accept-means: the payload match in an ensures was read as a variant test and the field claims were dropped
//@ verdict: failed
//@ fn-failed: <E as std::default::Default>::default
//@ teeth: none demonstrated — measured FAILED; it guards the claim the derive now emits for payload variants
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub enum E {
    A(i32, i32),
    B,
}

impl Default for E {
    // WRONG: the second field is 1.
    #[ensures(match result { E::A(x0, x1) => x0 == 0i32 && x1 == 0i32, _ => false })]
    fn default() -> Self {
        E::A(0i32, 1i32)
    }
}
