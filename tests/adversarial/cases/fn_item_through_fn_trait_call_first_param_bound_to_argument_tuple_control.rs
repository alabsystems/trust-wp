//@ expect: verify
//@ xfail: the fn-item lane binds `g`'s first parameter to the whole argument tuple, so the TRUE
//@ xfail: `result == 2` is refuted against field 1 of `((1, 2), 3)`.
//@ xfail-verdict: failed
//@ mechanism: the TRUE twin of fn_item_through_fn_trait_call_first_param_bound_to_argument_tuple.rs:
//@ mechanism: `Fn::call(&g, ((1, 2), 3))` returns `x.1`, which is 2.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — control. MEASURED at the head D-181 was reviewed at: `caller FAILED (postcondition)` with
//@ teeth: `g verified`, a refutation of a true claim.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(fn_traits, unboxed_closures)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == x.1)]
pub fn g(x: (u32, u32), y: u32) -> u32 {
    let _ = y;
    x.1
}

#[ensures(result == 2u32)]
pub fn caller() -> u32 {
    Fn::call(&g, ((1u32, 2u32), 3u32))
}
