//@ expect: verify
//@ mechanism: Final-collapse guard — over-refusal control for the Option<&mut T> lane
//@ fixed-by: 932a7de (Fix A), refined by 9f835d7 (guardref)
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
//@
//@ Fix A refuses `^`-collapse on carriers that may embed a `&mut`. This control asserts a
//@ CURRENT-value property of the same Option<&mut T> shape, which needs no prophecy slot at all.
//@ If this stops verifying, the fail-closed guard has grown teeth it should not have and is
//@ refusing pure-value obligations on mut-ref-embedding carriers.
//@ teeth: n/a — over-refusal control; verifies on main.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(match result {
    Some(r) => *r == *x,
    None => false,
})]
pub fn payload_current_value(x: &mut i32) -> Option<&mut i32> {
    Some(x)
}
