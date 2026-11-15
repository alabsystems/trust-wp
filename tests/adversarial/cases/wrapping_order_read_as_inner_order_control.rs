//@ expect: verify
//@ mechanism: the isolating twin of reverse_order_read_as_inner_order.rs: the same four functions and
//@ mechanism: contracts over `std::num::Wrapping`, whose comparisons order as the inner values do, so every
//@ mechanism: contract holds and the builtin `PartialOrd` contracts read them correctly. Only the newtype differs.
//@ accept-means: n/a (control) — `Wrapping(x) < Wrapping(y)` exactly when `x < y`.
//@ fixed-by: n/a (control)
//@ teeth: verified when committed and on the campaign tip (each function verified).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::num::Wrapping;

#[requires(x@ < y@)]
#[ensures(result)]
pub fn wrap_lt(x: i32, y: i32) -> bool {
    Wrapping(x) < Wrapping(y)
}

#[requires(x@ < y@)]
#[ensures(!result)]
pub fn wrap_ge(x: i32, y: i32) -> bool {
    Wrapping(x) >= Wrapping(y)
}

#[requires(a.0@ < b.0@)]
#[ensures(result)]
pub fn wrap_param_le(a: Wrapping<u8>, b: Wrapping<u8>) -> bool {
    a <= b
}

#[requires(x@ < y@)]
pub fn wrap_gt_guards_panic(x: i64, y: i64) {
    if Wrapping(x) > Wrapping(y) {
        panic!();
    }
}
