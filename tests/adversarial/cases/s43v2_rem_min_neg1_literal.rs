//@ expect: reject
//@ mechanism: signed MIN / -1 overflow on a primitive integer Rem::rem (literal divisor) call. The std spec required only
//@ mechanism: rhs@ != 0, so a call that always panics (Rust: attempt to calculate the remainder with overflow) verified.
//@ fixed-by: wp-s43 v2 (creusot-std num.rs spec_div_rem! precondition !(self@ == MIN@ && rhs@ == -1))
//@ accept-means: the Rem::rem (literal divisor) spec no longer carries the signed-overflow precondition.
//@ WHY THE PROGRAM IS WRONG: the call panics for every admitted input.
//@ teeth: verified on wp-s43 c3dfdff8 AND with a429a8b8 reverted (generic T::rem.postcondition fallback), review probe e_panic.rs, 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::ops::Rem;

#[requires(x@ == -2147483648)]
#[ensures(true)]
pub fn rem_min_neg1(x: i32) -> i32 {
    x.rem(-1)
}
