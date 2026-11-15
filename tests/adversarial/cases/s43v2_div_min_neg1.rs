//@ expect: reject
//@ mechanism: signed MIN / -1 overflow on a primitive integer Div::div call. The std spec required only
//@ mechanism: rhs@ != 0, so a call that always panics (Rust: attempt to divide with overflow) verified.
//@ fixed-by: wp-s43 v2 (creusot-std num.rs spec_div_rem! precondition !(self@ == MIN@ && rhs@ == -1))
//@ accept-means: the Div::div spec no longer carries the signed-overflow precondition.
//@ WHY THE PROGRAM IS WRONG: the call panics for every admitted input.
//@ teeth: pre-existing: verified on wp-s43 c3dfdff8 (review probe e_panic.rs), measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::ops::Div;

#[requires(x@ == -128)]
#[ensures(true)]
pub fn div_min_neg1(x: i8) -> i8 {
    x.div(-1)
}
