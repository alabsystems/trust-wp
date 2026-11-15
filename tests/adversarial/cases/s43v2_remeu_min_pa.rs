//@ expect: reject
//@ mechanism: signed MIN / -1 overflow on a primitive integer rem_euclid call. The std spec required only
//@ mechanism: rhs@ != 0, so a call that always panics (Rust: attempt to calculate the remainder with overflow) verified.
//@ fixed-by: wp-s43 v2 (creusot-std num.rs spec_div_rem! precondition !(self@ == MIN@ && rhs@ == -1))
//@ accept-means: the rem_euclid spec no longer carries the signed-overflow precondition.
//@ WHY THE PROGRAM IS WRONG: the call panics for every admitted input.
//@ teeth: verified on wp-s43 c3dfdff8 (review probe e_panic.rs), measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn remeu_min_pa() {
    let x = i64::MIN;
    let m = -1i64;
    let r = x.rem_euclid(m);
    proof_assert!(r@ == 0);
}
