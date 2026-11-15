//@ expect: verify
//@ mechanism: control for v10_callsite_lent_through_projection_slot: a projection naming no
//@ mechanism: region the borrow's region outlives is no slot for it (`<() as Cnt>::N` is `u32`),
//@ mechanism: so `inc_beside_proj`'s `^p` keeps its reading in its lane and at the call.
//@ fixed-by: n/a (over-refusal guard)
//@ teeth: MEASURED (debug driver): verified on f6039647 and on D-108.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Cnt {
    type N;
}

impl Cnt for () {
    type N = u32;
}

#[requires(*p < 100i32)]
#[ensures(^p == *p + 1i32)]
pub fn inc_beside_proj(p: &mut i32, n: &mut <() as Cnt>::N) {
    *p += 1;
}

#[requires(*x < 100i32)]
#[ensures(^x == *x + 1i32)]
pub fn inc_beside_proj_caller(x: &mut i32) {
    let mut n: u32 = 0;
    inc_beside_proj(x, &mut n);
}
