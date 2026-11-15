//@ expect: verify
//@ mechanism: control for s16v4_after_inner_*: the inner-loop exit continuation re-binds only what the inner loop may write, so arithmetic on an outer-loop local after the inner loop keeps the outer invariant and condition (i < n <= u32::MAX, so i + 1 cannot overflow).
//@ accept-means: n/a (control; a rejection is an over-refusal of the v4 continuation)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(n: u32) {
    let mut i: u32 = 0;
    #[invariant(i <= n)]
    while i < n {
        let mut j: u8 = 0;
        while j < 255 {
            j += 1;
        }
        let _k = i + 1;
        i += 1;
    }
}
