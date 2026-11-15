//@ expect: reject
//@ mechanism: code after an INNER loop exit inside an OUTER loop body got no arithmetic obligation: the region walk stopped at the inner condition block (outside the outer exclusive region), the inner region excludes the code, the post-loop lane takes only non-loop blocks, and the primary lane skips cyclic bodies.
//@ accept-means: f(1, x) computes 255u8 + 1 after the inner loop for every x, which panics. FALSE.
//@ fixed-by: wp-s16 overflow-obligations v4 (arithmetic walk continues through inner-loop exits; structural arithmetic-site coverage check)
//@ teeth: the soundness-review probe of this shape, whose inner u8 counter starts from a parameter and carries no invariant, was ACCEPTED (verified) on d1b9aa55 and on 42007ede; see the v4 commit for the post-fix FAILED run
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(n: u32, x: u8) {
    let mut i: u32 = 0;
    #[invariant(i <= n)]
    while i < n {
        let mut j: u8 = x;
        while j < 255 {
            j += 1;
        }
        let _k = j + 1;
        i += 1;
    }
}
