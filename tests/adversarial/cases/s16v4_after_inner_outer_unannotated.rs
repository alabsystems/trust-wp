//@ expect: reject
//@ mechanism: code after an INNER loop exit inside an OUTER loop body got no arithmetic obligation: the region walk stopped at the inner condition block (outside the outer exclusive region), the inner region excludes the code, the post-loop lane takes only non-loop blocks, and the primary lane skips cyclic bodies.
//@ accept-means: outer loop unannotated, inner `#[invariant(j <= 255u8)]`: f(1) computes 255u8 + 1 after the inner loop, which panics. FALSE.
//@ fixed-by: wp-s16 overflow-obligations v4 (arithmetic walk continues through inner-loop exits; structural arithmetic-site coverage check)
//@ teeth: a soundness-review probe of this shape — unannotated outer loop, invariant on the inner loop — was ACCEPTED (verified) on d1b9aa55 and on 42007ede; see the v4 commit for the post-fix FAILED run
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(n: u32) {
    let mut i: u32 = 0;
    while i < n {
        let mut j: u8 = 0;
        #[invariant(j <= 255u8)]
        while j < 255 {
            j += 1;
        }
        let _k = j + 1;
        i += 1;
    }
}
