//@ expect: reject
//@ mechanism: closed-thunk rule substituted a closure body value computed by a non-exact extractor that skips loops (FalseUnwind real_target).
//@ fixed-by: wp-s23 exact-thunk rule + opaque-callable clause drop
//@ accept-means: a thunk whose body loops was replaced by the loop-free path's value; the closure returns 3, not 0
//@ teeth: verified — ACCEPTED (verified ✓) by the pre-fix closed-thunk rule, measured on a review probe of this shape with an integer-returning thunk
//@ also-verified: thunk_loop_map_or_else::{closure#0}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// FALSE: the closure returns 3 (the loop runs three times).
pub fn thunk_loop_map_or_else() {
    let none: Option<i32> = None;
    let r = none.map_or_else(|| { let mut x = 0i32; while x < 3 { x += 1; } x }, |x| x);
    proof_assert!(r == 0i32);
}
