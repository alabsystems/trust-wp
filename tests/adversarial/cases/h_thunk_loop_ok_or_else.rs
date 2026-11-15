//@ expect: reject
//@ mechanism: closed-thunk rule under ok_or_else with a loop body (Int payload asserted via match, not whole-value ==).
//@ fixed-by: wp-s23 exact-thunk rule + opaque-callable clause drop
//@ accept-means: the loop-skipping extractor fed Err(0) into ok_or_else's contract; the payload is 3
//@ teeth: verified — ACCEPTED (verified ✓) by wp-s10's closed-thunk rule (review probe: the same ok_or_else thunk with an Int payload, asserted via match)
//@ also-verified: thunk_loop_ok_or_else::{closure#0}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// FALSE: the Err payload is 3.
pub fn thunk_loop_ok_or_else() {
    let none: Option<i32> = None;
    let r = none.ok_or_else(|| { let mut x = 0i32; while x < 3 { x += 1; } x });
    match r {
        Err(e) => proof_assert!(e == 0i32),
        Ok(_) => {}
    }
}
