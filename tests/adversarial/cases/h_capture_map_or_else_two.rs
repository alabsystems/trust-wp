//@ expect: reject
//@ mechanism: capturing closure translated to its environment tuple and substituted for default() in map_or_else's contract.
//@ fixed-by: wp-s23 exact-thunk rule + opaque-callable clause drop
//@ accept-means: two different capturing closures were identified by their equal environments (b); the results are b+1 and b+2
//@ teeth: verified — ACCEPTED (EXIT=0) before the fix, on an audit probe of this same two-capturing-closure shape
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// FALSE: r1 = b + 1, r2 = b + 2.
pub fn capture_map_or_else_two(b: i32) {
    if b < 100 {
        let n: Option<i32> = None;
        let r1 = n.map_or_else(move || b + 1, |x| x);
        let r2 = n.map_or_else(move || b + 2, |x| x);
        proof_assert!(r1 == r2);
    }
}
