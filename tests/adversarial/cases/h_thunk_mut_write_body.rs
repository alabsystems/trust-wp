//@ expect: reject
//@ mechanism: closed-thunk rule substituted a closure body value computed by an extractor that ignores writes through &mut.
//@ fixed-by: wp-s23 exact-thunk rule + opaque-callable clause drop
//@ accept-means: a write through a mutable borrow inside the thunk was ignored; the closure returns 2, not 1
//@ teeth: ACCEPTED (verified ✓) by the earlier closed-thunk rule, measured on a review probe reducing this case to an integer-returning thunk
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// FALSE: the closure writes 2 through `p` and returns 2.
pub fn thunk_mut_write_map_or_else() {
    let none: Option<i32> = None;
    let r = none.map_or_else(|| { let mut x = 1i32; let p = &mut x; *p = 2; x }, |x| x);
    proof_assert!(r == 1i32);
}
