//@ expect: reject
//@ mechanism: closed-thunk rule gave a value to a thunk body that panics on every path.
//@ fixed-by: wp-s23 exact-thunk rule + opaque-callable clause drop
//@ accept-means: a diverging thunk was given the value of its dead tail; the call never returns 1
//@ teeth: verified — ACCEPTED (verified ✓) by the earlier closed-thunk rule, measured on a review probe of the same shape: an integer-returning thunk whose body panics on every path
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// FALSE: calling this function always panics (the closure panics on every
/// path), which Creusot's contract forbids; the closure has no value 1 to
/// substitute into ok_or_else's contract.
pub fn thunk_panic_ok_or_else() {
    let none: Option<i32> = None;
    let r = none.ok_or_else(|| -> i32 { if 1u8 == 1u8 { panic!() } 1i32 });
    match r {
        Err(e) => proof_assert!(e == 1i32),
        Ok(_) => {}
    }
}
