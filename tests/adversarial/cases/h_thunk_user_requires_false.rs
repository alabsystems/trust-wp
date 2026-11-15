//@ expect: reject
//@ mechanism: a closure with its own user contract (#[requires(false)]) passed to a std combinator must never be replaced by its body value.
//@ fixed-by: wp-s23 exact-thunk rule (user_specs guard) + opaque-callable clause drop
//@ accept-means: the closure's precondition was bypassed; Creusot requires f.precondition(()) at the call
//@ teeth: defense in depth — not run on the pre-fix driver; the pre-fix closed-thunk rule did not check user_specs
//@ also-verified: requires_false_unwrap_or_else::{closure#1}, requires_false_map_or_else::{closure#2}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// FALSE under Creusot: unwrap_or_else on None calls f, whose precondition is false.
pub fn requires_false_unwrap_or_else() {
    let none: Option<i32> = None;
    let f = #[requires(false)] || 3i32;
    let r = none.unwrap_or_else(f);
    proof_assert!(r == 3i32);
}

/// FALSE: the call r == 3 holds but f's precondition is false.
pub fn requires_false_map_or_else() {
    let none: Option<i32> = None;
    let f = #[requires(false)] || 2i32;
    let r = none.map_or_else(f, |x| x);
    proof_assert!(r == 2i32);
}
