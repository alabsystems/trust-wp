//@ expect: reject
//@ mechanism: closure `_` parameter fallback arg1 duplicated a real closure parameter arg1.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ accept-means: c(5, 9) bound to 9.
//@ teeth: regression guard (g is unknown before and after; exit 2 is a rejection).
//@ also-verified: g::{closure#1}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: the closure returns its first argument, 5.
#[ensures(result == 9u32)]
pub fn g() -> u32 {
    let c = #[ensures(result == arg1)] |arg1: u32, _: u32| arg1;
    c(5, 9)
}
