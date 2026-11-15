//@ expect: reject
//@ mechanism: call-site alias vocabulary (`value`/`rhs`/`argN`) must never override a real parameter name.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ accept-means: `_` fallback arg2 overrode real arg2.
//@ teeth: FAILED on 5f5fa607 (review rev28/c3); regression guard.
//@ also-verified: m
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// `_` at position 2 gets fallback `arg2`; a real parameter at position 0 is named `arg2`.
#[ensures(result == arg2)]
pub fn m(arg2: u32, x: u32, _: u32) -> u32 { arg2 }
// WRONG: m(1, 2, 3) == 1.
#[ensures(result == 3u32)]
pub fn through() -> u32 { m(1, 2, 3) }
