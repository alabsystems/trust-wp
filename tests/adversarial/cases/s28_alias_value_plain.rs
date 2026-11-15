//@ expect: reject
//@ mechanism: call-site alias vocabulary (`value`/`rhs`/`argN`) must never override a real parameter name.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ accept-means: value alias bound m(1,2) to its second argument.
//@ teeth: FAILED on 5f5fa607 (review rev28/c1); regression guard.
//@ also-verified: m
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == value)]
pub fn m(value: u32, y: u32) -> u32 { value }
// WRONG: m(1, 2) == 1.
#[ensures(result == 2u32)]
pub fn through() -> u32 { m(1, 2) }
