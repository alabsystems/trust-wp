//@ expect: reject
//@ mechanism: mut_borrow/spec_advancement.rs bound a free function`s first declared parameter to the SECOND call argument (receiver skipped unconditionally) and let positional argN overwrite real names.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ accept-means: pick(5, 9) bound to 9.
//@ teeth: no accept measured before the fix (caller unknown); regression guard for the rewritten binding.
//@ also-verified: pick
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == a)]
pub fn pick(a: u32, b: u32) -> u32 { a }
// WRONG: pick(5, 9) returns 5.
#[ensures(result == 9u32)]
pub fn caller(x: &mut u32) -> u32 { *x = 1; pick(5, 9) }
