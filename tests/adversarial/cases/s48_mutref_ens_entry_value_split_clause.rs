//@ expect: reject
//@ mechanism: a separate `^r` clause did not stop the `*r` clause being rewritten to `^r`.
//@ fixed-by: wp-s48 (contract_transform: *p in an ensures is the entry value; only ^p is final)
//@ accept-means: the per-clause `*p -> ^p` rewrite is back.
//@ WHY THE PROGRAM IS WRONG: result is 5 but the entry *r is arbitrary.
//@ teeth: verified (exit 0) on wp-campaign b98d5d87, measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((^r)@ == 5)]
#[ensures(result@ == (*r)@)]
pub fn f(r: &mut u32) -> u32 { *r = 5; 5 }
