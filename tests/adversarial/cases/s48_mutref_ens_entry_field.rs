//@ expect: reject
//@ mechanism: an ensures `(*r).a@` projection of a &mut struct param was read at the final value.
//@ fixed-by: wp-s48 (contract_transform: *p in an ensures is the entry value; only ^p is final)
//@ accept-means: projections of `*r` in an ensures bind to the final value again.
//@ WHY THE PROGRAM IS WRONG: result is 5 but the entry field is arbitrary.
//@ teeth: verified (exit 0) on wp-campaign b98d5d87, measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P { pub a: u32, pub b: u32 }
#[ensures(result@ == (*r).a@)]
pub fn f(r: &mut P) -> u32 { r.a = 5; 5 }
