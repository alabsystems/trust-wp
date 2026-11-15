//@ expect: reject
//@ mechanism: an ensures `(*r)@` over a &mut param was rewritten to the final value `^r`.
//@ fixed-by: wp-s48 (contract_transform: *p in an ensures is the entry value; only ^p is final)
//@ accept-means: `*r` in an ensures is read as the final value again.
//@ WHY THE PROGRAM IS WRONG: result is 5 but the entry *r is arbitrary.
//@ teeth: verified (exit 0) on wp-campaign b98d5d87, measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == (*r)@)]
pub fn mutref_ens_entry_wrong(r: &mut u32) -> u32 {
    *r = 5;
    5
}
