//@ expect: verify
//@ mechanism: control: the entry `*r` is pinned to 5 by requires, so `result@ == (*r)@` is true.
//@ fixed-by: wp-s48 (contract_transform: *p in an ensures is the entry value; only ^p is final)
//@ teeth: control - must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires((*r)@ == 5)]
#[ensures(result@ == (*r)@)]
pub fn f(r: &mut u32) -> u32 { *r = 5; 5 }
