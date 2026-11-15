//@ expect: verify
//@ mechanism: control: `(^r)@ == 5` after `*r = 5`.
//@ fixed-by: wp-s48 (contract_transform: *p in an ensures is the entry value; only ^p is final)
//@ teeth: control - must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((^r)@ == 5)]
pub fn mutref_ens_final_true(r: &mut u32) {
    *r = 5;
}
