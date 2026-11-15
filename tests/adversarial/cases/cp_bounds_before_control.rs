//@ expect: verify
//@ mechanism: control: a bounds precondition established before the index (requires) still discharges it
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
#[requires(v@.len() > 0)]
#[ensures(result == v@[0])]
pub fn f(v: &Vec<u8>) -> u8 {
    let x = v[0];
    let _n = v.len();
    x
}
