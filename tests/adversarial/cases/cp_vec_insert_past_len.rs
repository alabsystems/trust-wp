//@ expect: reject
//@ mechanism: Vec::insert precondition index <= len not owed
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: `v.insert(len + 1, 0)` verified; it always panics.
//@ teeth: verified on wp-campaign 3eede3c2 (debug driver); rejected on wp-s44.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn vi(mut v: Vec<u8>) {
    let n = v.len();
    v.insert(n + 1, 0);
}
