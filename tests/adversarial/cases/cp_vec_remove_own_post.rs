//@ expect: reject
//@ mechanism: a callee postcondition was a premise of its own precondition (flat call effects)
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: `v.remove(0)` on a possibly empty Vec verified: `(^v)@.len() == v@.len() - 1` with len >= 0 entailed the owed `0 < v@.len()`.
//@ teeth: verified on wp-campaign 3eede3c2 (debug driver); rejected on wp-s44.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn vr(mut v: Vec<u8>) -> u8 {
    v.remove(0)
}
