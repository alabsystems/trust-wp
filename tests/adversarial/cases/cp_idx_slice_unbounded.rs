//@ expect: reject
//@ mechanism: built-in slice index bounds check assumed, never proved
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: `v[10]` on a slice of unknown length verified; it panics for any slice shorter than 11.
//@ teeth: verified on wp-campaign 3eede3c2 (debug driver); rejected on wp-s44.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(true)]
pub fn idx(v: &[u8]) -> u8 {
    v[10]
}
