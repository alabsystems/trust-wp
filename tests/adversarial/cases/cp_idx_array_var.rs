//@ expect: reject
//@ mechanism: built-in array index bounds check assumed, never proved
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: `a[i]` with no bound on `i` verified; it panics for i >= 3.
//@ teeth: verified on wp-campaign 3eede3c2 (debug driver); rejected on wp-s44.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(true)]
pub fn arr(a: [u8; 3], i: usize) -> u8 {
    a[i]
}
