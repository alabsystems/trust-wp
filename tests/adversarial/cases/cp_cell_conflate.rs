//@ expect: reject
//@ mechanism: two Cell::get reads around a Cell::set through &Cell were one value
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: `a == b` around `c.set(0)` verified as always true; false for any cell not holding 0.
//@ teeth: verified on wp-campaign 3eede3c2 (debug driver); rejected on wp-s44.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

use std::cell::Cell;

#[ensures(result == true)]
pub fn cell_conflate(c: &Cell<u8>) -> bool {
    let a = c.get();
    c.set(0);
    let b = c.get();
    a == b
}
