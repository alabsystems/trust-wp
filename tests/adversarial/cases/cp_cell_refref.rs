//@ expect: reject
//@ mechanism: a `&&Cell` argument is a write capability: reads of the cell before and after `poke(&c)` are not one value
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: `a == b` around `poke(&c)` verified; false because poke increments the cell.
//@ teeth: exit 0 (conflate verified) on HEAD 5780c31e and base 853ad732 (review probe r_cell_refref).
//@ also-verified: poke
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::cell::Cell;

#[ensures(true)]
pub fn poke(c: &&Cell<u8>) { c.set(c.get().wrapping_add(1)) }
#[ensures(result == true)]
pub fn conflate(c: &Cell<u8>) -> bool {
    let a = c.get();
    poke(&c);
    let b = c.get();
    a == b
}
