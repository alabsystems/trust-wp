//@ expect: reject
//@ mechanism: a tuple holding `&Cell` is a write capability for the cell
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: `a == b` around `poke((c, a + 1))` verified; false because poke stores a + 1.
//@ teeth: exit 0 on HEAD 5780c31e and base 853ad732 (review probe r_cell_tuple).
//@ also-verified: poke
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::cell::Cell;

#[ensures(true)]
pub fn poke(s: (&Cell<u8>, u8)) { s.0.set(s.1) }
#[ensures(result == true)]
pub fn conflate(c: &Cell<u8>) -> bool {
    let a = c.get();
    poke((c, a.wrapping_add(1)));
    let b = c.get();
    a == b
}
