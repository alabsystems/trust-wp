//@ expect: reject
//@ mechanism: a struct passed by value holding `&Cell` is a write capability for the cell
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: `a == b` around `poke(S { c })` verified; false because poke increments the cell.
//@ teeth: exit 0 on HEAD 5780c31e and base 853ad732 (review probe r_cell_struct_byval).
//@ also-verified: poke
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::cell::Cell;

pub struct S<'a> { pub c: &'a Cell<u8> }
#[ensures(true)]
pub fn poke(s: S) { s.c.set(s.c.get().wrapping_add(1)) }
#[ensures(result == true)]
pub fn conflate(c: &Cell<u8>) -> bool {
    let a = c.get();
    poke(S { c });
    let b = c.get();
    a == b
}
