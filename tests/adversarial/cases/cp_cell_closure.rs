//@ expect: reject
//@ mechanism: calling a closure whose upvars capture `&Cell` writes through the capture
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: `a == b` around `bump()` verified; false because bump increments the cell.
//@ teeth: exit 0 on HEAD 5780c31e and base 853ad732 (review probe r_cell_closure).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::cell::Cell;

#[ensures(result == true)]
pub fn conflate(c: &Cell<u8>) -> bool {
    let a = c.get();
    let bump = #[ensures(true)] || c.set(c.get().wrapping_add(1));
    bump();
    let b = c.get();
    a == b
}
