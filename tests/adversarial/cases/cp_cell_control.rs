//@ expect: verify
//@ mechanism: interior-mutable write rule — over-refusal control
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: n/a (control) — claims nothing about the cell contents.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

use std::cell::Cell;

#[ensures(true)]
pub fn cell_ok(c: &Cell<u8>) -> u8 {
    c.set(1);
    c.get()
}
