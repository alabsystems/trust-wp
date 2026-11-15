// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN twin of should_fail_cell_nc2: two reads of the cell around a
//! `set`, each bounded by its own path condition, so the addition holds for
//! any values the reads return.

use std::cell::Cell;
use trust_wp::ensures;

#[ensures(true)]
pub fn cell_twin(c: &Cell<u8>) -> u8 {
    let a = c.get();
    c.set(a);
    let b = c.get();
    if a < 100 && b < 100 {
        a + b
    } else {
        0
    }
}

fn main() {}
