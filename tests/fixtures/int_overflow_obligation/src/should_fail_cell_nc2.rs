// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Two `Cell::get` reads around a `Cell::set` are two values: with
//! `c = Cell::new(1)` the subtraction `0 - 1` panics. Contract-free, so the
//! body must be FAILED or capped, never verified.

use std::cell::Cell;

pub fn cell_nc2(c: &Cell<u8>) -> u8 {
    let a = c.get();
    c.set(0);
    let b = c.get();
    b - a
}

fn main() {}
