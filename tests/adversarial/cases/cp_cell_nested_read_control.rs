//@ expect: verify
//@ mechanism: control: two reads of a `&Cell` with no write in between
//@ fixed-by: s44 v2 (wp-s44, contracted panic sites v2)
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::cell::Cell;

#[ensures(true)]
pub fn rd(c: &Cell<u8>) -> u8 {
    let a = c.get();
    let b = c.get();
    a.wrapping_add(b)
}
