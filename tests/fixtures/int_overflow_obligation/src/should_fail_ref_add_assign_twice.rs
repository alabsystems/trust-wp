// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: two `+=` calls through the same `&mut`: the second must read the
//! value the first wrote (100 + 100 + 100 overflows), never the entry value.

use trust_wp::{ensures, requires};

#[requires(x@ == 100 && y@ == 100)]
#[ensures(true)]
pub fn ref_add_assign_twice(x: &mut u8, y: &u8) {
    *x += y;
    *x += y;
}

fn main() {}
