// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `*x += y` with `y: &u8` calls `<u8 as AddAssign<&u8>>::add_assign`
//! on the `&mut` itself: panics for `*x = 255`.

use trust_wp::{ensures, requires};

#[requires(y@ == 1)]
#[ensures(true)]
pub fn ref_add_assign(x: &mut u8, y: &u8) {
    *x += y;
}

fn main() {}
