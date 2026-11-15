// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `&u8 + u8` calls `<&u8 as Add<u8>>::add` (no caller MIR Assert),
//! which forwards to the overflow-checked `u8 + u8`: panics for `*x = 255`.

use trust_wp::{ensures, requires};

#[requires(true)]
#[ensures(true)]
pub fn ref_add(x: &u8) -> u8 {
    x + 1
}

fn main() {}
