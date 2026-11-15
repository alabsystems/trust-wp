// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: a loop whose second counter `j` is not bounded by the invariant:
//! `j += 1` can overflow once `j` reaches 255.

use trust_wp::{ensures, invariant, requires};

#[requires(true)]
#[ensures(true)]
#[invariant(i@ <= n@)]
pub fn count(n: u8) {
    let mut i: u8 = 0;
    let mut j: u8 = 0;
    while i < n {
        i += 1;
        j += 1;
    }
    let _ = j;
}

fn main() {}
