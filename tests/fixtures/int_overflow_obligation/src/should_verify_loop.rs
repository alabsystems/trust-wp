// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN: a loop counter increment bounded by the loop condition and the
//! invariant never overflows.

use trust_wp::{ensures, invariant, requires};

#[requires(true)]
#[ensures(result@ == n@)]
#[invariant(i@ <= n@)]
pub fn count_to(n: u8) -> u8 {
    let mut i: u8 = 0;
    while i < n {
        i += 1;
    }
    i
}

fn main() {}
