// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED (entry-value conflation): a parameter mutated inside the loop must not
//! be read at its ENTRY value (constrained by the precondition) in the loop.

use trust_wp::{ensures, invariant, requires};

#[requires(x@ < 10)]
#[ensures(true)]
#[invariant(true)]
pub fn bump(mut x: u8, n: u32) -> u8 {
    let mut i: u32 = 0;
    while i < n {
        x = x + 1;
        i += 1;
    }
    x
}

fn main() {}
