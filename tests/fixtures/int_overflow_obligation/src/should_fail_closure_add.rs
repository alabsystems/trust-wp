// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: the contract-free closure body `x + 1` owes its own overflow goal
//! (its precondition is `true`); `f(255)` panics.

use trust_wp::{ensures, requires};

#[requires(true)]
#[ensures(true)]
pub fn closure_add() -> u8 {
    let f = |x: u8| x + 1;
    f(255)
}

fn main() {}
