// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: the contract-free closure body `x + 1` owes its OWN overflow goal
//! (its precondition is `true`), even though this call site passes 1.

use trust_wp::{ensures, requires};

#[requires(true)]
#[ensures(true)]
pub fn closure_body_only() -> u8 {
    let f = |x: u8| x + 1;
    f(1)
}

fn main() {}
