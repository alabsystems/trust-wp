// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `const { N + 1 }` in a generic fn overflows for `N = u32::MAX`.
//! Creusot: goal `vc_f.0` "Add overflow" (tests/should_fail/ignore_overflow).

use trust_wp::ensures;

#[ensures(true)]
pub fn succ_const<const N: u32>(x: u32) -> u32 {
    let _ = const { N + 1 };
    x
}

fn main() {}
