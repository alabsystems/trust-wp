//@ expect: verify
//@ mechanism: control for spec_mach_u32_add_logic_body: the body adds the `Int` views
//@ WHY THE CONTRACT IS TRUE: `a@ + b@ >= a@` because `b@ >= 0`.
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
pub fn add(a: u32, b: u32) -> Int {
    pearlite! { a@ + b@ }
}

#[ensures(add(a, b) >= a@)]
pub fn add_logic_body(a: u32, b: u32) {}
