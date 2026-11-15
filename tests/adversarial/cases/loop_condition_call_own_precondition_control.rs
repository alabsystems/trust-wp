//@ expect: verify
//@ mechanism: control: the loop condition's call has a precondition the invariant discharges at every
//@ mechanism: pass through the header, the exiting one included (`i <= 10u32`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k <= 10u32)]
#[ensures(result == (k < 10u32))]
pub fn small(k: u32) -> bool { k < 10 }

pub fn go() {
    let mut i = 0u32;
    #[invariant(i <= 10u32)]
    while small(i) { i += 1; }
}
