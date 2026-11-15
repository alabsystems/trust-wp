// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Two contracted functions. With `TRUST_WP_PROBE_PANIC=panic_guard_target`
//! the first one's verification panics, standing in for the ay solver panics
//! the main loop's `catch_unwind` exists to contain; the second must still be
//! verified (the guard continues with the remaining functions).
//!
//! Without the variable both verify and the crate exits 0 — that is the
//! control the panicking run is measured against.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == x)]
pub fn panic_guard_target(x: u32) -> u32 {
    x
}

#[ensures(result == x)]
pub fn panic_guard_bystander(x: u32) -> u32 {
    x
}

fn main() {}
