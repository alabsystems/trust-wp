//@ expect: verify
//@ mechanism: the call-result symbol `$call_{N}` must not disturb ordinary parameter names.
//@ fixed-by: wp-s28 (trust_wp_core::formula::synthesized_names)
//@ teeth: control — the same shape with ordinary parameter names verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == v)]
pub fn id(v: u32) -> u32 { v }

#[ensures(result == 7u32)]
pub fn g(c0: u32, c1: u32, c2: u32, c3: u32) -> u32 { id(7) }
