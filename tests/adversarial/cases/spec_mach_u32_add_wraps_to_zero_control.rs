//@ expect: verify
//@ mechanism: control: the oracle's `u32 + u32` wraps, so `u32::MAX + 1u32 == 0u32` holds in logic
//@ WHY THE CONTRACT IS TRUE: UInt32.add: t'int(add x y) is x + y reduced into [0, 2^32), here 2^32
//@ WHY THE CONTRACT IS TRUE: - 2^32 = 0.
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a@ == 4294967295)]
#[ensures(a + 1u32 == 0u32)]
pub fn add_wraps_to_zero(a: u32) {}
