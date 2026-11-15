//@ expect: verify
//@ mechanism: control: `a + b >= a` over `u32` under a precondition that rules out the wrap
//@ WHY THE CONTRACT IS TRUE: `a@ + b@ <= u32::MAX@`, so the oracle's `add` is exact and the sum is
//@ WHY THE CONTRACT IS TRUE: at least a.
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a@ + b@ <= 4294967295)]
#[ensures(a + b >= a)]
pub fn add_no_overflow(a: u32, b: u32) {}
