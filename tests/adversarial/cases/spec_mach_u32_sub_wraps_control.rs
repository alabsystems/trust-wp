//@ expect: verify
//@ mechanism: control: the oracle's `u32 - u32` wraps
//@ WHY THE CONTRACT IS TRUE: UInt32.sub of 0 and 1 is 2^32 - 1.
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a@ == 0)]
#[ensures((a - 1u32)@ == 4294967295)]
pub fn sub_wraps(a: u32) {}
