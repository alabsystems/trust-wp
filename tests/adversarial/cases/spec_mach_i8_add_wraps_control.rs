//@ expect: verify
//@ mechanism: control: the oracle's `i8 + i8` wraps in two's complement
//@ WHY THE CONTRACT IS TRUE: Int8.add of 127 and 1 is -128.
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a@ == 127)]
#[ensures((a + 1i8)@ == -128)]
pub fn add_wraps(a: i8) {}
