//@ expect: verify
//@ mechanism: control for binder_u32_exists_view_negative: a u32 witness the type has.
//@ WHY THE CONTRACT IS TRUE: x = 0 is a u32 whose view is 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(exists<x: u32> x@ == 0)]
pub fn exists_zero_u32() {}
