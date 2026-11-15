//@ expect: verify
//@ mechanism: control for s28_synth_reborrow_child_param: the write goes through the reborrow of x and the contract names x.
//@ fixed-by: wp-s28 v8
//@ teeth: the reborrow child must still link to its parent after the rename.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^x == 7u32)]
pub fn g(x: &mut u32, x_rb3: &mut u32) { let y = &mut *x; *y = 7u32; }
