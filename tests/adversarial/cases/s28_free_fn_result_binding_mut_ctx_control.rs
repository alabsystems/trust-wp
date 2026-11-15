//@ expect: verify
//@ mechanism: spec_advancement binding
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ teeth: control: verified on c743b394.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == a)]
pub fn pick(a: u32, b: u32) -> u32 { a }
// WRONG: pick(5, 9) returns 5.
#[ensures(result == 5u32)]
pub fn caller(x: &mut u32) -> u32 { *x = 1; pick(5, 9) }
