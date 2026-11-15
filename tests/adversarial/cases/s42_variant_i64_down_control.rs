//@ expect: verify
//@ mechanism: control: i64 down(x - 1) under x > 0 decreases with the i64 range requires
//@ fixed-by: s42 variant-range-facts-v2
//@ accept-means: n/a (control)
//@ timeout: 300
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn down(x: i64) -> Int {
    pearlite! { if x > 0i64 { down(x - 1i64) + 1 } else { 0 } }
}

#[ensures(down(2i64) == 2)]
pub fn g() {}
