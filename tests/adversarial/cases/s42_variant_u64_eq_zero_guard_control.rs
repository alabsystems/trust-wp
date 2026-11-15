//@ expect: verify
//@ mechanism: control: u64 variant decrease needs the u64 range (x != 0 does not imply 0 <= x), supplied by the range requires
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
pub fn f(x: u64) -> Int {
    pearlite! { if x == 0u64 { 0 } else { f(x - 1u64) + 1 } }
}

#[ensures(f(3u64) == 3)]
pub fn g() {}
