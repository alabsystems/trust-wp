//@ expect: verify
//@ mechanism: control: let y = x - 1; f(y) under x > 0 decreases once the let value is substituted
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
pub fn f(x: Int) -> Int {
    pearlite! { if x > 0 { let y = x - 1; f(y) + 1 } else { 0 } }
}

#[ensures(f(2) == 2)]
pub fn g() {}
