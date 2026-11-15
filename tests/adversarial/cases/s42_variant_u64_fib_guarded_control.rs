//@ expect: verify
//@ mechanism: control: range-guarded u64 fib still unfolds at in-range arguments
//@ fixed-by: s42 variant-range-facts-v2
//@ accept-means: n/a (control)
//@ timeout: 300
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(i)]
pub fn fib(i: u64) -> Int {
    pearlite! { if i == 0u64 { 0 } else if i == 1u64 { 1 } else { fib(i - 1u64) + fib(i - 2u64) } }
}

#[ensures(fib(3u64) == 2)]
pub fn g() {}
