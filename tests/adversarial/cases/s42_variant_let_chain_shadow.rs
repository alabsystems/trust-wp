//@ expect: reject
//@ mechanism: chained lets (let y = x + 1; let x = y) shadowing a parameter around a recursive call
//@ fixed-by: s42 variant-range-facts-v2
//@ accept-means: let chains are not substituted into call edges
//@ timeout: 300
//@ verdict: error
//@ refused-with: logic recursion check failed: `creusot_test::f`: self-recursive logic function variant does not strictly decrease: variant `x` does not strictly decrease at self-call creusot_test::f -> creusot_test::f
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn f(x: Int) -> Int {
    pearlite! { if x > 0 { let y = x + 1; let x = y; f(x - 1) + 1 } else { 0 } }
}

#[ensures(f(1) == 42)]
pub fn g() {}
