//@ expect: reject
//@ mechanism: a match-arm binding shadowing a parameter reached the permissive Unsupported variant arm
//@ fixed-by: s42 variant-range-facts-v2
//@ accept-means: a recursive call under a parameter-shadowing match binder is accepted again
//@ timeout: 300
//@ verdict: error
//@ refused-with: logic recursion check failed: `creusot_test::f`: self-recursive logic function variant does not strictly decrease: a binder shadows parameter `x` around a recursive call, so the call's arguments cannot be related
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn f(x: Int) -> Int {
    pearlite! { if x > 0 { match Some(x + 1) { Some(x) => f(x - 1) + 1, None => 0 } } else { 0 } }
}

#[ensures(f(1) == 42)]
pub fn g() {}
